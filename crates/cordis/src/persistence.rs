//! Explicit JSON persistence with three-way merges and per-file atomic replacement.
//!
//! A plan reads every source before writing any source. Commit checks each file
//! again, then replaces it through a synced sibling temporary file. This is not a
//! cross-file transaction or a filesystem compare-and-swap against other editors.

use crate::loader::{ConfigTree, Entry};
use serde_json::{Map, Value};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::fs::{self, File, OpenOptions, Permissions};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

/// Progress remains available on failure; `written` includes a replacement whose
/// directory sync failed. No successful replacement is silently rolled back.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SaveReport {
    pub written: Vec<PathBuf>,
    pub unchanged: Vec<PathBuf>,
    /// Files not yet processed during commit; planning failures do not list a plan.
    pub remaining: Vec<PathBuf>,
    /// These files retain external edits absent from the running configuration.
    pub merged_external: Vec<PathBuf>,
    /// Replacement succeeded, but crash durability could not be confirmed.
    pub durability_uncertain: Vec<PathBuf>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SaveErrorKind {
    NoFileSource,
    RecoveryPending,
    StalePlan,
    /// Paths name JSON fields, not their potentially sensitive values.
    Conflict(Vec<String>),
    Topology(String),
    SourceChanged,
    InvalidMergedConfiguration(String),
    Io(String),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SaveError {
    pub path: Option<PathBuf>,
    pub kind: SaveErrorKind,
    pub report: Box<SaveReport>,
}
impl SaveError {
    pub(crate) fn new(path: Option<&Path>, kind: SaveErrorKind) -> Self {
        Self {
            path: path.map(Path::to_owned),
            kind,
            report: Box::default(),
        }
    }
    fn io(path: &Path, error: impl fmt::Display) -> Self {
        Self::new(Some(path), SaveErrorKind::Io(error.to_string()))
    }
}
impl fmt::Display for SaveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(path) = &self.path {
            write!(f, "{}: ", path.display())?;
        }
        match &self.kind {
            SaveErrorKind::NoFileSource => write!(f, "load_file is required before saving"),
            SaveErrorKind::RecoveryPending => {
                write!(f, "recover the pending runtime revision before saving")
            }
            SaveErrorKind::StalePlan => {
                write!(f, "loader changed after save planning; prepare a new plan")
            }
            SaveErrorKind::Conflict(paths) => {
                write!(f, "conflicting edits at {}", paths.join(", "))
            }
            SaveErrorKind::Topology(message) => write!(f, "include topology: {message}"),
            SaveErrorKind::SourceChanged => {
                write!(f, "source changed after save planning; prepare a new plan")
            }
            SaveErrorKind::InvalidMergedConfiguration(message) => {
                write!(f, "merged configuration is invalid: {message}")
            }
            SaveErrorKind::Io(message) => write!(f, "{message}"),
        }
    }
}
impl std::error::Error for SaveError {}

/// Inspect `json()` before handing the plan back to `Loader::commit_save`.
#[derive(Debug)]
pub struct PlannedFile {
    path: PathBuf,
    observed: String,
    output: String,
    pub(crate) ours: ConfigTree,
    permissions: Permissions,
    merged_external: bool,
    retry_directory_sync: bool,
}
impl PlannedFile {
    pub fn path(&self) -> &Path {
        &self.path
    }
    pub fn json(&self) -> &str {
        &self.output
    }
    pub fn will_write(&self) -> bool {
        self.output != self.observed
    }
    /// True for a replacement or a retry after an earlier directory sync failure.
    pub fn requires_directory_sync(&self) -> bool {
        self.will_write() || self.retry_directory_sync
    }
    pub fn includes_external_edits(&self) -> bool {
        self.merged_external
    }
}

/// A reviewable snapshot, invalidated by a loader mutation or a disk edit.
#[derive(Debug)]
pub struct SavePlan {
    files: Vec<PlannedFile>,
    pub(crate) tree: ConfigTree,
    pub(crate) sources: BTreeMap<PathBuf, String>,
    pub(crate) checkpoints: BTreeMap<PathBuf, ConfigTree>,
    pub(crate) registry_revision: u64,
    pub(crate) pending_sync: BTreeSet<PathBuf>,
    include_targets: BTreeMap<PathBuf, PathBuf>,
}
impl SavePlan {
    pub fn files(&self) -> &[PlannedFile] {
        &self.files
    }
    pub(crate) fn merged_sources(&self) -> BTreeMap<PathBuf, String> {
        self.files
            .iter()
            .map(|file| (file.path.clone(), file.output.clone()))
            .collect()
    }
    pub(crate) fn desired(&self) -> BTreeMap<PathBuf, ConfigTree> {
        self.files
            .iter()
            .map(|file| (file.path.clone(), file.ours.clone()))
            .collect()
    }
    pub(crate) fn prepare(
        tree: ConfigTree,
        sources: BTreeMap<PathBuf, String>,
        checkpoints: BTreeMap<PathBuf, ConfigTree>,
        desired: BTreeMap<PathBuf, ConfigTree>,
        registry_revision: u64,
        pending_sync: BTreeSet<PathBuf>,
        include_targets: BTreeMap<PathBuf, PathBuf>,
    ) -> Result<Self, SaveError> {
        let mut files = Vec::new();
        for (path, ours) in desired {
            let base = &checkpoints[&path];
            let (observed, permissions) = read_regular(&path)?;
            let theirs =
                ConfigTree::from_json(&observed).map_err(|error| SaveError::io(&path, error))?;
            if include_signature(&base.entries) != include_signature(&theirs.entries) {
                return Err(SaveError::new(
                    Some(&path),
                    SaveErrorKind::Topology(
                        "disk include anchors changed; reload before saving".into(),
                    ),
                ));
            }
            let mut conflicts = Vec::new();
            let entries = merge_entries(
                &base.entries,
                &ours.entries,
                &theirs.entries,
                "$",
                &mut conflicts,
            );
            if !conflicts.is_empty() {
                return Err(SaveError::new(
                    Some(&path),
                    SaveErrorKind::Conflict(conflicts),
                ));
            }
            let merged = ConfigTree { entries };
            let output = if merged == theirs {
                observed.clone()
            } else {
                let value = if serde_json::from_str::<Value>(&observed)
                    .map_err(|error| SaveError::io(&path, error))?
                    .is_array()
                {
                    serde_json::to_value(&merged.entries)
                } else {
                    serde_json::to_value(&merged)
                }
                .map_err(|error| SaveError::io(&path, error))?;
                format!(
                    "{}\n",
                    serde_json::to_string_pretty(&value)
                        .map_err(|error| SaveError::io(&path, error))?
                )
            };
            let retry_directory_sync = pending_sync.contains(&path);
            files.push(PlannedFile {
                path,
                observed,
                output,
                merged_external: merged != ours,
                retry_directory_sync,
                ours,
                permissions,
            });
        }
        Ok(Self {
            files,
            tree,
            sources,
            checkpoints,
            registry_revision,
            pending_sync,
            include_targets,
        })
    }
    pub(crate) fn commit(self) -> Result<SaveReport, SaveError> {
        self.commit_with(sync_parent)
    }
    fn commit_with(
        self,
        synchronize_parent: impl Fn(&Path) -> std::io::Result<()>,
    ) -> Result<SaveReport, SaveError> {
        let mut report = SaveReport {
            remaining: self.files.iter().map(|file| file.path.clone()).collect(),
            ..SaveReport::default()
        };
        for file in self.files {
            let result = (|| {
                for (lexical, target) in &self.include_targets {
                    let current_target =
                        fs::canonicalize(lexical).map_err(|error| SaveError::io(lexical, error))?;
                    if &current_target != target {
                        return Err(SaveError::new(
                            Some(lexical),
                            SaveErrorKind::Topology(
                                "include target changed after planning; reload before saving"
                                    .into(),
                            ),
                        ));
                    }
                }
                let (current, permissions) = read_regular(&file.path)?;
                if current != file.observed || permissions != file.permissions {
                    return Err(SaveError::new(
                        Some(&file.path),
                        SaveErrorKind::SourceChanged,
                    ));
                }
                if file.merged_external {
                    report.merged_external.push(file.path.clone());
                }
                if !file.will_write() {
                    report.unchanged.push(file.path.clone());
                    report.remaining.remove(0);
                    if file.retry_directory_sync {
                        if let Err(error) = synchronize_parent(&file.path) {
                            report.durability_uncertain.push(file.path.clone());
                            return Err(SaveError::io(&file.path, error));
                        }
                    }
                    return Ok(());
                }
                let mut temporary = Temporary::new(&file.path)?;
                temporary
                    .file
                    .write_all(file.output.as_bytes())
                    .map_err(|error| SaveError::io(&file.path, error))?;
                temporary
                    .file
                    .set_permissions(file.permissions.clone())
                    .map_err(|error| SaveError::io(&file.path, error))?;
                temporary
                    .file
                    .sync_all()
                    .map_err(|error| SaveError::io(&file.path, error))?;
                // Recheck after preparing the temporary file, as well as before it.
                let (current, permissions) = read_regular(&file.path)?;
                if current != file.observed || permissions != file.permissions {
                    return Err(SaveError::new(
                        Some(&file.path),
                        SaveErrorKind::SourceChanged,
                    ));
                }
                fs::rename(&temporary.path, &file.path)
                    .map_err(|error| SaveError::io(&file.path, error))?;
                temporary.renamed = true;
                report.written.push(file.path.clone());
                report.remaining.remove(0);
                if let Err(error) = synchronize_parent(&file.path) {
                    report.durability_uncertain.push(file.path.clone());
                    return Err(SaveError::io(&file.path, error));
                }
                Ok(())
            })();
            if let Err(mut error) = result {
                error.report = Box::new(report);
                return Err(error);
            }
        }
        Ok(report)
    }
}

fn read_regular(path: &Path) -> Result<(String, Permissions), SaveError> {
    let metadata = fs::symlink_metadata(path).map_err(|error| SaveError::io(path, error))?;
    if !metadata.file_type().is_file() {
        return Err(SaveError::io(
            path,
            "source must remain a regular file, not a symlink or directory",
        ));
    }
    if fs::canonicalize(path).map_err(|error| SaveError::io(path, error))? != path {
        return Err(SaveError::new(Some(path), SaveErrorKind::SourceChanged));
    }
    let mut file = File::open(path).map_err(|error| SaveError::io(path, error))?;
    let mut text = String::new();
    file.read_to_string(&mut text)
        .map_err(|error| SaveError::io(path, error))?;
    Ok((
        text,
        file.metadata()
            .map_err(|error| SaveError::io(path, error))?
            .permissions(),
    ))
}
#[cfg(unix)]
fn sync_parent(path: &Path) -> std::io::Result<()> {
    File::open(path.parent().unwrap_or(Path::new(".")))?.sync_all()
}
#[cfg(not(unix))]
fn sync_parent(_: &Path) -> std::io::Result<()> {
    Err(std::io::Error::new(
        std::io::ErrorKind::Unsupported,
        "replacement completed; directory durability is not supported on this platform",
    ))
}
static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);
struct Temporary {
    path: PathBuf,
    file: File,
    renamed: bool,
}
impl Temporary {
    fn new(destination: &Path) -> Result<Self, SaveError> {
        for _ in 0..128 {
            let path = destination.with_file_name(format!(
                ".cordis-save-{}-{}.tmp",
                std::process::id(),
                NEXT_TEMP.fetch_add(1, Ordering::Relaxed)
            ));
            let mut options = OpenOptions::new();
            options.write(true).create_new(true);
            #[cfg(unix)]
            {
                use std::os::unix::fs::OpenOptionsExt;
                options.mode(0o600);
            }
            match options.open(&path) {
                Ok(file) => {
                    return Ok(Self {
                        path,
                        file,
                        renamed: false,
                    })
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => return Err(SaveError::io(destination, error)),
            }
        }
        Err(SaveError::io(
            destination,
            "could not allocate a unique temporary file",
        ))
    }
}
impl Drop for Temporary {
    fn drop(&mut self) {
        if !self.renamed {
            let _ = fs::remove_file(&self.path);
        }
    }
}

pub(crate) fn include_signature(entries: &[Entry]) -> BTreeMap<String, PathBuf> {
    fn walk(entries: &[Entry], parent: &str, result: &mut BTreeMap<String, PathBuf>) {
        for entry in entries {
            let path = format!("{parent}/{}", entry.id);
            if let Some(include) = &entry.include {
                result.insert(path.clone(), include.clone());
            }
            walk(&entry.children, &path, result);
        }
    }
    let mut result = BTreeMap::new();
    walk(entries, "", &mut result);
    result
}
fn merge_json(
    base: Option<&Value>,
    ours: Option<&Value>,
    theirs: Option<&Value>,
    path: &str,
    conflicts: &mut Vec<String>,
) -> Option<Value> {
    if ours == base {
        return theirs.cloned();
    }
    if theirs == base || ours == theirs {
        return ours.cloned();
    }
    if let (Some(Value::Object(base)), Some(Value::Object(ours)), Some(Value::Object(theirs))) =
        (base, ours, theirs)
    {
        let mut result = Map::new();
        let keys: BTreeSet<_> = base
            .keys()
            .chain(ours.keys())
            .chain(theirs.keys())
            .collect();
        for key in keys {
            if let Some(value) = merge_json(
                base.get(key),
                ours.get(key),
                theirs.get(key),
                &format!("{path}/{key}"),
                conflicts,
            ) {
                result.insert(key.clone(), value);
            }
        }
        return Some(Value::Object(result));
    }
    conflicts.push(path.to_owned());
    ours.cloned()
}
fn merge_entries(
    base: &[Entry],
    ours: &[Entry],
    theirs: &[Entry],
    path: &str,
    conflicts: &mut Vec<String>,
) -> Vec<Entry> {
    fn index<'a>(
        entries: &'a [Entry],
        path: &str,
        conflicts: &mut Vec<String>,
    ) -> BTreeMap<&'a str, &'a Entry> {
        let mut result = BTreeMap::new();
        for entry in entries {
            if result.insert(entry.id.as_str(), entry).is_some() {
                conflicts.push(format!("{path}/{} (duplicate id)", entry.id));
            }
        }
        result
    }
    let (b, o, t) = (
        index(base, path, conflicts),
        index(ours, path, conflicts),
        index(theirs, path, conflicts),
    );
    let ids: BTreeSet<_> = b.keys().chain(o.keys()).chain(t.keys()).copied().collect();
    let mut merged = BTreeMap::new();
    for id in ids {
        let (base, ours, theirs) = (b.get(id).copied(), o.get(id).copied(), t.get(id).copied());
        let child_path = format!("{path}/{id}");
        let value = if ours == base {
            theirs.cloned()
        } else if theirs == base || ours == theirs {
            ours.cloned()
        } else if let (Some(base), Some(ours), Some(theirs)) = (base, ours, theirs) {
            let mut bv = serde_json::to_value(base).expect("Entry serialization is infallible");
            let mut ov = serde_json::to_value(ours).expect("Entry serialization is infallible");
            let mut tv = serde_json::to_value(theirs).expect("Entry serialization is infallible");
            for value in [&mut bv, &mut ov, &mut tv] {
                value.as_object_mut().unwrap().remove("children");
            }
            let fields =
                merge_json(Some(&bv), Some(&ov), Some(&tv), &child_path, conflicts).unwrap();
            let mut entry: Entry =
                serde_json::from_value(fields).expect("merged entry fields retain their type");
            entry.children = merge_entries(
                &base.children,
                &ours.children,
                &theirs.children,
                &child_path,
                conflicts,
            );
            Some(entry)
        } else {
            conflicts.push(child_path);
            ours.cloned()
        };
        if let Some(value) = value {
            merged.insert(id, value);
        }
    }
    let ids = |entries: &[Entry]| {
        entries
            .iter()
            .map(|entry| entry.id.clone())
            .collect::<Vec<_>>()
    };
    let (bi, oi, ti) = (ids(base), ids(ours), ids(theirs));
    let order = if oi == bi {
        ti
    } else if ti == bi || oi == ti {
        oi
    } else {
        conflicts.push(format!("{path}/<order>"));
        oi
    };
    order
        .iter()
        .filter_map(|id| merged.remove(id.as_str()))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;

    #[test]
    fn failed_directory_sync_reports_replacement_and_noop_retry_retries_sync() {
        let directory = std::env::temp_dir().join(format!(
            "cordis-sync-fault-{}-{}",
            std::process::id(),
            NEXT_TEMP.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&directory).unwrap();
        let path = directory.join("config.json");
        let base_text = r#"[{"id":"a","config":{"n":1}}]"#.to_owned();
        fs::write(&path, &base_text).unwrap();
        let path = fs::canonicalize(path).unwrap();
        let base = ConfigTree::from_json(&base_text).unwrap();
        let mut ours = base.clone();
        ours.entries[0].config["n"] = Value::from(2);
        let sources = BTreeMap::from([(path.clone(), base_text)]);
        let desired = BTreeMap::from([(path.clone(), ours.clone())]);
        let plan = SavePlan::prepare(
            ours.clone(),
            sources.clone(),
            BTreeMap::from([(path.clone(), base)]),
            desired.clone(),
            0,
            BTreeSet::new(),
            BTreeMap::new(),
        )
        .unwrap();
        let error = plan
            .commit_with(|_| Err(std::io::Error::other("injected directory fsync failure")))
            .unwrap_err();
        assert_eq!(error.report.written, vec![path.clone()]);
        assert_eq!(error.report.durability_uncertain, vec![path.clone()]);
        assert!(error.report.remaining.is_empty());
        assert_eq!(
            ConfigTree::from_json(&fs::read_to_string(&path).unwrap()).unwrap(),
            ours
        );
        let pending_sync = BTreeSet::from([path.clone()]);
        let retry = SavePlan::prepare(
            ours.clone(),
            sources,
            desired.clone(),
            desired,
            0,
            pending_sync,
            BTreeMap::new(),
        )
        .unwrap();
        assert!(!retry.files()[0].will_write());
        let calls = Cell::new(0);
        let result = retry
            .commit_with(|_| {
                calls.set(calls.get() + 1);
                Ok(())
            })
            .unwrap();
        assert_eq!(calls.get(), 1);
        assert_eq!(result.unchanged, vec![path]);
        assert!(result.written.is_empty());
        assert!(result.durability_uncertain.is_empty());
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn abandoned_temporary_file_is_removed() {
        let directory = std::env::temp_dir().join(format!(
            "cordis-temp-fault-{}-{}",
            std::process::id(),
            NEXT_TEMP.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&directory).unwrap();
        let destination = directory.join("config.json");
        fs::write(&destination, "original").unwrap();
        let temporary_path;
        {
            let mut temporary = Temporary::new(&destination).unwrap();
            temporary_path = temporary.path.clone();
            temporary.file.write_all(b"partial replacement").unwrap();
            assert!(temporary_path.exists());
            // Simulate aborting before rename, including write/sync validation failures.
        }
        assert!(!temporary_path.exists());
        assert_eq!(fs::read_to_string(destination).unwrap(), "original");
        fs::remove_dir_all(directory).unwrap();
    }
}
