//! Explicit JSON persistence with three-way merges and per-file atomic replacement.
//!
//! A plan reads every source before writing any source. Commit checks each file
//! again, then replaces it through a synced sibling temporary file. This is not a
//! cross-file transaction or a filesystem compare-and-swap against other editors.

use crate::loader::{ConfigTree, Entry};
use cordis_kernel::configuration_save::{Document, Stage, StepError};
use serde_json::{Map, Value};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::fs::{self, File, OpenOptions, Permissions};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

/// Progress remains available on failure; `written` includes a replacement whose
/// durability barrier failed. No successful replacement is silently rolled back.
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
type FileData =
    cordis_kernel::configuration_save::sources::Target<PathBuf, ConfigTree, Permissions>;
#[derive(Debug)]
pub struct PlannedFile {
    document: Document<FileData>,
}
impl PlannedFile {
    pub fn path(&self) -> &Path {
        &self.document.data().key
    }
    pub fn json(&self) -> &str {
        self.document.output()
    }
    pub fn will_write(&self) -> bool {
        self.document.will_write()
    }
    /// True for a replacement or a retry after an earlier durability barrier failure.
    /// Windows uses a write-through replacement and file flush, rather than directory fsync.
    pub fn requires_directory_sync(&self) -> bool {
        self.document.requires_sync()
    }
    pub fn includes_external_edits(&self) -> bool {
        self.document.merged_external()
    }
}

#[derive(Debug)]
pub(crate) struct SaveOrigin {
    pub(crate) registry_revision: u64,
    pub(crate) configuration: cordis_kernel::configuration_transaction::SaveStamp,
}

/// A reviewable snapshot, invalidated by a loader mutation or a disk edit.
#[derive(Debug)]
pub struct SavePlan {
    files: Vec<PlannedFile>,
    pub(crate) tree: ConfigTree,
    pub(crate) sources: BTreeMap<PathBuf, String>,
    pub(crate) checkpoints: BTreeMap<PathBuf, ConfigTree>,
    pub(crate) origin: SaveOrigin,
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
            .map(|file| (file.path().to_owned(), file.json().to_owned()))
            .collect()
    }
    pub(crate) fn prepare(
        tree: ConfigTree,
        sources: BTreeMap<PathBuf, String>,
        checkpoints: BTreeMap<PathBuf, ConfigTree>,
        desired: BTreeMap<PathBuf, ConfigTree>,
        origin: SaveOrigin,
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
            let merged_external = merged != ours;
            files.push(PlannedFile {
                document: Document::new(
                    FileData::new(path, ours, permissions),
                    observed,
                    output,
                    retry_directory_sync,
                    merged_external,
                ),
            });
        }
        Ok(Self {
            files,
            tree,
            sources,
            checkpoints,
            origin,
            pending_sync,
            include_targets,
        })
    }
    pub(crate) fn commit<S, R, K, U>(
        self,
        configuration: &mut cordis_kernel::configuration_recorded::Recorded<
            S,
            R,
            K,
            U,
            PathBuf,
            ConfigTree,
        >,
        domain: u64,
    ) -> Result<SaveReport, SaveError> {
        self.commit_with(configuration, domain, sync_parent)
    }
    fn commit_with<S, R, K, U>(
        self,
        configuration: &mut cordis_kernel::configuration_recorded::Recorded<
            S,
            R,
            K,
            U,
            PathBuf,
            ConfigTree,
        >,
        domain: u64,
        synchronize_parent: impl Fn(&Path) -> std::io::Result<()>,
    ) -> Result<SaveReport, SaveError> {
        if !configuration.accepts_save(domain, &self.origin.configuration) {
            return Err(SaveError::new(None, SaveErrorKind::StalePlan));
        }
        let mut save = self
            .origin
            .configuration
            .start(self.files.into_iter().map(|file| file.document).collect());
        let mut temporary: Option<Temporary> = None;
        let result = loop {
            // The checked owner supplies the actual stored document and phase.
            // The adapter executes I/O; it cannot acknowledge a replacement or
            // advance to the next file by constructing a progress report.
            let next = save.step(|stage, document| {
                let file = document.data();
                match stage {
                    Stage::Check | Stage::Recheck => {
                        if stage == Stage::Check {
                            for (lexical, target) in &self.include_targets {
                                let current = fs::canonicalize(lexical)
                                    .map_err(|error| SaveError::io(lexical, error))?;
                                if &current != target {
                                    return Err(SaveError::new(
                                        Some(lexical),
                                        SaveErrorKind::Topology(
                                            "include target changed after planning; reload before saving".into(),
                                        ),
                                    ));
                                }
                            }
                        }
                        let (current, permissions) = read_regular(&file.key)?;
                        if current != document.observed() || permissions != file.metadata {
                            return Err(SaveError::new(Some(&file.key), SaveErrorKind::SourceChanged));
                        }
                        Ok(())
                    }
                    Stage::Prepare => {
                        let mut prepared = Temporary::new(&file.key)?;
                        prepared.file.write_all(document.output().as_bytes())
                            .map_err(|error| SaveError::io(&file.key, error))?;
                        prepared.file.set_permissions(file.metadata.clone())
                            .map_err(|error| SaveError::io(&file.key, error))?;
                        prepared.file.sync_all()
                            .map_err(|error| SaveError::io(&file.key, error))?;
                        temporary = Some(prepared);
                        Ok(())
                    }
                    Stage::Replace => {
                        let prepared = temporary.as_mut().ok_or_else(||
                            SaveError::io(&file.key, "replacement has no prepared temporary file"))?;
                        replace_file(&prepared.path, &file.key)
                            .map_err(|error| SaveError::io(&file.key, error))?;
                        prepared.renamed = true;
                        Ok(())
                    }
                    Stage::Sync => synchronize_parent(&file.key)
                        .map_err(|error| SaveError::io(&file.key, error)),
                    Stage::Done => unreachable!("completed files are not dispatched"),
                }
            });
            match next {
                Ok(true) => break Ok(()),
                Ok(false) => {}
                Err(StepError::Callback(error)) => break Err(error),
                Err(StepError::Halted) => unreachable!("failed saves return immediately"),
            }
        };
        let mut report = SaveReport::default();
        for (index, document) in save.files().iter().enumerate() {
            let state = save.progress(index).expect("stored document index");
            let path = &document.data().key;
            if state.written {
                report.written.push(path.clone());
            }
            if state.unchanged {
                report.unchanged.push(path.clone());
            }
            if state.remaining {
                report.remaining.push(path.clone());
            }
            if state.merged_external {
                report.merged_external.push(path.clone());
            }
            if state.durability_uncertain {
                report.durability_uncertain.push(path.clone());
            }
        }
        assert!(
            configuration.accept_saved_sources(domain, save).is_ok(),
            "the exclusively borrowed accepted configuration still matches the reviewed save"
        );
        match result {
            Ok(()) => Ok(report),
            Err(mut error) => {
                error.report = Box::new(report);
                Err(error)
            }
        }
    }
}

pub(crate) fn check_regular(path: &Path) -> Result<(), SaveError> {
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
    Ok(())
}

fn read_regular(path: &Path) -> Result<(String, Permissions), SaveError> {
    check_regular(path)?;
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
#[cfg(windows)]
fn replace_file(source: &Path, destination: &Path) -> std::io::Result<()> {
    // Temporary::new keeps both files in the same directory. The safe wrapper
    // uses MoveFileExW(REPLACE_EXISTING | WRITE_THROUGH), without COPY_ALLOWED.
    atomicwrites::replace_atomic(source, destination)
}
#[cfg(not(windows))]
fn replace_file(source: &Path, destination: &Path) -> std::io::Result<()> {
    fs::rename(source, destination)
}
#[cfg(unix)]
fn sync_parent(path: &Path) -> std::io::Result<()> {
    File::open(path.parent().unwrap_or(Path::new(".")))?.sync_all()
}
#[cfg(windows)]
fn sync_parent(path: &Path) -> std::io::Result<()> {
    // Replacement already used the Windows write-through metadata barrier.
    // Flush the committed file too; a failed flush remains retryable without
    // rewriting that file or replaying a successful replacement.
    OpenOptions::new().write(true).open(path)?.sync_all()
}
#[cfg(not(any(unix, windows)))]
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
// Keyed children are encoded separately from their order. JSON arrays in user
// configuration remain atomic values; only entry lists receive keyed merging.
fn encoded_entries(entries: &[Entry], path: &str) -> Result<Value, String> {
    let mut members = Map::new();
    let mut order = Vec::new();
    for entry in entries {
        let child_path = format!("{path}/{}", entry.id);
        let mut fields = serde_json::to_value(entry).expect("Entry serialization");
        fields.as_object_mut().unwrap().insert(
            "children".into(),
            encoded_entries(&entry.children, &child_path)?,
        );
        if members.insert(entry.id.clone(), fields).is_some() {
            return Err(format!("{child_path} (duplicate id)"));
        }
        order.push(Value::String(entry.id.clone()));
    }
    Ok(serde_json::json!({"<order>": order, "<entries>": members}))
}

fn decoded_entries(value: Value, path: &str) -> Result<Vec<Entry>, String> {
    let invalid = || format!("{path}/<order>");
    let order = value
        .get("<order>")
        .and_then(Value::as_array)
        .ok_or_else(invalid)?
        .iter()
        .map(|id| id.as_str().map(str::to_owned).ok_or_else(invalid))
        .collect::<Result<Vec<_>, _>>()?;
    let members = value
        .get("<entries>")
        .and_then(Value::as_object)
        .ok_or_else(invalid)?;
    let members = members
        .iter()
        .map(|(key, value)| (key.clone(), crate::config_data::encode(value)))
        .collect::<Vec<_>>();
    let ordered =
        cordis_kernel::configuration_data::ordered(&members, &order).map_err(|_| invalid())?;
    ordered
        .into_iter()
        .zip(order)
        .map(|(entry, id)| {
            let mut value = crate::config_data::decode(entry);
            let child_path = format!("{path}/{id}");
            let children = value
                .as_object_mut()
                .and_then(|entry| entry.remove("children"))
                .ok_or_else(|| child_path.clone())?;
            let children = decoded_entries(children, &child_path)?;
            value
                .as_object_mut()
                .ok_or_else(|| child_path.clone())?
                .insert("children".into(), Value::Array(Vec::new()));
            let mut entry: Entry = serde_json::from_value(value).map_err(|_| child_path.clone())?;
            if entry.id != id {
                return Err(child_path);
            }
            entry.children = children;
            Ok(entry)
        })
        .collect()
}

fn conflict_path(root: &str, parts: Vec<String>) -> String {
    // Strip only the keyed encoding's structural markers. User entry IDs and
    // configuration keys may themselves be named <entries> or children.
    enum Position {
        List,
        Id,
        Field,
        Data,
    }
    let mut position = Position::List;
    let mut visible = Vec::new();
    for part in parts {
        match position {
            Position::List if part == "<entries>" => position = Position::Id,
            Position::Id => {
                visible.push(part);
                position = Position::Field;
            }
            Position::Field if part == "children" => position = Position::List,
            _ => {
                visible.push(part);
                position = Position::Data;
            }
        }
    }
    format!("{root}/{}", visible.join("/"))
}

fn merge_entries(
    base: &[Entry],
    ours: &[Entry],
    theirs: &[Entry],
    path: &str,
    conflicts: &mut Vec<String>,
) -> Vec<Entry> {
    let result = (|| {
        let base = encoded_entries(base, path)?;
        let ours = encoded_entries(ours, path)?;
        let theirs = encoded_entries(theirs, path)?;
        let merged = crate::config_data::merge(&base, &ours, &theirs)
            .map_err(|parts| conflict_path(path, parts))?;
        decoded_entries(merged, path)
    })();
    match result {
        Ok(entries) => entries,
        Err(error) => {
            conflicts.push(error);
            Vec::new()
        }
    }
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
        let sources = BTreeMap::from([(path.clone(), base_text.clone())]);
        let mut configuration = cordis_kernel::configuration_recorded::Recorded::<
            (),
            (),
            (),
            (),
            PathBuf,
            ConfigTree,
        >::new(());
        configuration
            .load_sources(cordis_kernel::configuration_recorded::Load {
                root: path.clone(),
                contents: sources.clone(),
                checkpoints: vec![(path.clone(), base.clone())],
                resolutions: BTreeMap::new(),
            })
            .unwrap();
        let desired = BTreeMap::from([(path.clone(), ours.clone())]);
        let plan = SavePlan::prepare(
            ours.clone(),
            sources.clone(),
            BTreeMap::from([(path.clone(), base)]),
            desired.clone(),
            SaveOrigin {
                registry_revision: 0,
                configuration: configuration.save_stamp(0).unwrap(),
            },
            BTreeSet::new(),
            BTreeMap::new(),
        )
        .unwrap();
        let error = plan
            .commit_with(&mut configuration, 0, |_| {
                Err(std::io::Error::other("injected directory fsync failure"))
            })
            .unwrap_err();
        assert_eq!(error.report.written, vec![path.clone()]);
        assert_eq!(error.report.durability_uncertain, vec![path.clone()]);
        assert!(error.report.remaining.is_empty());
        assert_eq!(
            ConfigTree::from_json(&fs::read_to_string(&path).unwrap()).unwrap(),
            ours
        );
        assert_eq!(configuration.sources().checkpoints()[&path].value, ours);
        assert!(configuration.sources().checkpoints()[&path].pending_sync);
        assert_eq!(configuration.sources().contents()[&path], base_text);
        // Replan from the retained owner, not from the report or expected state.
        let pending_sync = configuration
            .sources()
            .checkpoints()
            .iter()
            .filter_map(|(key, entry)| entry.pending_sync.then_some(key.clone()))
            .collect();
        let checkpoints = configuration
            .sources()
            .checkpoints()
            .iter()
            .map(|(key, entry)| (key.clone(), entry.value.clone()))
            .collect();
        let retry = SavePlan::prepare(
            ours.clone(),
            configuration.sources().contents().clone(),
            checkpoints,
            desired,
            SaveOrigin {
                registry_revision: 0,
                configuration: configuration.save_stamp(0).unwrap(),
            },
            pending_sync,
            BTreeMap::new(),
        )
        .unwrap();
        assert!(!retry.files()[0].will_write());
        let calls = Cell::new(0);
        let result = retry
            .commit_with(&mut configuration, 0, |_| {
                calls.set(calls.get() + 1);
                Ok(())
            })
            .unwrap();
        assert_eq!(calls.get(), 1);
        assert_eq!(result.unchanged, vec![path.clone()]);
        assert_eq!(configuration.sources().checkpoints()[&path].value, ours);
        assert!(!configuration.sources().checkpoints()[&path].pending_sync);
        assert_eq!(configuration.sources().contents()[&path], base_text);
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
