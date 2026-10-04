//! Declarative JSON trees, include files and explicit Rust factory HMR.
//! These host operations are behavior-tested, not Verus-proved callbacks.

use crate::config::{ConfigError, ConfigScope, Schema};
use crate::persistence::{SaveError, SaveErrorKind, SavePlan, SaveReport};
use crate::{Context, Plugin, PluginId, Runtime, RuntimeError, ServiceKey};
use serde::{Deserialize, Serialize};
use serde_json::{Map, Value};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::fs;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::path::{Path, PathBuf};
use std::sync::Arc;

fn enabled() -> bool {
    true
}
fn empty_config() -> Value {
    Value::Object(Map::new())
}

/// IDs are configuration keys local to a parent. Runtime IDs change on revision.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct Entry {
    pub id: String,
    /// Missing name creates an ownership group.
    #[serde(default)]
    pub name: Option<String>,
    #[serde(default = "enabled")]
    pub enabled: bool,
    #[serde(default = "empty_config")]
    pub config: Value,
    #[serde(default)]
    pub inject: Vec<String>,
    #[serde(default)]
    pub isolate: Vec<String>,
    #[serde(default)]
    pub intercept: BTreeMap<String, Value>,
    #[serde(default)]
    pub metadata: Map<String, Value>,
    #[serde(default)]
    pub children: Vec<Entry>,
    /// Relative to the containing file; included entries become scoped children.
    #[serde(default)]
    pub include: Option<PathBuf>,
}
/// Borrowed six-field record of Definition 81. Module URLs are resolved by the
/// caller; registered factory names are not treated as URLs implicitly.
pub type PaperEntry<'a, Url> = cordis_kernel::configuration_entry::Entry<
    &'a str,
    Url,
    &'a [String],
    &'a BTreeMap<String, Value>,
    &'a Value,
>;
impl Entry {
    /// Project a named plugin leaf after explicitly resolving its module URL.
    ///
    /// Groups, includes, unresolved names and entries with children return None:
    /// their encoding requires a separate grouped-component interpretation.
    /// Configuration is the recorded raw value, before schema/interception
    /// processing. Administrative disabled is this entry's own `!enabled`, not
    /// its parent's effective status. Extra host fields and execution behavior
    /// are outside this record projection.
    pub fn as_paper_entry<Url>(
        &self,
        resolve_url: impl FnOnce(&str) -> Option<Url>,
    ) -> Option<PaperEntry<'_, Url>> {
        if self.include.is_some() || !self.children.is_empty() {
            return None;
        }
        let url = resolve_url(self.name.as_deref()?)?;
        Some(cordis_kernel::configuration_entry::Entry::new(
            self.id.as_str(),
            url,
            self.isolate.as_slice(),
            &self.intercept,
            &self.config,
            !self.enabled,
        ))
    }

    pub fn plugin(id: impl Into<String>, name: impl Into<String>, config: Value) -> Self {
        Self {
            id: id.into(),
            name: Some(name.into()),
            enabled: true,
            config,
            inject: Vec::new(),
            isolate: Vec::new(),
            intercept: BTreeMap::new(),
            metadata: Map::new(),
            children: Vec::new(),
            include: None,
        }
    }
    pub fn group(id: impl Into<String>, children: Vec<Entry>) -> Self {
        Self {
            name: None,
            children,
            ..Self::plugin(id, "", empty_config())
        }
    }
}
#[derive(Clone, Debug, Default, Serialize, Deserialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct ConfigTree {
    pub entries: Vec<Entry>,
}
impl ConfigTree {
    /// Accept an entries object or the entries array itself.
    pub fn from_json(text: &str) -> Result<Self, LoaderError> {
        let value: Value =
            serde_json::from_str(text).map_err(|error| ConfigError::new("$", error.to_string()))?;
        if value.is_array() {
            serde_json::from_value(value).map(|entries| Self { entries })
        } else {
            serde_json::from_value(value)
        }
        .map_err(|error| ConfigError::new("$", error.to_string()).into())
    }
    pub fn to_json(&self) -> Result<String, LoaderError> {
        serde_json::to_string_pretty(self)
            .map_err(|error| ConfigError::new("$", error.to_string()).into())
    }
    pub fn entry_mut(&mut self, path: &str) -> Option<&mut Entry> {
        fn find<'a>(entries: &'a mut [Entry], parts: &[&str]) -> Option<&'a mut Entry> {
            let (first, rest) = parts.split_first()?;
            let entry = entries.iter_mut().find(|entry| entry.id == *first)?;
            if rest.is_empty() {
                Some(entry)
            } else {
                find(&mut entry.children, rest)
            }
        }
        find(&mut self.entries, &path.split('/').collect::<Vec<_>>())
    }
}
type Factory = Arc<dyn Fn(&Value, &ConfigScope) -> Result<Plugin, String> + Send + Sync>;
type Require = Arc<dyn Fn(Plugin) -> Plugin + Send + Sync>;
type Isolate = Arc<dyn Fn(&Context) -> Context + Send + Sync>;
#[derive(Clone)]
struct RegisteredFactory {
    revision: u64,
    schema: Schema,
    build: Factory,
}
#[derive(Clone)]
struct RegisteredService {
    revision: u64,
    require: Require,
    isolate: Isolate,
}

/// Re-registration is an explicit code revision. Old recipes retain old factories
/// so failed revisions can restore the last committed configuration.
#[derive(Clone, Default)]
pub struct FactoryRegistry {
    factories: BTreeMap<String, Arc<RegisteredFactory>>,
    services: BTreeMap<String, RegisteredService>,
    revision: u64,
}
impl FactoryRegistry {
    pub fn new() -> Self {
        Self::default()
    }
    fn next_revision(&mut self) -> u64 {
        self.revision = self
            .revision
            .checked_add(1)
            .expect("factory revision space exhausted");
        self.revision
    }
    pub fn register(
        &mut self,
        name: impl Into<String>,
        schema: Schema,
        factory: impl Fn(&Value, &ConfigScope) -> Result<Plugin, String> + Send + Sync + 'static,
    ) -> u64 {
        let revision = self.next_revision();
        self.factories.insert(
            name.into(),
            Arc::new(RegisteredFactory {
                revision,
                schema,
                build: Arc::new(factory),
            }),
        );
        revision
    }
    pub fn register_service<T: 'static>(&mut self, name: impl Into<String>, key: ServiceKey<T>) {
        let revision = self.next_revision();
        self.services.insert(
            name.into(),
            RegisteredService {
                revision,
                require: Arc::new(move |plugin| plugin.requires(key)),
                isolate: Arc::new(move |context| context.isolate(key)),
            },
        );
    }
    pub fn revision(&self, name: &str) -> Option<u64> {
        self.factories.get(name).map(|factory| factory.revision)
    }
    pub fn names(&self) -> impl Iterator<Item = &str> {
        self.factories.keys().map(String::as_str)
    }
}
#[derive(Debug)]
pub enum LoaderError {
    Config(ConfigError),
    Source {
        path: PathBuf,
        message: String,
    },
    IncludeCycle(Vec<PathBuf>),
    Factory {
        entry: String,
        message: String,
    },
    Runtime(RuntimeError),
    /// No rollback error means the previous configuration was restored.
    Apply {
        cause: Box<LoaderError>,
        rollback: Option<Box<LoaderError>>,
    },
}
impl From<ConfigError> for LoaderError {
    fn from(error: ConfigError) -> Self {
        Self::Config(error)
    }
}
impl From<RuntimeError> for LoaderError {
    fn from(error: RuntimeError) -> Self {
        Self::Runtime(error)
    }
}
impl fmt::Display for LoaderError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Config(error) => write!(f, "{error}"),
            Self::Source { path, message } => write!(f, "{}: {message}", path.display()),
            Self::IncludeCycle(paths) => write!(
                f,
                "include cycle: {}",
                paths
                    .iter()
                    .map(|path| path.display().to_string())
                    .collect::<Vec<_>>()
                    .join(" -> ")
            ),
            Self::Factory { entry, message } => write!(f, "factory at {entry}: {message}"),
            Self::Runtime(error) => write!(f, "{error}"),
            Self::Apply {
                cause,
                rollback: None,
            } => write!(
                f,
                "revision failed; previous configuration restored: {cause}"
            ),
            Self::Apply {
                cause,
                rollback: Some(rollback),
            } => write!(
                f,
                "revision failed: {cause}; recovery remains pending: {rollback}"
            ),
        }
    }
}
impl std::error::Error for LoaderError {}
#[derive(Clone, PartialEq)]
struct Signature {
    entry: Entry,
    inject: Vec<(String, u64)>,
    isolate: Vec<(String, u64)>,
    factory: Option<u64>,
    enabled: bool,
}
#[derive(Clone)]
struct Node {
    path: String,
    parent: Option<String>,
    scope: ConfigScope,
    signature: Signature,
    factory: Option<Arc<RegisteredFactory>>,
    inject: Vec<RegisteredService>,
    id: Option<PluginId>,
}
impl Node {
    fn build(&self) -> Result<Plugin, LoaderError> {
        let result = catch_unwind(AssertUnwindSafe(|| match &self.factory {
            Some(factory) => (factory.build)(&self.signature.entry.config, &self.scope),
            None => Ok(Plugin::new(format!("group:{}", self.path), |_| Ok(()))),
        }));
        let mut plugin = result
            .map_err(|_| LoaderError::Factory {
                entry: self.path.clone(),
                message: "factory panicked".into(),
            })?
            .map_err(|message| LoaderError::Factory {
                entry: self.path.clone(),
                message,
            })?;
        for service in &self.inject {
            plugin = (service.require)(plugin);
        }
        Ok(plugin)
    }
}
#[derive(Clone, Default)]
struct Snapshot {
    tree: ConfigTree,
    nodes: BTreeMap<String, Node>,
    order: Vec<String>,
}
impl Snapshot {
    fn parent_for(&self, node: &Node, root_parent: Option<PluginId>) -> Option<PluginId> {
        node.parent
            .as_ref()
            .and_then(|parent| self.nodes[parent].id)
            .or(root_parent)
    }
}

/// File provenance and save progress belong to the last successful file load.
/// Clear them together only after switching to a non-file source succeeds.
#[derive(Default)]
struct SourceTracking {
    root: Option<PathBuf>,
    contents: BTreeMap<PathBuf, String>,
    checkpoints: BTreeMap<PathBuf, ConfigTree>,
    pending_sync: BTreeSet<PathBuf>,
    resolutions: BTreeMap<PathBuf, PathBuf>,
}

struct Transaction {
    before: Snapshot,
    created: Vec<PluginId>,
}
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ApplyReport {
    pub revision: u64,
    pub changed: Vec<String>,
    pub removed: Vec<String>,
    pub retained: usize,
}
impl ApplyReport {
    pub fn is_unchanged(&self) -> bool {
        self.changed.is_empty() && self.removed.is_empty()
    }
}

/// Dropping a mutation future preserves a pending transaction. The next mutation
/// or explicit recover() restores the last committed tree before continuing.
pub struct Loader {
    runtime: Runtime,
    root: ConfigScope,
    parent: Option<PluginId>,
    registry: FactoryRegistry,
    current: Snapshot,
    pending: Option<Transaction>,
    revision: u64,
    source: SourceTracking,
}
impl Loader {
    pub fn new(context: Context, registry: FactoryRegistry) -> Self {
        Self::with_runtime(Runtime::new(), ConfigScope::new(context), registry, None)
    }
    pub fn with_runtime(
        runtime: Runtime,
        root: ConfigScope,
        registry: FactoryRegistry,
        parent: Option<PluginId>,
    ) -> Self {
        Self {
            runtime,
            root,
            parent,
            registry,
            current: Snapshot::default(),
            pending: None,
            revision: 0,
            source: SourceTracking::default(),
        }
    }
    pub fn runtime(&self) -> &Runtime {
        &self.runtime
    }
    pub fn runtime_mut(&mut self) -> &mut Runtime {
        &mut self.runtime
    }
    pub fn registry(&self) -> &FactoryRegistry {
        &self.registry
    }
    pub fn registry_mut(&mut self) -> &mut FactoryRegistry {
        &mut self.registry
    }
    /// Last successfully committed configuration, including expanded includes.
    pub fn tree(&self) -> &ConfigTree {
        &self.current.tree
    }
    pub fn id(&self, path: &str) -> Option<PluginId> {
        let id = self.current.nodes.get(path)?.id?;
        self.runtime.contains(id).then_some(id)
    }
    pub fn scope(&self, path: &str) -> Option<&ConfigScope> {
        self.current.nodes.get(path).map(|node| &node.scope)
    }
    pub fn revision(&self) -> u64 {
        self.revision
    }
    pub fn recovery_pending(&self) -> bool {
        self.pending.is_some()
    }
    pub fn watched_files(&self) -> impl Iterator<Item = &Path> {
        self.source.contents.keys().map(PathBuf::as_path)
    }

    fn prepare(&self, tree: ConfigTree) -> Result<Snapshot, LoaderError> {
        struct Planner<'a> {
            loader: &'a Loader,
            plan: Snapshot,
        }
        impl Planner<'_> {
            #[allow(clippy::too_many_arguments)]
            fn visit(
                &mut self,
                entries: &[Entry],
                parent: Option<&str>,
                scope: &ConfigScope,
                inherited: &[String],
                parent_enabled: bool,
                parent_retained: bool,
                depth: usize,
            ) -> Result<(), LoaderError> {
                if depth > 128 {
                    return Err(ConfigError::new(
                        parent.unwrap_or("$"),
                        "configuration nesting exceeds 128",
                    )
                    .into());
                }
                let mut siblings = BTreeSet::new();
                for entry in entries {
                    if entry.id.is_empty()
                        || entry.id.contains('/')
                        || entry.id.contains(':')
                        || !siblings.insert(entry.id.clone())
                    {
                        return Err(ConfigError::new(
                            parent.unwrap_or("$"),
                            "entry IDs must be unique, nonempty, and contain neither / nor :",
                        )
                        .into());
                    }
                    let path = parent.map_or_else(
                        || entry.id.clone(),
                        |parent| format!("{parent}/{}", entry.id),
                    );
                    if entry.include.is_some() {
                        return Err(ConfigError::new(
                            &path,
                            "includes require load_file(), not apply() or load_json()",
                        )
                        .into());
                    }
                    let mut scope = scope.extend_json(&entry.metadata);
                    for (name, patch) in &entry.intercept {
                        scope = scope.intercept(name, patch.clone());
                    }
                    let mut inject = inherited.to_vec();
                    for name in &entry.inject {
                        if !inject.contains(name) {
                            inject.push(name.clone());
                        }
                    }
                    inject.sort();
                    let service = |name: &str| {
                        self.loader
                            .registry
                            .services
                            .get(name)
                            .cloned()
                            .ok_or_else(|| {
                                ConfigError::new(&path, format!("unknown service: {name}"))
                            })
                    };
                    let services = inject
                        .iter()
                        .map(|name| service(name))
                        .collect::<Result<Vec<_>, _>>()?;
                    let isolates = entry
                        .isolate
                        .iter()
                        .map(|name| service(name))
                        .collect::<Result<Vec<_>, _>>()?;
                    let factory = match &entry.name {
                        Some(name) => Some(
                            self.loader
                                .registry
                                .factories
                                .get(name)
                                .cloned()
                                .ok_or_else(|| {
                                    ConfigError::new(
                                        &path,
                                        format!("unknown plugin factory: {name}"),
                                    )
                                })?,
                        ),
                        None => None,
                    };
                    let mut normalized = entry.clone();
                    normalized.children.clear();
                    if let Some(factory) = &factory {
                        normalized.config = factory
                            .schema
                            .validate(&scope.resolve(entry.name.as_deref().unwrap(), &entry.config))
                            .map_err(|error| {
                                ConfigError::new(format!("{path}{}", error.path), error.message)
                            })?;
                    }
                    let signature = Signature {
                        entry: normalized,
                        inject: inject
                            .iter()
                            .zip(&services)
                            .map(|(name, service)| (name.clone(), service.revision))
                            .collect(),
                        isolate: entry
                            .isolate
                            .iter()
                            .zip(&isolates)
                            .map(|(name, service)| (name.clone(), service.revision))
                            .collect(),
                        factory: factory.as_ref().map(|factory| factory.revision),
                        enabled: parent_enabled && entry.enabled,
                    };
                    let retained = parent_retained
                        && self.loader.current.nodes.get(&path).is_some_and(|old| {
                            old.signature == signature
                                && match old.id {
                                    Some(id) => {
                                        self.loader.runtime.contains(id)
                                            && !self.loader.runtime.retired(id)
                                    }
                                    None => !signature.enabled,
                                }
                        });
                    let id = if retained {
                        let old = &self.loader.current.nodes[&path];
                        scope = old.scope.clone();
                        old.id
                    } else {
                        for service in isolates {
                            scope = scope.with_context((service.isolate)(scope.context()));
                        }
                        None
                    };
                    self.plan.order.push(path.clone());
                    self.plan.nodes.insert(
                        path.clone(),
                        Node {
                            path: path.clone(),
                            parent: parent.map(str::to_owned),
                            scope: scope.clone(),
                            signature: signature.clone(),
                            factory,
                            inject: services,
                            id,
                        },
                    );
                    self.visit(
                        &entry.children,
                        Some(&path),
                        &scope,
                        &inject,
                        signature.enabled,
                        retained,
                        depth + 1,
                    )?;
                }
                Ok(())
            }
        }
        let mut planner = Planner {
            loader: self,
            plan: Snapshot {
                tree: tree.clone(),
                ..Snapshot::default()
            },
        };
        planner.visit(&tree.entries, None, &self.root, &[], true, true, 0)?;
        Ok(planner.plan)
    }

    pub async fn load_json(&mut self, json: &str) -> Result<ApplyReport, LoaderError> {
        self.recover().await?;
        let report = self.apply(ConfigTree::from_json(json)?).await?;
        self.source = SourceTracking::default();
        Ok(report)
    }
    pub async fn apply(&mut self, tree: ConfigTree) -> Result<ApplyReport, LoaderError> {
        self.recover().await?;
        let mut settled = false;
        let (mut plan, mut report) = loop {
            let plan = self.prepare(tree.clone())?;
            let mut report = ApplyReport {
                revision: self.revision,
                ..ApplyReport::default()
            };
            for path in &plan.order {
                let node = &plan.nodes[path];
                let unchanged = self.current.nodes.get(path).is_some_and(|old| {
                    node.signature == old.signature
                        && node.id == old.id
                        && (!node.signature.enabled || node.id.is_some())
                });
                if unchanged {
                    report.retained += 1;
                } else {
                    report.changed.push(path.clone());
                }
            }
            report.removed = self
                .current
                .order
                .iter()
                .filter(|path| !plan.nodes.contains_key(*path))
                .cloned()
                .collect();
            if !report.is_unchanged() {
                break (plan, report);
            }
            if settled {
                self.current.tree = plan.tree;
                return Ok(report);
            }
            // An explicit runtime.restart() can retire owned config children even
            // when the configuration itself is unchanged. Reconcile after driving it.
            self.runtime.settle().await?;
            settled = true;
        };
        // A dependency revision can indirectly retire a retained owner's children.
        // Preconstruct standby plugins so their factory errors are also detected
        // before retiring any old resource.
        let mut plugins = BTreeMap::new();
        for path in &plan.order {
            let node = &plan.nodes[path];
            if node.signature.enabled {
                plugins.insert(path.clone(), node.build()?);
            }
        }
        self.pending = Some(Transaction {
            before: self.current.clone(),
            created: Vec::new(),
        });
        let result = self.apply_prepared(&mut plan, plugins).await;
        match result {
            Ok(()) => {
                report.changed =
                    plan.order
                        .iter()
                        .filter(|path| {
                            let next = &plan.nodes[*path];
                            self.current.nodes.get(*path).is_none_or(|old| {
                                old.signature != next.signature || old.id != next.id
                            })
                        })
                        .cloned()
                        .collect();
                report.retained = plan.nodes.len() - report.changed.len();
                self.current = plan;
                self.pending = None;
                self.revision = self
                    .revision
                    .checked_add(1)
                    .expect("loader revision space exhausted");
                report.revision = self.revision;
                Ok(report)
            }
            Err(cause) => {
                let rollback = self.recover().await.err().map(Box::new);
                Err(LoaderError::Apply {
                    cause: Box::new(cause),
                    rollback,
                })
            }
        }
    }

    async fn apply_prepared(
        &mut self,
        plan: &mut Snapshot,
        mut plugins: BTreeMap<String, Plugin>,
    ) -> Result<(), LoaderError> {
        for (path, old) in &self.current.nodes {
            if let Some(id) = old.id {
                if plan.nodes.get(path).and_then(|node| node.id) != Some(id) {
                    self.runtime.dispose(id)?;
                }
            }
        }
        self.runtime.settle().await?;
        // Dependency changes can also retire a retained node's owned children.
        for path in &plan.order {
            let node = &plan.nodes[path];
            if !node.signature.enabled {
                continue;
            }
            if node
                .id
                .is_some_and(|id| self.runtime.contains(id) && !self.runtime.retired(id))
            {
                continue;
            }
            let plugin = match plugins.remove(path) {
                Some(plugin) => plugin,
                None => node.build()?,
            };
            let parent = plan.parent_for(node, self.parent);
            let id = self.runtime.mount(node.scope.context(), parent, plugin)?;
            self.pending.as_mut().unwrap().created.push(id);
            plan.nodes.get_mut(path).unwrap().id = Some(id);
        }
        self.runtime.settle().await?;
        Ok(())
    }

    /// Restore interrupted/failed revisions using captured old factories. Newly
    /// restored IDs are recorded before awaiting, so recovery can also be dropped.
    pub async fn recover(&mut self) -> Result<(), LoaderError> {
        let Some(transaction) = &self.pending else {
            return Ok(());
        };
        for id in &transaction.created {
            self.runtime.dispose(*id)?;
        }
        for node in transaction.before.nodes.values() {
            if let Some(id) = node.id {
                if self.runtime.failure(id).is_some() {
                    self.runtime.dispose(id)?;
                }
            }
        }
        self.runtime.settle().await?;
        let order = self.pending.as_ref().unwrap().before.order.clone();
        for path in order {
            let node = self.pending.as_ref().unwrap().before.nodes[&path].clone();
            if !node.signature.enabled {
                continue;
            }
            if node
                .id
                .is_some_and(|id| self.runtime.contains(id) && !self.runtime.retired(id))
            {
                continue;
            }
            let plugin = node.build()?;
            let parent = self
                .pending
                .as_ref()
                .unwrap()
                .before
                .parent_for(&node, self.parent);
            let id = self.runtime.mount(node.scope.context(), parent, plugin)?;
            self.pending
                .as_mut()
                .unwrap()
                .before
                .nodes
                .get_mut(&path)
                .unwrap()
                .id = Some(id);
        }
        self.runtime.settle().await?;
        self.current = self.pending.take().unwrap().before;
        Ok(())
    }
    pub async fn reload(&mut self) -> Result<ApplyReport, LoaderError> {
        self.recover().await?;
        self.apply(self.current.tree.clone()).await
    }
    pub async fn set_enabled(
        &mut self,
        path: &str,
        enabled: bool,
    ) -> Result<ApplyReport, LoaderError> {
        self.recover().await?;
        let mut tree = self.current.tree.clone();
        tree.entry_mut(path)
            .ok_or_else(|| ConfigError::new(path, "unknown entry"))?
            .enabled = enabled;
        self.apply(tree).await
    }
    pub async fn dispose(&mut self) -> Result<ApplyReport, LoaderError> {
        let report = self.apply(ConfigTree::default()).await?;
        self.source = SourceTracking::default();
        Ok(report)
    }
    pub async fn load_file(&mut self, path: impl AsRef<Path>) -> Result<ApplyReport, LoaderError> {
        self.recover().await?;
        let loaded = read_tree(path.as_ref())?;
        let report = self.apply(loaded.tree).await?;
        self.source.root = Some(loaded.root);
        self.source.resolutions = loaded.resolutions;
        self.source.checkpoints = loaded
            .sources
            .iter()
            .map(|(path, text)| {
                // read_tree already parsed every source before committing the runtime.
                (
                    path.clone(),
                    ConfigTree::from_json(text).expect("successfully parsed source"),
                )
            })
            .collect();
        self.source.contents = loaded.sources;
        self.source
            .pending_sync
            .retain(|path| self.source.contents.contains_key(path));
        Ok(report)
    }
    /// Prepare an explicit, inspectable three-way save without writing files.
    /// Include boundaries are retained. New children directly beside an include
    /// have ambiguous ownership and must first be added through the source file.
    /// Saving never changes the running configuration; poll_reload applies any
    /// external edits retained by the merge.
    pub fn prepare_save(&self) -> Result<SavePlan, SaveError> {
        if self.pending.is_some() {
            return Err(SaveError::new(None, SaveErrorKind::RecoveryPending));
        }
        let root = self
            .source
            .root
            .as_ref()
            .ok_or_else(|| SaveError::new(None, SaveErrorKind::NoFileSource))?;
        let (desired, include_targets) = project_sources(
            root,
            &self.source.contents,
            &self.source.resolutions,
            &self.current.tree,
        )?;
        let plan = SavePlan::prepare(
            self.current.tree.clone(),
            self.source.contents.clone(),
            self.source.checkpoints.clone(),
            desired,
            self.registry.revision,
            self.source.pending_sync.clone(),
            include_targets,
        )?;
        let merged = read_tree_cached(root, Some(plan.merged_sources())).map_err(|error| {
            SaveError::new(
                None,
                SaveErrorKind::InvalidMergedConfiguration(error.to_string()),
            )
        })?;
        self.prepare(merged.tree).map_err(|error| {
            SaveError::new(
                None,
                SaveErrorKind::InvalidMergedConfiguration(error.to_string()),
            )
        })?;
        Ok(plan)
    }
    /// Commit a reviewed plan. Errors contain exact per-file progress; completed
    /// files remain saved, and another save can retry the remaining local edits.
    pub fn commit_save(&mut self, plan: SavePlan) -> Result<SaveReport, SaveError> {
        if self.pending.is_some() {
            return Err(SaveError::new(None, SaveErrorKind::RecoveryPending));
        }
        if plan.tree != self.current.tree
            || plan.sources != self.source.contents
            || plan.checkpoints != self.source.checkpoints
            || plan.registry_revision != self.registry.revision
            || plan.pending_sync != self.source.pending_sync
        {
            return Err(SaveError::new(None, SaveErrorKind::StalePlan));
        }
        let desired = plan.desired();
        let result = plan.commit();
        let report = match &result {
            Ok(report) => report,
            Err(error) => &error.report,
        };
        for path in report.written.iter().chain(&report.unchanged) {
            self.source
                .checkpoints
                .insert(path.clone(), desired[path].clone());
            if report.durability_uncertain.contains(path) {
                self.source.pending_sync.insert(path.clone());
            } else {
                self.source.pending_sync.remove(path);
            }
        }
        result
    }
    /// Explicit convenience operation; apply and set_enabled never write files.
    pub fn save(&mut self) -> Result<SaveReport, SaveError> {
        let plan = self.prepare_save()?;
        self.commit_save(plan)
    }
    /// Poll contents and factory revisions once from an application's timer/event
    /// loop. Invalid files leave the previous successful source snapshot intact.
    pub async fn poll_reload(&mut self) -> Result<ApplyReport, LoaderError> {
        let Some(path) = self.source.root.clone() else {
            return self.reload().await;
        };
        self.load_file(path).await
    }
}

struct LoadedTree {
    tree: ConfigTree,
    root: PathBuf,
    sources: BTreeMap<PathBuf, String>,
    resolutions: BTreeMap<PathBuf, PathBuf>,
}
fn read_tree(path: &Path) -> Result<LoadedTree, LoaderError> {
    read_tree_cached(path, None)
}
fn read_tree_cached(
    path: &Path,
    cached: Option<BTreeMap<PathBuf, String>>,
) -> Result<LoadedTree, LoaderError> {
    fn source_error(path: &Path, error: impl fmt::Display) -> LoaderError {
        LoaderError::Source {
            path: path.to_owned(),
            message: error.to_string(),
        }
    }
    fn read(
        path: &Path,
        stack: &mut Vec<PathBuf>,
        sources: &mut BTreeMap<PathBuf, String>,
        cached_only: bool,
        resolutions: &mut BTreeMap<PathBuf, PathBuf>,
    ) -> Result<ConfigTree, LoaderError> {
        let lexical = path.to_owned();
        let path = fs::canonicalize(path).map_err(|error| source_error(path, error))?;
        if resolutions
            .insert(lexical, path.clone())
            .is_some_and(|previous| previous != path)
        {
            return Err(source_error(&path, "include target changed while reading"));
        }
        if stack.contains(&path) {
            let mut cycle = stack.clone();
            cycle.push(path);
            return Err(LoaderError::IncludeCycle(cycle));
        }
        if stack.len() >= 128 {
            return Err(source_error(&path, "include nesting exceeds 128"));
        }
        let text = match sources.get(&path) {
            Some(text) => text.clone(),
            None if cached_only => {
                return Err(source_error(
                    &path,
                    "include source was not part of the save plan",
                ))
            }
            None => fs::read_to_string(&path).map_err(|error| source_error(&path, error))?,
        };
        let mut tree = ConfigTree::from_json(&text).map_err(|error| source_error(&path, error))?;
        sources.insert(path.clone(), text);
        stack.push(path.clone());
        fn expand(
            entries: &mut [Entry],
            base: &Path,
            stack: &mut Vec<PathBuf>,
            sources: &mut BTreeMap<PathBuf, String>,
            depth: usize,
            cached_only: bool,
            resolutions: &mut BTreeMap<PathBuf, PathBuf>,
        ) -> Result<(), LoaderError> {
            if depth > 128 {
                return Err(source_error(base, "configuration nesting exceeds 128"));
            }
            for entry in entries {
                expand(
                    &mut entry.children,
                    base,
                    stack,
                    sources,
                    depth + 1,
                    cached_only,
                    resolutions,
                )?;
                if let Some(include) = entry.include.take() {
                    let included = read(
                        &base.join(include),
                        stack,
                        sources,
                        cached_only,
                        resolutions,
                    )?;
                    entry.children.extend(included.entries);
                }
            }
            Ok(())
        }
        expand(
            &mut tree.entries,
            path.parent().unwrap_or(Path::new(".")),
            stack,
            sources,
            0,
            cached_only,
            resolutions,
        )?;
        stack.pop();
        Ok(tree)
    }
    let root = fs::canonicalize(path).map_err(|error| source_error(path, error))?;
    let cached_only = cached.is_some();
    let mut sources = cached.unwrap_or_default();
    let mut resolutions = BTreeMap::new();
    let tree = read(
        &root,
        &mut Vec::new(),
        &mut sources,
        cached_only,
        &mut resolutions,
    )?;
    Ok(LoadedTree {
        tree,
        root,
        sources,
        resolutions,
    })
}

type ProjectedSources = (BTreeMap<PathBuf, ConfigTree>, BTreeMap<PathBuf, PathBuf>);

/// Project expanded entries back into the successful read's include topology.
fn project_sources(
    root: &Path,
    sources: &BTreeMap<PathBuf, String>,
    resolutions: &BTreeMap<PathBuf, PathBuf>,
    tree: &ConfigTree,
) -> Result<ProjectedSources, SaveError> {
    struct Projector<'a> {
        sources: &'a BTreeMap<PathBuf, String>,
        desired: BTreeMap<PathBuf, ConfigTree>,
        resolutions: &'a BTreeMap<PathBuf, PathBuf>,
        used_resolutions: BTreeMap<PathBuf, PathBuf>,
    }
    impl Projector<'_> {
        fn error(path: &Path, message: impl Into<String>) -> SaveError {
            SaveError::new(Some(path), SaveErrorKind::Topology(message.into()))
        }
        fn raw(&self, path: &Path) -> Result<ConfigTree, SaveError> {
            let text = self
                .sources
                .get(path)
                .ok_or_else(|| Self::error(path, "source was not part of the successful load"))?;
            ConfigTree::from_json(text).map_err(|error| Self::error(path, error.to_string()))
        }
        fn file(&mut self, path: &Path, entries: &[Entry]) -> Result<(), SaveError> {
            let raw = self.raw(path)?;
            let projected = ConfigTree {
                entries: self.entries(path, &raw.entries, entries)?,
            };
            if self
                .desired
                .get(path)
                .is_some_and(|previous| previous != &projected)
            {
                return Err(Self::error(path, "shared include instances have different edits; edit all instances consistently or split the include in its source"));
            }
            self.desired.insert(path.to_owned(), projected);
            Ok(())
        }
        fn entries(
            &mut self,
            path: &Path,
            template: &[Entry],
            entries: &[Entry],
        ) -> Result<Vec<Entry>, SaveError> {
            let mut result = Vec::new();
            for current in entries {
                let original = template.iter().find(|entry| entry.id == current.id);
                let mut entry = current.clone();
                if let Some(include) = original.and_then(|entry| entry.include.as_ref()) {
                    let original = original.unwrap();
                    let lexical = path.parent().unwrap_or(Path::new(".")).join(include);
                    let included_path = self
                        .resolutions
                        .get(&lexical)
                        .ok_or_else(|| {
                            Self::error(path, "include target was not part of the successful load")
                        })?
                        .clone();
                    let current_target = fs::canonicalize(&lexical)
                        .map_err(|error| Self::error(path, error.to_string()))?;
                    if current_target != included_path {
                        return Err(Self::error(
                            path,
                            "include target changed after loading; reload before saving",
                        ));
                    }
                    self.used_resolutions.insert(lexical, included_path.clone());
                    let included = self.raw(&included_path)?;
                    let mut inline = Vec::new();
                    let mut external = Vec::new();
                    for child in &current.children {
                        if original.children.iter().any(|entry| entry.id == child.id) {
                            inline.push(child.clone());
                        } else if included.entries.iter().any(|entry| entry.id == child.id) {
                            external.push(child.clone());
                        } else {
                            return Err(Self::error(path, format!("new child {} of include entry {} has no source owner; add it in the intended source file and reload", child.id, current.id)));
                        }
                    }
                    // Inline children precede include children at expansion time.
                    // Reject ordering edits that cannot round-trip that boundary.
                    let reconstructed: Vec<_> = inline
                        .iter()
                        .chain(&external)
                        .map(|entry| &entry.id)
                        .collect();
                    if reconstructed
                        != current
                            .children
                            .iter()
                            .map(|entry| &entry.id)
                            .collect::<Vec<_>>()
                    {
                        return Err(Self::error(
                            path,
                            format!(
                                "children of {} cross the inline/include ordering boundary",
                                current.id
                            ),
                        ));
                    }
                    entry.children = self.entries(path, &original.children, &inline)?;
                    entry.include = Some(include.clone());
                    self.file(&included_path, &external)?;
                } else {
                    entry.children = self.entries(
                        path,
                        original.map_or(&[], |entry| entry.children.as_slice()),
                        &current.children,
                    )?;
                }
                result.push(entry);
            }
            Ok(result)
        }
    }
    let mut projector = Projector {
        sources,
        desired: BTreeMap::new(),
        resolutions,
        used_resolutions: BTreeMap::new(),
    };
    projector.file(root, &tree.entries)?;
    Ok((projector.desired, projector.used_resolutions))
}
