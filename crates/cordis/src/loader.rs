//! Declarative JSON trees, include files and explicit Rust factory HMR.
//! These host operations are behavior-tested, not Verus-proved callbacks.

use crate::config::{ConfigError, ConfigScope, ConfigUpdate, ConfigUpdatePlan, Schema};
use crate::persistence::{SaveError, SaveErrorKind, SaveOrigin, SavePlan, SaveReport};
use crate::{Context, Phase, Plugin, PluginId, Runtime, RuntimeError, ServiceKey};
use cordis_kernel::configuration_planning as planning;
use cordis_kernel::configuration_transaction::{Structure, StructureError};
use serde::{Deserialize, Serialize};
use serde_json::{Map, Value};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::fs;
use std::future::{poll_fn, Future};
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::path::{Path, PathBuf};
use std::pin::Pin;
use std::sync::Arc;
use std::task::Poll;

fn structure_error(error: StructureError<LoaderError>) -> LoaderError {
    match error {
        StructureError::Callback(error) => error,
        StructureError::NotReady => LoaderError::Transaction(
            cordis_kernel::configuration_transaction::TransactionError::NotReady,
        ),
    }
}

fn enabled() -> bool {
    true
}
fn empty_config() -> Value {
    Value::Object(Map::new())
}

/// Required services with per-consumer configuration. JSON accepts either
/// `["model"]` or `{ "model": { "capability": "chat" } }`; arrays use null config.
#[derive(Clone, Debug, Default, Serialize, PartialEq)]
#[serde(transparent)]
pub struct Inject(BTreeMap<String, Value>);
impl Inject {
    pub fn push(&mut self, name: String) {
        self.0.insert(name, Value::Null);
    }
    pub fn insert(&mut self, name: impl Into<String>, config: Value) -> Option<Value> {
        self.0.insert(name.into(), config)
    }
    pub fn get(&self, name: &str) -> Option<&Value> {
        self.0.get(name)
    }
    pub fn iter(&self) -> impl Iterator<Item = (&String, &Value)> {
        self.0.iter()
    }
}
impl<'de> Deserialize<'de> for Inject {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        #[derive(Deserialize)]
        #[serde(untagged)]
        enum Declaration {
            Names(Vec<String>),
            Config(BTreeMap<String, Value>),
            Empty(()),
        }
        Ok(Self(match Declaration::deserialize(deserializer)? {
            Declaration::Names(names) => {
                names.into_iter().map(|name| (name, Value::Null)).collect()
            }
            Declaration::Config(config) => config,
            Declaration::Empty(()) => BTreeMap::new(),
        }))
    }
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
    pub inject: Inject,
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
type ExpansionEntry = cordis_kernel::configuration_expansion::Entry<Entry, PathBuf>;
type ExpansionDocument = cordis_kernel::configuration_expansion::Document<Entry, PathBuf, PathBuf>;
impl Entry {
    // JSON decoding is the input boundary. Move structural fields into the
    // checked expander; the remaining entry payload is preserved without cloning.
    fn into_expansion(mut self) -> ExpansionEntry {
        let children = std::mem::take(&mut self.children)
            .into_iter()
            .map(Self::into_expansion)
            .collect();
        let include = self.include.take();
        ExpansionEntry::new(self, children, include)
    }
    fn from_expansion(expanded: ExpansionEntry) -> Self {
        let mut entry = expanded.payload;
        entry.children = expanded
            .children
            .into_iter()
            .map(Self::from_expansion)
            .collect();
        entry.include = expanded.include;
        entry
    }
    fn into_planning(mut self) -> planning::Entry<Self> {
        let children = std::mem::take(&mut self.children)
            .into_iter()
            .map(Self::into_planning)
            .collect();
        planning::Entry::new(self.id.clone(), self.enabled, self, children)
    }
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
            inject: Inject::default(),
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
type Require = Arc<dyn Fn(Plugin, Value) -> Plugin + Send + Sync>;
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
                require: Arc::new(move |plugin, config| plugin.requires_with_config(key, config)),
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
    Transaction(cordis_kernel::configuration_transaction::TransactionError),
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
    Update {
        entry: String,
        error: crate::CallbackError,
    },
    /// The configuration was committed, but dependent lifecycle propagation failed.
    PostCommit {
        revision: u64,
        cause: Box<LoaderError>,
    },
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
            Self::Transaction(error) => write!(f, "configuration transaction: {error:?}"),
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
            Self::Update { entry, error } => write!(f, "configuration update at {entry}: {error}"),
            Self::PostCommit { revision, cause } => write!(f, "configuration revision {revision} committed; lifecycle propagation failed: {cause}"),
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
impl std::error::Error for LoaderError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Config(error) => Some(error),
            Self::Runtime(error) => Some(error),
            Self::Update { error, .. } => Some(error),
            Self::PostCommit { cause, .. } | Self::Apply { cause, .. } => Some(cause.as_ref()),
            _ => None,
        }
    }
}
#[derive(Clone, PartialEq)]
struct Signature {
    entry: Entry,
    inject: Vec<(String, u64)>,
    isolate: Vec<(String, u64)>,
    factory: Option<u64>,
    enabled: bool,
}
impl Signature {
    fn only_config_changed(&self, previous: &Self) -> bool {
        if self.entry.config == previous.entry.config {
            return false;
        }
        let mut normalized = self.clone();
        normalized.entry.config = previous.entry.config.clone();
        normalized == *previous
    }
}
#[derive(Clone)]
struct Node {
    path: String,
    scope: ConfigScope,
    signature: Signature,
    factory: Option<Arc<RegisteredFactory>>,
    inject: Vec<(RegisteredService, Value)>,
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
        for (service, config) in &self.inject {
            plugin = (service.require)(plugin, config.clone());
        }
        Ok(plugin)
    }
}
type CheckedNode = cordis_kernel::configuration_tree::Node<Node>;

/// The index is only a lookup cache. The checked owner stores the authoritative
/// name, recipe, enabled flag, parent index and actual mounted identity.
#[derive(Clone, Default)]
struct ConfigNodes {
    by_path: BTreeMap<String, usize>,
    checked: cordis_kernel::configuration_tree::Tree<Node>,
}
impl ConfigNodes {
    fn get(&self, path: &str) -> Option<&CheckedNode> {
        self.checked.get(*self.by_path.get(path)?, path)
    }
    fn contains_key(&self, path: &str) -> bool {
        self.get(path).is_some()
    }
    fn len(&self) -> usize {
        self.checked.nodes().len()
    }
    fn values(&self) -> impl Iterator<Item = &CheckedNode> {
        self.checked.nodes().iter()
    }
    fn iter(&self) -> impl Iterator<Item = (&String, &CheckedNode)> {
        self.values().map(|node| (node.key(), node))
    }
    fn order(&self) -> Vec<String> {
        self.checked.keys()
    }
    fn from_checked(checked: cordis_kernel::configuration_tree::Tree<Node>) -> Self {
        let by_path = checked
            .keys()
            .into_iter()
            .enumerate()
            .map(|(index, path)| (path, index))
            .collect();
        Self { by_path, checked }
    }
    fn reconstruct(
        &mut self,
        runtime: &mut Runtime,
        plugins: &mut BTreeMap<String, Plugin>,
        created: Option<&mut Vec<PluginId>>,
    ) -> Result<(), LoaderError> {
        let mut host = (runtime, plugins, created);
        let result = self
            .checked
            .reconstruct(&mut host, |host, node, parent| {
                let (runtime, plugins, created) = host;
                // Re-read the actual owner: a saved allocation is historical evidence,
                // not a promise that it remains live or still has the required parent.
                if let Some(allocation) = node
                    .id()
                    .and_then(|id| runtime.configuration_allocation(id))
                {
                    if allocation.parent() == parent {
                        return Ok(allocation);
                    }
                }
                let plugin = match plugins.remove(node.key()) {
                    Some(plugin) => plugin,
                    None => node.build()?,
                };
                let allocation =
                    runtime.mount_configuration(node.scope.context(), parent, plugin)?;
                if let Some(created) = created {
                    created.push(allocation.id());
                }
                Ok::<_, LoaderError>(allocation)
            })
            .result;
        result.map_err(|error| {
            let path = self.checked.nodes()[error.index].key();
            match error.error {
                cordis_kernel::configuration_tree::MountError::Callback(error) => error,
                cordis_kernel::configuration_tree::MountError::Mismatch(_) => ConfigError::new(
                    path,
                    "mount returned an invalid domain, parent, or duplicate identity",
                )
                .into(),
                cordis_kernel::configuration_tree::MountError::Tree(error) => {
                    ConfigError::new(path, format!("configuration tree: {error:?}")).into()
                }
            }
        })
    }
}
impl std::ops::Index<&String> for ConfigNodes {
    type Output = CheckedNode;
    fn index(&self, path: &String) -> &Self::Output {
        self.get(path).expect("planned configuration entry")
    }
}
#[derive(Clone, Default)]
struct Snapshot {
    tree: ConfigTree,
    nodes: ConfigNodes,
}

/// Loaded text and logical merge checkpoints share one checked owner. Save
/// reports remain diagnostics; only the actual save cursor can advance a base.
pub(crate) type SourceTracking =
    cordis_kernel::configuration_save::sources::Source<PathBuf, ConfigTree>;

fn source_checkpoints(source: &SourceTracking) -> BTreeMap<PathBuf, ConfigTree> {
    source
        .checkpoints()
        .iter()
        .map(|(path, checkpoint)| (path.clone(), checkpoint.value.clone()))
        .collect()
}
fn source_pending_sync(source: &SourceTracking) -> BTreeSet<PathBuf> {
    source
        .checkpoints()
        .iter()
        .filter(|(_, checkpoint)| checkpoint.pending_sync)
        .map(|(path, _)| path.clone())
        .collect()
}

struct UpdateKey {
    path: String,
    target: cordis_kernel::configuration_runtime::Target,
}
type ConfigurationState = cordis_kernel::configuration_recorded::Recorded<
    Snapshot,
    Transaction,
    UpdateKey,
    ConfigUpdatePlan,
    PathBuf,
    ConfigTree,
>;

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
    /// Config-only changes accepted without replacing the active instance.
    pub updated: Vec<String>,
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
    configuration: ConfigurationState,
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
        let configuration = runtime.configuration(Snapshot::default());
        Self {
            runtime,
            root,
            parent,
            registry,
            configuration,
        }
    }
    pub fn runtime(&self) -> &Runtime {
        &self.runtime
    }
    /// Mutate the retained runtime through its operations. The view cannot
    /// replace the runtime that owns this Loader's configuration Journal.
    pub fn runtime_mut(&mut self) -> crate::RuntimeAccess<'_> {
        crate::RuntimeAccess::new(&mut self.runtime)
    }
    /// Capture native lifecycle, accepted/pending configuration and source
    /// checkpoints in one Journal read. Typed proof history is erased; this is
    /// not a serialized audit log or a proof of arbitrary plugin callbacks.
    pub fn execution_snapshot(&self) -> cordis_kernel::reversible_value::joint::Snapshot {
        self.runtime.configuration_snapshot(&self.configuration)
    }
    pub fn registry(&self) -> &FactoryRegistry {
        &self.registry
    }
    pub fn registry_mut(&mut self) -> &mut FactoryRegistry {
        &mut self.registry
    }
    /// Last successfully committed configuration, including expanded includes.
    pub fn tree(&self) -> &ConfigTree {
        &self.configuration.current().tree
    }
    pub fn id(&self, path: &str) -> Option<PluginId> {
        let id = self.configuration.current().nodes.get(path)?.id()?;
        self.runtime.contains(id).then_some(id)
    }
    pub fn scope(&self, path: &str) -> Option<&ConfigScope> {
        self.configuration
            .current()
            .nodes
            .get(path)
            .map(|node| &node.scope)
    }
    pub fn revision(&self) -> u64 {
        self.configuration.revision()
    }
    pub fn recovery_pending(&self) -> bool {
        self.configuration.pending().is_some()
    }
    pub fn watched_files(&self) -> impl Iterator<Item = &Path> {
        self.configuration
            .sources()
            .contents()
            .keys()
            .map(PathBuf::as_path)
    }

    fn prepare(
        &self,
        tree: ConfigTree,
        restart: &BTreeSet<String>,
    ) -> Result<Snapshot, LoaderError> {
        struct Parent {
            scope: ConfigScope,
            inject: BTreeMap<String, Value>,
            retained: bool,
        }
        let entries = tree
            .entries
            .clone()
            .into_iter()
            .map(Entry::into_planning)
            .collect();
        let planned = planning::plan(
            entries,
            Parent {
                scope: self.root.clone(),
                inject: BTreeMap::new(),
                retained: true,
            },
            self.runtime.configuration_domain(),
            self.parent,
            (self, restart),
            |host, entry, declaration, parent| {
                let (loader, restart) = host;
                let path = declaration.key().clone();
                if entry.include.is_some() {
                    return Err(ConfigError::new(
                        &path,
                        "includes require load_file(), not apply() or load_json()",
                    )
                    .into());
                }
                let mut scope = parent.scope.extend_json(&entry.metadata);
                for (name, patch) in &entry.intercept {
                    scope = scope.intercept(name, patch.clone());
                }
                let mut inject = parent.inject.clone();
                inject.extend(
                    entry
                        .inject
                        .iter()
                        .map(|(name, config)| (name.clone(), config.clone())),
                );
                scope = scope.with_injections(&inject);
                let service =
                    |name: &str| {
                        loader.registry.services.get(name).cloned().ok_or_else(|| {
                            ConfigError::new(&path, format!("unknown service: {name}"))
                        })
                    };
                let services = inject
                    .iter()
                    .map(|(name, config)| service(name).map(|service| (service, config.clone())))
                    .collect::<Result<Vec<_>, _>>()?;
                let isolates = entry
                    .isolate
                    .iter()
                    .map(|name| service(name))
                    .collect::<Result<Vec<_>, _>>()?;
                let factory = match &entry.name {
                    Some(name) => Some(loader.registry.factories.get(name).cloned().ok_or_else(
                        || ConfigError::new(&path, format!("unknown plugin factory: {name}")),
                    )?),
                    None => None,
                };
                let mut normalized = entry.clone();
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
                        .map(|((name, _), (service, _))| (name.clone(), service.revision))
                        .collect(),
                    isolate: entry
                        .isolate
                        .iter()
                        .zip(&isolates)
                        .map(|(name, service)| (name.clone(), service.revision))
                        .collect(),
                    factory: factory.as_ref().map(|factory| factory.revision),
                    enabled: declaration.enabled(),
                };
                let retained = parent.retained
                    && loader
                        .configuration
                        .current()
                        .nodes
                        .get(&path)
                        .is_some_and(|old| {
                            (old.signature == signature
                                || (!restart.contains(&path)
                                    && signature.only_config_changed(&old.signature)
                                    && old.id().is_some_and(|id| {
                                        loader.runtime.phase(id) == Some(Phase::Active)
                                    })))
                                && match old.id() {
                                    Some(id) => {
                                        loader.runtime.contains(id) && !loader.runtime.retired(id)
                                    }
                                    None => !signature.enabled,
                                }
                        });
                let allocation = if retained {
                    let old = &loader.configuration.current().nodes[&path];
                    scope = old.scope.clone();
                    old.allocation()
                } else {
                    for service in isolates {
                        scope = scope.with_context((service.isolate)(scope.context()));
                    }
                    None
                };

                Ok::<_, LoaderError>(planning::Prepared {
                    data: Node {
                        path,
                        scope: scope.clone(),
                        signature,
                        factory,
                        inject: services,
                    },
                    context: Parent {
                        scope,
                        inject,
                        retained,
                    },
                    allocation,
                })
            },
        );
        let checked = planned.result.map_err(|error| match error {
            planning::PlanError::Callback { error, .. } => error,
            planning::PlanError::Input(error) => ConfigError::new(
                "$",
                match error {
                    planning::InputError::Depth => "configuration nesting exceeds 128",
                    planning::InputError::Capacity => "configuration contains too many entries",
                },
            )
            .into(),
            planning::PlanError::Tree { index, cause } => {
                let message = match cause {
                    cordis_kernel::configuration_tree::TreeError::InvalidId
                    | cordis_kernel::configuration_tree::TreeError::Duplicate => {
                        "entry IDs must be unique, nonempty, and contain neither / nor :".to_owned()
                    }
                    error => format!("configuration tree: {error:?}"),
                };
                ConfigError::new(format!("$[entry {index}]"), message).into()
            }
        })?;
        Ok(Snapshot {
            tree,
            nodes: ConfigNodes::from_checked(checked),
        })
    }

    pub async fn load_json(&mut self, json: &str) -> Result<ApplyReport, LoaderError> {
        self.recover().await?;
        let report = self.apply_transaction(ConfigTree::from_json(json)?).await?;
        self.configuration
            .clear_sources()
            .map_err(LoaderError::Transaction)?;
        self.settle_committed(report).await
    }
    pub async fn apply(&mut self, tree: ConfigTree) -> Result<ApplyReport, LoaderError> {
        let report = self.apply_transaction(tree).await?;
        self.settle_committed(report).await
    }
    async fn settle_committed(
        &mut self,
        mut report: ApplyReport,
    ) -> Result<ApplyReport, LoaderError> {
        self.runtime
            .settle()
            .await
            .map_err(|error| LoaderError::PostCommit {
                revision: self.configuration.revision(),
                cause: Box::new(error.into()),
            })?;
        // New service availability can restart consumers and retire their owned
        // config children. Reinstall missing entries from the accepted tree.
        if self.configuration.current().nodes.values().any(|node| {
            node.signature.enabled
                && node
                    .id()
                    .is_none_or(|id| !self.runtime.contains(id) || self.runtime.retired(id))
        }) {
            let repaired = self
                .apply_transaction(self.configuration.current().tree.clone())
                .await
                .map_err(|cause| LoaderError::PostCommit {
                    revision: self.configuration.revision(),
                    cause: Box::new(cause),
                })?;
            report.revision = repaired.revision;
            for path in repaired.changed {
                if !report.changed.contains(&path) {
                    report.changed.push(path);
                }
            }
            report.retained = self.configuration.current().nodes.len() - report.changed.len();
        }
        Ok(report)
    }
    async fn apply_transaction(&mut self, tree: ConfigTree) -> Result<ApplyReport, LoaderError> {
        self.recover().await?;
        let mut settled = false;
        let mut restart = BTreeSet::new();
        let (mut plan, mut report) = loop {
            let plan = self.prepare(tree.clone(), &restart)?;
            let mut report = ApplyReport {
                revision: self.configuration.revision(),
                ..ApplyReport::default()
            };
            for path in &plan.nodes.order() {
                let node = &plan.nodes[path];
                let unchanged = self
                    .configuration
                    .current()
                    .nodes
                    .get(path)
                    .is_some_and(|old| {
                        node.signature == old.signature
                            && node.id() == old.id()
                            && (!node.signature.enabled || node.id().is_some())
                    });
                if unchanged {
                    report.retained += 1;
                } else {
                    report.changed.push(path.clone());
                }
            }
            report.removed = self
                .configuration
                .current()
                .nodes
                .order()
                .iter()
                .filter(|path| !plan.nodes.contains_key(path))
                .cloned()
                .collect();
            if !report.is_unchanged() {
                break (plan, report);
            }
            if settled {
                let mut refreshed = self.configuration.current().clone();
                refreshed.tree = plan.tree;
                let _previous = self
                    .configuration
                    .refresh(refreshed)
                    .ok()
                    .expect("recovery completed before planning");
                return Ok(report);
            }
            // An explicit runtime.restart() can retire owned config children even
            // when the configuration itself is unchanged. Reconcile after driving it.
            self.runtime.settle().await?;
            settled = true;
        };
        self.configuration
            .check_begin()
            .map_err(LoaderError::Transaction)?;
        // A config update retains its episode only when structural changes cannot
        // restart it through ownership or the transitive committed dependency graph.
        let (plugins, updates) = loop {
            let mut affected = self
                .configuration
                .current()
                .nodes
                .checked
                .retirements(&plan.nodes.checked)
                .map_err(|error| {
                    ConfigError::new("$", format!("configuration selection: {error:?}"))
                })?
                .iter()
                .map(|entry| entry.allocation().id())
                .collect::<BTreeSet<_>>();
            let runtime_snapshot = self.runtime.snapshot();
            loop {
                let before = affected.len();
                // Include programmatically mounted children and dynamic service
                // providers, not just nodes directly represented in the config.
                for node in &runtime_snapshot.plugins {
                    if node.parent.is_some_and(|parent| affected.contains(&parent))
                        || node
                            .committed
                            .iter()
                            .any(|binding| affected.contains(&binding.provider))
                    {
                        affected.insert(node.id);
                    }
                }
                if affected.len() == before {
                    break;
                }
            }
            let candidates = plan
                .nodes
                .order()
                .iter()
                .filter(|path| {
                    let node = &plan.nodes[*path];
                    node.id().is_some()
                        && self
                            .configuration
                            .current()
                            .nodes
                            .get(path)
                            .is_some_and(|old| node.signature.only_config_changed(&old.signature))
                })
                .cloned()
                .collect::<Vec<_>>();
            let mut replan = false;
            for path in &candidates {
                let id = plan.nodes[path].id().unwrap();
                let prefix = format!("{path}/");
                let child_affected =
                    self.configuration
                        .current()
                        .nodes
                        .iter()
                        .any(|(child, node)| {
                            child.starts_with(&prefix)
                                && node.id().is_some_and(|id| affected.contains(&id))
                        });
                if affected.contains(&id) || child_affected {
                    restart.insert(path.clone());
                    replan = true;
                }
            }
            if replan {
                plan = self.prepare(tree.clone(), &restart)?;
                continue;
            }
            // All candidate and standby factories are checked before user update
            // planning or resource retirement. Planning itself must be side-effect free.
            let mut plugins = BTreeMap::new();
            for path in &plan.nodes.order() {
                let node = &plan.nodes[path];
                if node.signature.enabled {
                    plugins.insert(path.clone(), node.build()?);
                }
            }
            let mut updates = Vec::new();
            for path in candidates {
                let node = &plan.nodes[&path];
                let id = node.id().unwrap();
                if !self.runtime.config_recipe_compatible(id, &plugins[&path]) {
                    restart.insert(path);
                    replan = true;
                    break;
                }
                let target = self
                    .runtime
                    .configuration_target(id)
                    .ok_or(RuntimeError::InactiveOwner(id))?;
                let previous = self.configuration.current().nodes[&path]
                    .signature
                    .entry
                    .config
                    .clone();
                match self.runtime.prepare_config_update(
                    id,
                    previous,
                    node.signature.entry.config.clone(),
                )? {
                    ConfigUpdate::Restart => {
                        restart.insert(path);
                        replan = true;
                        break;
                    }
                    ConfigUpdate::Apply(update) => {
                        updates.push(cordis_kernel::configuration_batch::Action::new(
                            UpdateKey { path, target },
                            update,
                        ))
                    }
                }
            }
            if replan {
                plan = self.prepare(tree.clone(), &restart)?;
                continue;
            }
            break (plugins, updates);
        };
        let recovery = Transaction {
            before: self.configuration.current().clone(),
            created: Vec::new(),
        };
        self.configuration
            .begin_structural(plan, recovery, updates)
            .map_err(|rejected| LoaderError::Transaction(rejected.error))?;
        let result =
            Self::apply_prepared(&mut self.runtime, &mut self.configuration, plugins).await;
        match result {
            Ok(()) => {
                let plan = &self.configuration.pending().unwrap().candidate;
                report.changed = plan
                    .nodes
                    .order()
                    .iter()
                    .filter(|path| {
                        let next = &plan.nodes[*path];
                        self.configuration
                            .current()
                            .nodes
                            .get(path)
                            .is_none_or(|old| {
                                old.signature != next.signature || old.id() != next.id()
                            })
                    })
                    .cloned()
                    .collect();
                report.retained = plan.nodes.len() - report.changed.len();
                report.updated = self
                    .configuration
                    .updates()
                    .actions()
                    .iter()
                    .map(|update| update.key().path.clone())
                    .collect();
                if !plan.nodes.checked.ready() {
                    return Err(LoaderError::Transaction(
                        cordis_kernel::configuration_transaction::TransactionError::NotReady,
                    ));
                }
                let _retired = self
                    .configuration
                    .commit()
                    .map_err(LoaderError::Transaction)?;
                report.revision = self.configuration.revision();
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
        runtime: &mut Runtime,
        configuration: &mut ConfigurationState,
        mut plugins: BTreeMap<String, Plugin>,
    ) -> Result<(), LoaderError> {
        loop {
            let done = poll_fn(|cx| configuration.poll_structure(|phase, current, pending| {
                let plan = &mut pending.candidate;
                let transaction = &mut pending.recovery;
                match phase {
                    Structure::Remove => {
                        current.nodes.checked.retire_into(&plan.nodes.checked, runtime,
                            |runtime, allocation| runtime.dispose(allocation.id()))
                            .result.map_err(|error| match error {
                                cordis_kernel::configuration_tree::selection::RetireError::Tree(error) =>
                                    LoaderError::from(ConfigError::new("$", format!("configuration selection: {error:?}"))),
                                cordis_kernel::configuration_tree::selection::RetireError::Callback {error, ..} => error.into(),
                            })?;
                        Poll::Ready(Ok(()))
                    }
                    Structure::SettleRemoved => Pin::new(&mut runtime.settle()).poll(cx).map_err(LoaderError::from),
                    Structure::Mount => {
                        plan.nodes.reconstruct(runtime, &mut plugins, Some(&mut transaction.created))?;
                        Poll::Ready(Ok(()))
                    }
                    Structure::SettleMounted => match Pin::new(&mut runtime.settle()).poll(cx) {
                        Poll::Ready(Ok(())) if !plan.nodes.checked.ready() => Poll::Ready(Err(LoaderError::Transaction(
                            cordis_kernel::configuration_transaction::TransactionError::NotReady))),
                        result => result.map_err(LoaderError::from),
                    },
                    _ => Poll::Ready(Err(LoaderError::Transaction(
                        cordis_kernel::configuration_transaction::TransactionError::NotReady))),
                }
            })).await.map_err(structure_error)?;
            if done {
                break;
            }
        }
        loop {
            let done = poll_fn(|cx| {
                configuration.poll_update(|key, plan| {
                    if !runtime.configuration_target_is_current(key.target) {
                        return Poll::Ready(Err(LoaderError::Factory {
                            entry: key.path.clone(),
                            message: "configuration update owner changed activation or recipe"
                                .into(),
                        }));
                    }
                    plan.poll_apply(cx).map(|result| {
                        result.map_err(|error| LoaderError::Update {
                            entry: key.path.clone(),
                            error,
                        })
                    })
                })
            })
            .await
            .map_err(|error| match error {
                cordis_kernel::configuration_batch::StepError::Callback(error) => error,
                cordis_kernel::configuration_batch::StepError::Recovering => {
                    LoaderError::Transaction(
                        cordis_kernel::configuration_transaction::TransactionError::NotReady,
                    )
                }
            })?;
            if done {
                break;
            }
        }
        let adoption: Vec<_> = configuration
            .updates()
            .actions()
            .iter()
            .map(|action| {
                let key = action.key();
                (key.path.clone(), key.target)
            })
            .collect();
        // Adoption is an owned phase after all actual updates. A failed
        // preflight cannot authorize the checked transaction's commit gate.
        poll_fn(|_cx| {
            configuration.poll_structure(|phase, _current, _pending| {
                if phase != Structure::Adopt {
                    return Poll::Ready(Err(LoaderError::Transaction(
                        cordis_kernel::configuration_transaction::TransactionError::NotReady,
                    )));
                }
                let recipes = adoption
                    .iter()
                    .map(|(path, target)| {
                        (
                            *target,
                            plugins
                                .remove(path)
                                .expect("preconstructed retained configuration update recipe"),
                        )
                    })
                    .collect();
                Poll::Ready(
                    runtime
                        .adopt_config_recipes(recipes)
                        .map_err(LoaderError::from),
                )
            })
        })
        .await
        .map_err(structure_error)?;
        Ok(())
    }

    /// Restore interrupted/failed revisions using captured old factories. Newly
    /// restored IDs are recorded before awaiting, so recovery can also be dropped.
    pub async fn recover(&mut self) -> Result<(), LoaderError> {
        if self.configuration.pending().is_none() {
            return Ok(());
        }
        loop {
            let done = poll_fn(|cx| {
                self.configuration.poll_rollback(|key, plan| {
                    plan.poll_rollback(cx).map(|result| {
                        result.map_err(|error| LoaderError::Update {
                            entry: key.path.clone(),
                            error,
                        })
                    })
                })
            })
            .await?;
            if done {
                break;
            }
        }
        let runtime = &mut self.runtime;
        loop {
            let done = poll_fn(|cx| self.configuration.poll_structure(|phase, _current, pending| {
                let transaction = &mut pending.recovery;
                match phase {
                    Structure::RecoverRemove => {
                        for id in &transaction.created { runtime.dispose(*id)?; }
                        for node in transaction.before.nodes.values() {
                            if let Some(id) = node.id() {
                                if runtime.failure(id).is_some() { runtime.dispose(id)?; }
                            }
                        }
                        Poll::Ready(Ok(()))
                    }
                    Structure::RecoverSettleRemoved => Pin::new(&mut runtime.settle()).poll(cx).map_err(LoaderError::from),
                    Structure::RecoverMount => {
                        transaction.before.nodes.reconstruct(runtime, &mut BTreeMap::new(), None)?;
                        Poll::Ready(Ok(()))
                    }
                    Structure::RecoverSettleMounted => match Pin::new(&mut runtime.settle()).poll(cx) {
                        Poll::Ready(Ok(())) if !transaction.before.nodes.checked.ready() => Poll::Ready(Err(LoaderError::Transaction(
                            cordis_kernel::configuration_transaction::TransactionError::NotReady))),
                        result => result.map_err(LoaderError::from),
                    },
                    _ => Poll::Ready(Err(LoaderError::Transaction(
                        cordis_kernel::configuration_transaction::TransactionError::NotReady))),
                }
            })).await.map_err(structure_error)?;
            if done {
                break;
            }
        }
        let _retired = self
            .configuration
            .recover_with(|transaction| std::mem::take(&mut transaction.before))
            .map_err(LoaderError::Transaction)?;
        Ok(())
    }
    pub async fn reload(&mut self) -> Result<ApplyReport, LoaderError> {
        self.recover().await?;
        self.apply(self.configuration.current().tree.clone()).await
    }
    pub async fn set_enabled(
        &mut self,
        path: &str,
        enabled: bool,
    ) -> Result<ApplyReport, LoaderError> {
        self.recover().await?;
        let mut tree = self.configuration.current().tree.clone();
        tree.entry_mut(path)
            .ok_or_else(|| ConfigError::new(path, "unknown entry"))?
            .enabled = enabled;
        self.apply(tree).await
    }
    pub async fn dispose(&mut self) -> Result<ApplyReport, LoaderError> {
        let report = self.apply_transaction(ConfigTree::default()).await?;
        self.configuration
            .clear_sources()
            .map_err(LoaderError::Transaction)?;
        self.settle_committed(report).await
    }
    pub async fn load_file(&mut self, path: impl AsRef<Path>) -> Result<ApplyReport, LoaderError> {
        self.recover().await?;
        let loaded = read_tree(path.as_ref())?;
        let report = self.apply_transaction(loaded.tree).await?;
        self.configuration
            .load_sources(cordis_kernel::configuration_recorded::Load {
                root: loaded.root,
                contents: loaded.sources,
                checkpoints: loaded.checkpoints.into_iter().collect(),
                resolutions: loaded.resolutions,
            })
            .map_err(|_| {
                LoaderError::Transaction(
                    cordis_kernel::configuration_transaction::TransactionError::Pending,
                )
            })?;
        self.settle_committed(report).await
    }
    /// Prepare an explicit, inspectable three-way save without writing files.
    /// Include boundaries are retained. New children directly beside an include
    /// have ambiguous ownership and must first be added through the source file.
    /// Saving never changes the running configuration; poll_reload applies any
    /// external edits retained by the merge.
    pub fn prepare_save(&self) -> Result<SavePlan, SaveError> {
        let configuration = self
            .configuration
            .save_stamp(self.runtime.configuration_domain())
            .ok_or_else(|| SaveError::new(None, SaveErrorKind::RecoveryPending))?;
        let root = self
            .configuration
            .sources()
            .root()
            .as_ref()
            .ok_or_else(|| SaveError::new(None, SaveErrorKind::NoFileSource))?;
        let (desired, include_targets) = project_sources(
            root,
            self.configuration.sources().contents(),
            self.configuration.sources().resolutions(),
            &self.configuration.current().tree,
        )?;
        let plan = SavePlan::prepare(
            self.configuration.current().tree.clone(),
            self.configuration.sources().contents().clone(),
            source_checkpoints(self.configuration.sources()),
            desired,
            SaveOrigin {
                registry_revision: self.registry.revision,
                configuration,
            },
            source_pending_sync(self.configuration.sources()),
            include_targets,
        )?;
        let merged = read_tree_cached(root, Some(plan.merged_sources())).map_err(|error| {
            SaveError::new(
                None,
                SaveErrorKind::InvalidMergedConfiguration(error.to_string()),
            )
        })?;
        self.prepare(merged.tree, &BTreeSet::new())
            .map_err(|error| {
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
        if self.configuration.pending().is_some() {
            return Err(SaveError::new(None, SaveErrorKind::RecoveryPending));
        }
        if !self.configuration.accepts_save(
            self.runtime.configuration_domain(),
            &plan.origin.configuration,
        ) || plan.tree != self.configuration.current().tree
            || &plan.sources != self.configuration.sources().contents()
            || plan.checkpoints != source_checkpoints(self.configuration.sources())
            || plan.origin.registry_revision != self.registry.revision
            || plan.pending_sync != source_pending_sync(self.configuration.sources())
        {
            return Err(SaveError::new(None, SaveErrorKind::StalePlan));
        }
        plan.commit(&mut self.configuration, self.runtime.configuration_domain())
    }
    /// Explicit convenience operation; apply and set_enabled never write files.
    pub fn save(&mut self) -> Result<SaveReport, SaveError> {
        let plan = self.prepare_save()?;
        self.commit_save(plan)
    }
    /// Poll contents and factory revisions once from an application's timer/event
    /// loop. Invalid files leave the previous successful source snapshot intact.
    pub async fn poll_reload(&mut self) -> Result<ApplyReport, LoaderError> {
        let Some(path) = self.configuration.sources().root().clone() else {
            return self.reload().await;
        };
        self.load_file(path).await
    }
}

struct LoadedTree {
    tree: ConfigTree,
    root: PathBuf,
    sources: BTreeMap<PathBuf, String>,
    checkpoints: BTreeMap<PathBuf, ConfigTree>,
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
    struct Reader {
        sources: BTreeMap<PathBuf, String>,
        checkpoints: BTreeMap<PathBuf, ConfigTree>,
        cached_only: bool,
        resolutions: BTreeMap<PathBuf, PathBuf>,
        locations: BTreeMap<Vec<u8>, PathBuf>,
    }
    impl Reader {
        fn read(&mut self, path: &Path) -> Result<ExpansionDocument, LoaderError> {
            let lexical = path.to_owned();
            let path = fs::canonicalize(path).map_err(|error| source_error(path, error))?;
            if self
                .resolutions
                .insert(lexical, path.clone())
                .is_some_and(|previous| previous != path)
            {
                return Err(source_error(&path, "include target changed while reading"));
            }
            // Preserve native path bytes: lossy Unicode conversion must not
            // merge two file identities during cycle detection.
            let identity = path.as_os_str().as_encoded_bytes().to_vec();
            self.locations.insert(identity.clone(), path.clone());
            let text = match self.sources.get(&path) {
                Some(text) => text.clone(),
                None if self.cached_only => {
                    return Err(source_error(
                        &path,
                        "include source was not part of the save plan",
                    ))
                }
                None => fs::read_to_string(&path).map_err(|error| source_error(&path, error))?,
            };
            let tree = ConfigTree::from_json(&text).map_err(|error| source_error(&path, error))?;
            self.checkpoints.insert(path.clone(), tree.clone());
            self.sources.insert(path.clone(), text);
            Ok(ExpansionDocument {
                identity,
                base: path.parent().unwrap_or(Path::new(".")).to_owned(),
                entries: tree
                    .entries
                    .into_iter()
                    .map(Entry::into_expansion)
                    .collect(),
            })
        }
        fn location(&self, identity: &[u8]) -> &Path {
            self.locations
                .get(identity)
                .expect("expansion identities originate from actual document reads")
        }
    }
    let root = fs::canonicalize(path).map_err(|error| source_error(path, error))?;
    let mut reader = Reader {
        cached_only: cached.is_some(),
        sources: cached.unwrap_or_default(),
        checkpoints: BTreeMap::new(),
        resolutions: BTreeMap::new(),
        locations: BTreeMap::new(),
    };
    let document = reader.read(&root)?;
    let mut expander = cordis_kernel::configuration_expansion::Expander::new(
        reader,
        |reader: &mut Reader, base: &PathBuf, include: &PathBuf| reader.read(&base.join(include)),
    );
    let result = expander.expand(document).result;
    let reader = expander.into_host();
    let entries = result.map_err(|error| {
        use cordis_kernel::configuration_expansion::ExpandError;
        match error {
            ExpandError::Read(error) => error,
            ExpandError::Cycle(cycle) => LoaderError::IncludeCycle(
                cycle
                    .iter()
                    .map(|key| reader.location(key).to_owned())
                    .collect(),
            ),
            ExpandError::IncludeDepth(key) => {
                source_error(reader.location(&key), "include nesting exceeds 128")
            }
            ExpandError::TreeDepth(key) => {
                source_error(reader.location(&key), "configuration nesting exceeds 128")
            }
        }
    })?;
    Ok(LoadedTree {
        tree: ConfigTree {
            entries: entries.into_iter().map(Entry::from_expansion).collect(),
        },
        root,
        sources: reader.sources,
        checkpoints: reader.checkpoints,
        resolutions: reader.resolutions,
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
