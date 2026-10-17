//! Schema checking and immutable, typed context extension for Rust plugins.
//!
//! Structural schemas, defaults and recursive overlays execute in the verified
//! kernel. Serde conversion, typed metadata and external callbacks are adapters.

use crate::future_support::poll_catching_unwind;
use crate::Context;
use serde_json::{Map, Value};
use std::any::{Any, TypeId};
use std::collections::{BTreeMap, HashMap};
use std::fmt;
use std::future::Future;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::pin::Pin;
use std::sync::Arc;
use std::task::{Context as TaskContext, Poll};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConfigError {
    pub path: String,
    pub message: String,
}

impl ConfigError {
    pub fn new(path: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            path: path.into(),
            message: message.into(),
        }
    }
}
impl fmt::Display for ConfigError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.path, self.message)
    }
}
impl std::error::Error for ConfigError {}

/// A deliberately explicit schema: objects reject unknown fields by default.
#[derive(Clone, Debug)]
pub enum Schema {
    Any,
    Boolean,
    String,
    Integer {
        min: Option<i64>,
        max: Option<i64>,
    },
    Number {
        min: Option<f64>,
        max: Option<f64>,
    },
    Enum(Vec<Value>),
    Array(Box<Schema>),
    Object {
        fields: BTreeMap<String, Field>,
        allow_unknown: bool,
    },
    Nullable(Box<Schema>),
}

#[derive(Clone, Debug)]
pub struct Field {
    pub schema: Schema,
    pub required: bool,
    pub default: Option<Value>,
}

impl Field {
    pub fn required(schema: Schema) -> Self {
        Self {
            schema,
            required: true,
            default: None,
        }
    }
    pub fn optional(schema: Schema) -> Self {
        Self {
            schema,
            required: false,
            default: None,
        }
    }
    pub fn defaulted(schema: Schema, value: impl Into<Value>) -> Self {
        Self {
            schema,
            required: false,
            default: Some(value.into()),
        }
    }
}

impl Schema {
    pub fn object(fields: impl IntoIterator<Item = (impl Into<String>, Field)>) -> Self {
        Self::Object {
            fields: fields
                .into_iter()
                .map(|(key, field)| (key.into(), field))
                .collect(),
            allow_unknown: false,
        }
    }
    pub fn integer(min: i64, max: i64) -> Self {
        Self::Integer {
            min: Some(min),
            max: Some(max),
        }
    }
    /// Return a validated copy with defaults inserted; never mutate the input.
    pub fn validate(&self, value: &Value) -> Result<Value, ConfigError> {
        self.validate_at(value, "$")
    }
    fn validate_at(&self, value: &Value, path: &str) -> Result<Value, ConfigError> {
        self.compile().validate_at(value, path)
    }
    pub(crate) fn compile(&self) -> CompiledSchema {
        use cordis_kernel::configuration_schema as checked;
        fn lower(schema: &Schema) -> checked::Schema {
            match schema {
                Schema::Any => checked::Schema::Any,
                Schema::Boolean => checked::Schema::Boolean,
                Schema::String => checked::Schema::String,
                Schema::Integer { min, max } => checked::Schema::Integer {
                    min: *min,
                    max: *max,
                },
                Schema::Number { min, max } => checked::Schema::Number {
                    low: min
                        .filter(|n| !n.is_nan())
                        .map(crate::config_data::number_rank),
                    high: max
                        .filter(|n| !n.is_nan())
                        .map(crate::config_data::number_rank),
                },
                Schema::Enum(values) => {
                    checked::Schema::Enum(values.iter().map(crate::config_data::encode).collect())
                }
                Schema::Array(inner) => checked::Schema::Array(Box::new(lower(inner))),
                Schema::Nullable(inner) => checked::Schema::Nullable(Box::new(lower(inner))),
                Schema::Object {
                    fields,
                    allow_unknown,
                } => checked::Schema::Object {
                    fields: fields
                        .iter()
                        .map(|(name, field)| checked::Field {
                            name: name.clone(),
                            schema: lower(&field.schema),
                            required: field.required,
                            default: field.default.as_ref().map(crate::config_data::encode),
                        })
                        .collect(),
                    allow_unknown: *allow_unknown,
                },
            }
        }
        CompiledSchema(Arc::new(lower(self)))
    }
}

#[derive(Clone)]
pub(crate) struct CompiledSchema(Arc<cordis_kernel::configuration_schema::Schema>);
impl CompiledSchema {
    pub(crate) fn checked(&self) -> Arc<cordis_kernel::configuration_schema::Schema> {
        self.0.clone()
    }
    fn validate_at(&self, value: &Value, path: &str) -> Result<Value, ConfigError> {
        self.0
            .validate(&crate::config_data::encode(value))
            .map(crate::config_data::decode)
            .map_err(|failure| ConfigError::schema(failure, path))
    }
}

impl ConfigError {
    pub(crate) fn schema(
        failure: cordis_kernel::configuration_schema::Failure,
        path: &str,
    ) -> Self {
        use cordis_kernel::configuration_schema::{Part, Reason};
        let mut path = path.to_owned();
        for part in failure.path {
            match part {
                Part::Field(name) => {
                    path.push('.');
                    path.push_str(&name);
                }
                Part::Index(index) => path.push_str(&format!("[{index}]")),
            }
        }
        ConfigError::new(
            path,
            match failure.reason {
                Reason::Boolean => "expected boolean",
                Reason::String => "expected string",
                Reason::Integer => "expected signed 64-bit integer",
                Reason::Number => "expected number",
                Reason::Range => "number is outside the permitted range",
                Reason::Enum => "value is not an allowed enum member",
                Reason::Array => "expected array",
                Reason::Object => "expected object",
                Reason::Unknown => "unknown field",
                Reason::Required => "required field is missing",
            },
        )
    }
}

/// Object fields merge recursively. Arrays, scalars and null replace a value.
/// Null is a value, not an implicit delete operation.
pub fn merge(base: &Value, patch: &Value) -> Value {
    crate::config_data::overlay(base, patch)
}

/// Rust's equivalent of context extension and scoped configuration interception.
/// Clones inherit Arc metadata; overriding a type affects only the derived scope.
#[derive(Clone)]
pub struct ConfigScope {
    context: Context,
    typed: HashMap<TypeId, Arc<dyn Any + Send + Sync>>,
    metadata: cordis_kernel::configuration_binding::Modules<Value>,
    interceptors: cordis_kernel::configuration_binding::Modules<Value>,
    injections: cordis_kernel::configuration_binding::Modules<Value>,
}

impl ConfigScope {
    pub fn new(context: Context) -> Self {
        Self {
            context,
            typed: HashMap::new(),
            metadata: cordis_kernel::configuration_binding::Modules::new(),
            interceptors: cordis_kernel::configuration_binding::Modules::new(),
            injections: cordis_kernel::configuration_binding::Modules::new(),
        }
    }
    pub fn context(&self) -> &Context {
        &self.context
    }
    pub fn with_context(&self, context: Context) -> Self {
        let mut next = self.clone();
        next.context = context;
        next
    }
    pub fn extend<T: Any + Send + Sync>(&self, value: T) -> Self {
        let mut next = self.clone();
        next.typed.insert(TypeId::of::<T>(), Arc::new(value));
        next
    }
    pub fn metadata<T: Any + Send + Sync>(&self) -> Option<Arc<T>> {
        self.typed.get(&TypeId::of::<T>())?.clone().downcast().ok()
    }
    pub fn extend_json(&self, metadata: &Map<String, Value>) -> Self {
        let mut next = self.clone();
        next.metadata.extend(
            metadata
                .iter()
                .map(|(key, value)| (key.clone(), Arc::new(value.clone())))
                .collect(),
        );
        next
    }
    pub fn json_metadata(&self, name: &str) -> Option<&Value> {
        self.metadata.get(name).map(Arc::as_ref)
    }
    /// Child interception overrides inherited interception field by field.
    /// The resulting patch overrides the plugin's supplied config, before schema validation.
    pub fn intercept(&self, plugin: impl Into<String>, patch: Value) -> Self {
        let mut next = self.clone();
        let name = plugin.into();
        let patch = next
            .interceptors
            .get(&name)
            .map_or_else(|| patch.clone(), |old| merge(old, &patch));
        next.interceptors.insert(name, Arc::new(patch));
        next
    }
    /// Configuration attached to this consumer's required service declaration.
    pub fn injection(&self, service: &str) -> Option<&Value> {
        self.injections.get(service).map(Arc::as_ref)
    }
    pub(crate) fn with_injections(&self, injections: &BTreeMap<String, Value>) -> Self {
        let mut next = self.clone();
        next.injections.extend(
            injections
                .iter()
                .map(|(name, value)| (name.clone(), Arc::new(value.clone())))
                .collect(),
        );
        next
    }
    pub(crate) fn injections(&self) -> BTreeMap<String, Value> {
        self.injections
            .names()
            .iter()
            .map(|name| {
                (
                    name.clone(),
                    self.injection(name).expect("checked scope key").clone(),
                )
            })
            .collect()
    }
    pub(crate) fn interception(&self, plugin: &str) -> Option<&Value> {
        self.interceptors.get(plugin).map(Arc::as_ref)
    }
    pub fn resolve(&self, plugin: &str, config: &Value) -> Value {
        self.interceptors
            .get(plugin)
            .map_or_else(|| config.clone(), |patch| merge(config, patch))
    }
}

impl Default for ConfigScope {
    fn default() -> Self {
        Self::new(Context::new())
    }
}
impl fmt::Debug for ConfigScope {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ConfigScope")
            .field("context", &self.context)
            .field("metadata", &self.metadata)
            .field("interceptors", &self.interceptors)
            .field("injections", &self.injections)
            .field("typed_metadata_count", &self.typed.len())
            .finish()
    }
}

/// An update hook may retain the active instance or request normal replacement.
/// Hook invocation only constructs a plan: it must not mutate external state.
pub enum ConfigUpdate {
    Restart,
    Apply(ConfigUpdatePlan),
}

type UpdateFuture = Pin<Box<dyn Future<Output = crate::CallbackResult> + Send>>;
type UndoFactory = Box<dyn FnMut() -> Result<UpdateFuture, crate::CallbackError> + Send>;

/// A reversible configuration update whose inverse is registered before apply.
///
/// `apply` can be asynchronous. Dropping the loader operation retains its future;
/// recovery first lets that future land, then runs `rollback`. Rollback must undo
/// partial application, including an apply error/panic, and must be safe to retry
/// after a rollback error. These are plugin contracts, not Verus-proved effects.
/// Neither callback runs while constructing this value.
pub struct ConfigUpdatePlan {
    execution: cordis_kernel::configuration_future::Reversible<
        UpdateFuture,
        UndoFactory,
        crate::CallbackError,
    >,
}
impl ConfigUpdatePlan {
    pub fn new(
        apply: impl FnOnce() -> crate::CallbackResult + Send + 'static,
        mut rollback: impl FnMut() -> crate::CallbackResult + Send + 'static,
    ) -> Self {
        Self::new_async(
            move || async move { apply() },
            move || std::future::ready(rollback()),
        )
    }
    pub fn new_async<A, AF, R, RF>(apply: A, mut rollback: R) -> Self
    where
        A: FnOnce() -> AF + Send + 'static,
        AF: Future<Output = crate::CallbackResult> + Send + 'static,
        R: FnMut() -> RF + Send + 'static,
        RF: Future<Output = crate::CallbackResult> + Send + 'static,
    {
        let forward: UpdateFuture = Box::pin(async move { apply().await });
        let inverse: UndoFactory = Box::new(move || {
            catch_unwind(AssertUnwindSafe(|| Box::pin(rollback()) as UpdateFuture)).map_err(|_| {
                crate::CallbackError::panic("configuration rollback construction panicked".into())
            })
        });
        Self {
            execution: cordis_kernel::configuration_future::Reversible::new(forward, inverse),
        }
    }
    pub(crate) fn poll_apply(&mut self, cx: &mut TaskContext<'_>) -> Poll<crate::CallbackResult> {
        self.execution
            .poll_apply(|future| poll_update_future(future, cx, "configuration update panicked"))
            .map(Clone::clone)
    }
    pub(crate) fn poll_rollback(
        &mut self,
        cx: &mut TaskContext<'_>,
    ) -> Poll<crate::CallbackResult> {
        // Both closures need the caller's task context, and the checked owner
        // invokes them sequentially. RefCell supplies a short, exclusive borrow.
        let context = std::cell::RefCell::new(cx);
        self.execution.poll_rollback(
            |future| {
                poll_update_future(
                    future,
                    &mut context.borrow_mut(),
                    "configuration update panicked",
                )
            },
            |future| {
                poll_update_future(
                    future,
                    &mut context.borrow_mut(),
                    "configuration rollback panicked",
                )
            },
        )
    }
}
fn poll_update_future(
    future: &mut UpdateFuture,
    cx: &mut TaskContext<'_>,
    panic_message: &str,
) -> Poll<crate::CallbackResult> {
    match poll_catching_unwind(future.as_mut(), cx) {
        Ok(result) => result,
        Err(_) => Poll::Ready(Err(crate::CallbackError::panic(panic_message.into()))),
    }
}
