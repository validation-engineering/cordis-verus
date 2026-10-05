//! Schema checking and immutable, typed context extension for Rust plugins.
//!
//! These are host-side facilities. Their validators and interceptors are not
//! part of the Verus lifecycle proof.

use crate::future_support::poll_catching_unwind;
use crate::Context;
use serde_json::{Map, Value};
use std::any::{Any, TypeId};
use std::collections::{BTreeMap, HashMap};
use std::fmt;
use std::future::{poll_fn, Future};
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
        let invalid = |message| ConfigError::new(path, message);
        match self {
            Self::Any => {}
            Self::Boolean if !value.is_boolean() => return Err(invalid("expected boolean")),
            Self::String if !value.is_string() => return Err(invalid("expected string")),
            Self::Integer { min, max } => {
                let n = value
                    .as_i64()
                    .ok_or_else(|| invalid("expected signed 64-bit integer"))?;
                if min.is_some_and(|min| n < min) || max.is_some_and(|max| n > max) {
                    return Err(invalid("integer is outside the permitted range"));
                }
            }
            Self::Number { min, max } => {
                let n = value.as_f64().ok_or_else(|| invalid("expected number"))?;
                if min.is_some_and(|min| n < min) || max.is_some_and(|max| n > max) {
                    return Err(invalid("number is outside the permitted range"));
                }
            }
            Self::Enum(values) if !values.contains(value) => {
                return Err(invalid("value is not an allowed enum member"));
            }
            Self::Array(schema) => {
                let values = value.as_array().ok_or_else(|| invalid("expected array"))?;
                return values
                    .iter()
                    .enumerate()
                    .map(|(i, v)| schema.validate_at(v, &format!("{path}[{i}]")))
                    .collect::<Result<Vec<_>, _>>()
                    .map(Value::Array);
            }
            Self::Object {
                fields,
                allow_unknown,
            } => {
                let object = value
                    .as_object()
                    .ok_or_else(|| invalid("expected object"))?;
                if !allow_unknown {
                    if let Some(key) = object.keys().find(|key| !fields.contains_key(*key)) {
                        return Err(ConfigError::new(format!("{path}.{key}"), "unknown field"));
                    }
                }
                let mut result = object.clone();
                for (key, field) in fields {
                    let field_path = format!("{path}.{key}");
                    match object.get(key).or(field.default.as_ref()) {
                        Some(value) => {
                            result
                                .insert(key.clone(), field.schema.validate_at(value, &field_path)?);
                        }
                        None if field.required => {
                            return Err(ConfigError::new(field_path, "required field is missing"));
                        }
                        None => {}
                    }
                }
                return Ok(Value::Object(result));
            }
            Self::Nullable(schema) if !value.is_null() => return schema.validate_at(value, path),
            _ => {}
        }
        Ok(value.clone())
    }
}

/// Object fields merge recursively. Arrays, scalars and null replace a value.
/// Null is a value, not an implicit delete operation.
pub fn merge(base: &Value, patch: &Value) -> Value {
    match (base, patch) {
        (Value::Object(base), Value::Object(patch)) => {
            let mut result = base.clone();
            for (key, value) in patch {
                let next = result
                    .get(key)
                    .map_or_else(|| value.clone(), |old| merge(old, value));
                result.insert(key.clone(), next);
            }
            Value::Object(result)
        }
        _ => patch.clone(),
    }
}

/// Rust's equivalent of context extension and scoped configuration interception.
/// Clones inherit Arc metadata; overriding a type affects only the derived scope.
#[derive(Clone)]
pub struct ConfigScope {
    context: Context,
    typed: HashMap<TypeId, Arc<dyn Any + Send + Sync>>,
    metadata: Map<String, Value>,
    interceptors: BTreeMap<String, Value>,
    injections: BTreeMap<String, Value>,
}

impl ConfigScope {
    pub fn new(context: Context) -> Self {
        Self {
            context,
            typed: HashMap::new(),
            metadata: Map::new(),
            interceptors: BTreeMap::new(),
            injections: BTreeMap::new(),
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
        next.metadata.extend(metadata.clone());
        next
    }
    pub fn json_metadata(&self, name: &str) -> Option<&Value> {
        self.metadata.get(name)
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
        next.interceptors.insert(name, patch);
        next
    }
    /// Configuration attached to this consumer's required service declaration.
    pub fn injection(&self, service: &str) -> Option<&Value> {
        self.injections.get(service)
    }
    pub(crate) fn with_injections(&self, injections: &BTreeMap<String, Value>) -> Self {
        let mut next = self.clone();
        next.injections = injections.clone();
        next
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

type UpdateFuture = Pin<Box<dyn Future<Output = Result<(), String>> + Send>>;
type UndoFactory = Box<dyn FnMut() -> UpdateFuture + Send>;

/// A reversible configuration update whose inverse is registered before apply.
///
/// `apply` can be asynchronous. Dropping the loader operation retains its future;
/// recovery first lets that future land, then runs `rollback`. Rollback must undo
/// partial application, including an apply error/panic, and must be safe to retry
/// after a rollback error. These are plugin contracts, not Verus-proved effects.
/// Neither callback runs while constructing this value.
pub struct ConfigUpdatePlan {
    apply: Option<UpdateFuture>,
    applied: Option<Result<(), String>>,
    started: bool,
    rollback: UndoFactory,
    restoring: Option<UpdateFuture>,
}
impl ConfigUpdatePlan {
    pub fn new(
        apply: impl FnOnce() -> Result<(), String> + Send + 'static,
        mut rollback: impl FnMut() -> Result<(), String> + Send + 'static,
    ) -> Self {
        Self::new_async(
            move || async move { apply() },
            move || std::future::ready(rollback()),
        )
    }
    pub fn new_async<A, AF, R, RF>(apply: A, mut rollback: R) -> Self
    where
        A: FnOnce() -> AF + Send + 'static,
        AF: Future<Output = Result<(), String>> + Send + 'static,
        R: FnMut() -> RF + Send + 'static,
        RF: Future<Output = Result<(), String>> + Send + 'static,
    {
        Self {
            // Constructing the user's future is inside the guarded poll boundary.
            apply: Some(Box::pin(async move { apply().await })),
            applied: None,
            started: false,
            rollback: Box::new(move || Box::pin(rollback())),
            restoring: None,
        }
    }
    fn poll_apply(&mut self, cx: &mut TaskContext<'_>) -> Poll<Result<(), String>> {
        if let Some(result) = &self.applied {
            return Poll::Ready(result.clone());
        }
        self.started = true;
        let result = match poll_catching_unwind(self.apply.as_mut().unwrap().as_mut(), cx) {
            Ok(Poll::Pending) => return Poll::Pending,
            Ok(Poll::Ready(result)) => result,
            Err(_) => Err("configuration update panicked".into()),
        };
        self.apply = None;
        self.applied = Some(result.clone());
        Poll::Ready(result)
    }
    pub(crate) async fn apply(&mut self) -> Result<(), String> {
        poll_fn(|cx| self.poll_apply(cx)).await
    }
    pub(crate) async fn rollback(&mut self) -> Result<(), String> {
        if !self.started {
            return Ok(());
        }
        // A started forward operation must land before its registered inverse.
        let _ = poll_fn(|cx| self.poll_apply(cx)).await;
        if self.restoring.is_none() {
            self.restoring = Some(
                catch_unwind(AssertUnwindSafe(|| (self.rollback)()))
                    .map_err(|_| "configuration rollback construction panicked".to_owned())?,
            );
        }
        let result = poll_fn(|cx| {
            match poll_catching_unwind(self.restoring.as_mut().unwrap().as_mut(), cx) {
                Ok(result) => result,
                Err(_) => Poll::Ready(Err("configuration rollback panicked".into())),
            }
        })
        .await;
        self.restoring = None;
        result
    }
}
