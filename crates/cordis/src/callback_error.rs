//! Errors retain their causes through setup, effect, cleanup and application waits.
use crate::ServiceReadError;
use std::{error::Error, fmt, sync::Arc};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum CallbackErrorKind {
    Message,
    ServiceRead,
    Panic,
    Cancelled,
    External,
    Multiple,
}

/// A cloneable callback failure. Cloning preserves the original error object;
/// formatting is only a presentation boundary, never the runtime's storage format.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallbackError(Arc<ErrorDetail>);

#[derive(Debug)]
struct ErrorDetail {
    kind: CallbackErrorKind,
    message: String,
    source: Option<Arc<dyn Error + Send + Sync>>,
    errors: Vec<CallbackError>,
}
impl CallbackError {
    /// Preserve an application/library error for downcasting via Error::source.
    pub fn new(error: impl Error + Send + Sync + 'static) -> Self {
        Self(Arc::new(ErrorDetail {
            kind: CallbackErrorKind::External,
            message: error.to_string(),
            source: Some(Arc::new(error)),
            errors: Vec::new(),
        }))
    }
    pub fn kind(&self) -> CallbackErrorKind {
        self.0.kind
    }
    pub fn message(&self) -> &str {
        &self.0.message
    }
    pub fn service_read(&self) -> Option<&ServiceReadError> {
        self.0.source.as_ref()?.downcast_ref()
    }
    /// Every constituent of a failed effect join, in receipt order.
    pub fn errors(&self) -> &[CallbackError] {
        &self.0.errors
    }
    pub(crate) fn panic(message: String) -> Self {
        Self(Arc::new(ErrorDetail {
            kind: CallbackErrorKind::Panic,
            message,
            source: None,
            errors: Vec::new(),
        }))
    }
    pub(crate) fn multiple(mut errors: Vec<Self>) -> Self {
        if errors.len() == 1 {
            return errors.pop().unwrap();
        }
        Self(Arc::new(ErrorDetail {
            kind: CallbackErrorKind::Multiple,
            message: errors
                .iter()
                .map(Self::message)
                .collect::<Vec<_>>()
                .join("; "),
            source: None,
            errors,
        }))
    }
    pub(crate) fn is_cancelled(&self) -> bool {
        self.0.kind == CallbackErrorKind::Cancelled
    }
}
impl From<String> for CallbackError {
    fn from(message: String) -> Self {
        let kind = if message == crate::CANCELLED {
            CallbackErrorKind::Cancelled
        } else {
            CallbackErrorKind::Message
        };
        Self(Arc::new(ErrorDetail {
            kind,
            message,
            source: None,
            errors: Vec::new(),
        }))
    }
}
impl From<&str> for CallbackError {
    fn from(message: &str) -> Self {
        message.to_owned().into()
    }
}
impl From<ServiceReadError> for CallbackError {
    fn from(error: ServiceReadError) -> Self {
        Self(Arc::new(ErrorDetail {
            kind: CallbackErrorKind::ServiceRead,
            message: error.to_string(),
            source: Some(Arc::new(error)),
            errors: Vec::new(),
        }))
    }
}
impl fmt::Display for CallbackError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0.message)
    }
}
impl Error for CallbackError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        self.0
            .source
            .as_deref()
            .map(|error| error as _)
            .or_else(|| self.0.errors.first().map(|error| error as _))
    }
}

// Built-in errors have value equality; opaque application causes compare by
// identity. A cloned receipt remains equal without guessing external semantics.
impl PartialEq for ErrorDetail {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
            && self.message == other.message
            && self.errors == other.errors
            && match (&self.source, &other.source) {
                (None, None) => true,
                (Some(a), Some(b)) if self.kind == CallbackErrorKind::ServiceRead => {
                    a.downcast_ref::<ServiceReadError>() == b.downcast_ref::<ServiceReadError>()
                }
                (Some(a), Some(b)) => Arc::ptr_eq(a, b),
                _ => false,
            }
    }
}
impl Eq for ErrorDetail {}
