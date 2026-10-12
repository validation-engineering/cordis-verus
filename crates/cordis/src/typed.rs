//! Declare required dependencies once and receive their committed values.
//!
//! This ordinary Rust adapter generates the existing Plugin declarations and
//! reads through AsyncSetup::require. It creates no independent service registry
//! or lifecycle authority. Extra manual context reads remain runtime checked.
use crate::{AsyncSetup, CallbackResult, Plugin, ServiceKey, ServiceReadError, Setup};
use std::any::Any;
use std::future::Future;
use std::sync::Arc;

mod private {
    pub trait Sealed {}
}

/// A closed set of dependency descriptions: a key, a configured key, (), or a
/// tuple of up to eight descriptions. Sealing prevents third-party declarations
/// from silently disagreeing with their value reads.
pub trait Dependencies: private::Sealed + Clone + Send + 'static {
    type Values: Send + 'static;
    #[doc(hidden)]
    fn declare(&self, plugin: Plugin) -> Plugin;
    #[doc(hidden)]
    fn resolve(&self, setup: &AsyncSetup) -> Result<Self::Values, ServiceReadError>;
}

impl<T: Any + Send + Sync> private::Sealed for ServiceKey<T> {}
impl<T: Any + Send + Sync> Dependencies for ServiceKey<T> {
    type Values = Arc<T>;
    fn declare(&self, plugin: Plugin) -> Plugin {
        plugin.requires(*self)
    }
    fn resolve(&self, setup: &AsyncSetup) -> Result<Self::Values, ServiceReadError> {
        setup.require(*self)
    }
}

/// A required dependency with input for its provider's availability predicate.
pub struct ConfiguredDependency<T> {
    key: ServiceKey<T>,
    config: serde_json::Value,
}
impl<T> Clone for ConfiguredDependency<T> {
    fn clone(&self) -> Self {
        Self {
            key: self.key,
            config: self.config.clone(),
        }
    }
}
impl<T> ServiceKey<T> {
    pub fn with_config(self, config: serde_json::Value) -> ConfiguredDependency<T> {
        ConfiguredDependency { key: self, config }
    }
}
impl<T: Any + Send + Sync> private::Sealed for ConfiguredDependency<T> {}
impl<T: Any + Send + Sync> Dependencies for ConfiguredDependency<T> {
    type Values = Arc<T>;
    fn declare(&self, plugin: Plugin) -> Plugin {
        plugin.requires_with_config(self.key, self.config.clone())
    }
    fn resolve(&self, setup: &AsyncSetup) -> Result<Self::Values, ServiceReadError> {
        setup.require(self.key)
    }
}
impl private::Sealed for () {}
impl Dependencies for () {
    type Values = ();
    fn declare(&self, plugin: Plugin) -> Plugin {
        plugin
    }
    fn resolve(&self, _: &AsyncSetup) -> Result<(), ServiceReadError> {
        Ok(())
    }
}
macro_rules! tuple_dependencies {
    ($($name:ident:$index:tt),+) => {
        impl<$($name: Dependencies),+> private::Sealed for ($($name,)+) {}
        impl<$($name: Dependencies),+> Dependencies for ($($name,)+) {
            type Values = ($($name::Values,)+);
            fn declare(&self, plugin: Plugin) -> Plugin {
                $(let plugin = self.$index.declare(plugin);)+
                plugin
            }
            fn resolve(&self, setup: &AsyncSetup) -> Result<Self::Values, ServiceReadError> {
                Ok(($(self.$index.resolve(setup)?,)+))
            }
        }
    };
}
tuple_dependencies!(A:0);
tuple_dependencies!(A:0, B:1);
tuple_dependencies!(A:0, B:1, C:2);
tuple_dependencies!(A:0, B:1, C:2, D:3);
tuple_dependencies!(A:0, B:1, C:2, D:3, E:4);
tuple_dependencies!(A:0, B:1, C:2, D:3, E:4, F:5);
tuple_dependencies!(A:0, B:1, C:2, D:3, E:4, F:5, G:6);
tuple_dependencies!(A:0, B:1, C:2, D:3, E:4, F:5, G:6, H:7);

pub struct TypedPluginBuilder<D> {
    name: String,
    dependencies: D,
}
impl Plugin {
    /// Generate the dependency declaration and setup inputs from the same keys.
    /// Missing providers still wait at runtime; a value-type mismatch fails to compile.
    ///
    /// ```
    /// use cordis::{Plugin, ServiceKey};
    /// let greeting = ServiceKey::<String>::of();
    /// let consumer = Plugin::with_dependencies("consumer", (greeting,))
    ///     .setup(|_, (greeting,)| { println!("{greeting}"); Ok(()) });
    /// ```
    ///
    /// ```compile_fail
    /// use cordis::{Plugin, ServiceKey};
    /// use std::sync::Arc;
    /// Plugin::with_dependencies("wrong type", ServiceKey::<String>::of())
    ///     .setup(|_, value: Arc<u64>| Ok(()));
    /// ```
    ///
    /// ```compile_fail
    /// use cordis::{Plugin, ServiceKey};
    /// Plugin::with_dependencies("wrong tuple", (ServiceKey::<String>::of(),))
    ///     .setup_async(|_, (a, b)| async move { Ok(()) });
    /// ```
    pub fn with_dependencies<D: Dependencies>(
        name: impl Into<String>,
        dependencies: D,
    ) -> TypedPluginBuilder<D> {
        TypedPluginBuilder {
            name: name.into(),
            dependencies,
        }
    }
}
impl<D: Dependencies> TypedPluginBuilder<D> {
    pub fn setup(
        self,
        mut callback: impl FnMut(&mut Setup<'_>, D::Values) -> CallbackResult + Send + 'static,
    ) -> Plugin {
        let keys = self.dependencies.clone();
        self.dependencies
            .declare(Plugin::new(self.name, move |setup| {
                let values = keys.resolve(&setup.to_async())?;
                callback(setup, values)
            }))
    }
    pub fn setup_async<F, Fut>(self, mut callback: F) -> Plugin
    where
        F: FnMut(AsyncSetup, D::Values) -> Fut + Send + 'static,
        Fut: Future<Output = CallbackResult> + Send + 'static,
    {
        let keys = self.dependencies.clone();
        self.dependencies
            .declare(Plugin::new_async(self.name, move |setup| {
                let next = keys.resolve(&setup).map(|values| callback(setup, values));
                async move { next?.await }
            }))
    }
}
