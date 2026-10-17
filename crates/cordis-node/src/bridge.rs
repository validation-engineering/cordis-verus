//! Small Node-API identity boundary. Native storage holds weak references;
//! JavaScript retains the corresponding immutable payload boxes. No JS is called
//! under a Driver or Bridge borrow, and no native strong reference cycle is added.
use crate::NativeDriver;
use cordis_driver::{ActionTicket, Command, HostBridge, HostCall, ObjectKey};
use napi::bindgen_prelude::{JavaScriptClassExt, Reference, WeakReference};
use napi::{Env, Error, Result, Status};
use napi_derive::napi;
use serde_json::json;
use std::cell::RefCell;

pub(crate) type Objects = RefCell<HostBridge<WeakReference<NativeObject>>>;
#[napi]
pub struct NativeObject {
    key: Option<ObjectKey>,
}
#[napi]
impl NativeObject {
    #[napi(getter)]
    pub fn id(&self) -> Result<String> {
        Ok(self.key()?.id().to_string())
    }
}
impl NativeObject {
    fn key(&self) -> Result<ObjectKey> {
        self.key
            .ok_or_else(|| Error::new(Status::GenericFailure, "Unbound host object"))
    }
}
#[napi]
pub struct NativeCall {
    call: HostCall,
}
#[napi(object)]
pub struct NativeRead {
    pub owner: String,
    pub publication: String,
    pub object: Reference<NativeObject>,
}
fn failed(error: impl std::fmt::Display) -> Error {
    Error::new(Status::GenericFailure, error.to_string())
}
fn number<T: std::str::FromStr>(value: &str) -> Result<T> {
    value
        .parse()
        .map_err(|_| Error::new(Status::InvalidArg, "Invalid host identity"))
}
fn upgrade(value: &WeakReference<NativeObject>, env: Env) -> Result<Reference<NativeObject>> {
    value.upgrade(env)?.ok_or_else(|| {
        Error::new(
            Status::GenericFailure,
            "Host object lost its JavaScript retention root",
        )
    })
}
#[napi]
impl NativeDriver {
    #[napi]
    pub fn enable_host_bridge(&self) -> Result<()> {
        self.check_fault()?;
        if !self.host_mode.get()
            && !self
                .driver
                .try_borrow()
                .map_err(failed)?
                .can_enable_host_bridge()
        {
            return Err(failed("HostBridge must be enabled before mounting plugins"));
        }
        self.host_mode.set(true);
        Ok(())
    }
    #[napi]
    pub fn validate_host_snapshot(&self) -> Result<()> {
        self.check_fault()?;
        self.driver
            .try_borrow()
            .map_err(failed)?
            .validate_host_snapshot(&*self.objects.try_borrow().map_err(failed)?)
            .map_err(failed)
    }
    #[napi]
    pub fn create_object(&self, env: Env) -> Result<Reference<NativeObject>> {
        self.check_fault()?;
        let mut object = NativeObject { key: None }.into_reference(env)?;
        let key = self
            .objects
            .try_borrow_mut()
            .map_err(failed)?
            .issue(object.downgrade())
            .map_err(|_| Error::new(Status::GenericFailure, "Host object identity exhausted"))?;
        object.key = Some(key);
        Ok(object)
    }
    #[napi]
    pub fn get_object(&self, env: Env, id: String) -> Result<Option<Reference<NativeObject>>> {
        self.check_fault()?;
        let objects = self.objects.try_borrow().map_err(failed)?;
        objects
            .lookup(number(&id)?)
            .map(|value| upgrade(value, env))
            .transpose()
    }
    #[napi]
    pub fn drop_object(&self, id: String) -> Result<()> {
        self.check_fault()?;
        let driver = self.driver.try_borrow().map_err(failed)?;
        let mut objects = self.objects.try_borrow_mut().map_err(failed)?;
        driver
            .remove_host_object(&mut objects, number(&id)?)
            .map_err(failed)?;
        Ok(())
    }
    #[napi]
    pub fn bind_fiber(&self, id: String, object: &NativeObject) -> Result<()> {
        self.check_fault()?;
        self.driver
            .try_borrow()
            .map_err(failed)?
            .bind_host_fiber(
                &mut *self.objects.try_borrow_mut().map_err(failed)?,
                number(&id)?,
                object.key()?,
            )
            .map_err(failed)
    }
    #[napi]
    pub fn get_fiber(&self, env: Env, id: String) -> Result<Option<Reference<NativeObject>>> {
        self.check_fault()?;
        self.objects
            .try_borrow()
            .map_err(failed)?
            .fiber(number(&id)?)
            .map(|value| upgrade(value, env))
            .transpose()
    }
    #[napi]
    pub fn unbind_fiber(&self, id: String) -> Result<Option<String>> {
        self.check_fault()?;
        self.driver
            .try_borrow()
            .map_err(failed)?
            .unbind_host_fiber(
                &mut *self.objects.try_borrow_mut().map_err(failed)?,
                number(&id)?,
            )
            .map(|key| key.map(|key| key.to_string()))
            .map_err(failed)
    }
    #[napi]
    pub fn begin_action(
        &self,
        ticket: String,
        fiber: &NativeObject,
        recipe: &NativeObject,
    ) -> Result<NativeCall> {
        self.check_fault()?;
        let ticket: ActionTicket = serde_json::from_str(&ticket).map_err(failed)?;
        let call = self
            .driver
            .try_borrow()
            .map_err(failed)?
            .begin_host_call(
                &mut *self.objects.try_borrow_mut().map_err(failed)?,
                ticket,
                fiber.key()?,
                recipe.key()?,
            )
            .map_err(failed)?;
        Ok(NativeCall { call })
    }
    #[napi]
    pub fn action_live(&self, call: &NativeCall) -> Result<bool> {
        self.check_fault()?;
        Ok(self
            .objects
            .try_borrow()
            .map_err(failed)?
            .validate_call(&call.call))
    }
    #[napi]
    pub fn action_recipe(&self, env: Env, call: &NativeCall) -> Result<Reference<NativeObject>> {
        self.check_fault()?;
        let objects = self.objects.try_borrow().map_err(failed)?;
        if !objects.validate_call(&call.call) {
            return Err(failed("Stale host dispatch"));
        }
        upgrade(
            objects
                .get(call.call.recipe())
                .ok_or_else(|| failed("Missing callback recipe"))?,
            env,
        )
    }
    #[napi]
    pub fn complete_action(
        &self,
        call: &NativeCall,
        success: bool,
        error: Option<String>,
    ) -> Result<()> {
        self.check_fault()?;
        let mut objects = self.objects.try_borrow_mut().map_err(failed)?;
        self.scope_command(|driver| {
            driver.complete_host_call(&mut objects, &call.call, success, error)
        })
    }
    #[napi]
    pub fn object_command(&self, input: String, object: &NativeObject) -> Result<String> {
        self.check_fault()?;
        let command: Command = serde_json::from_str(&input).map_err(failed)?;
        let mut driver = self.driver.try_borrow_mut().map_err(failed)?;
        let objects = self.objects.try_borrow().map_err(failed)?;
        let key = object.key()?;
        let reply = match command {
            Command::Publish {
                id,
                generation,
                key: port_key,
                realm,
                value,
                check,
            } => {
                if value != key.id() {
                    return Err(failed("Host value identity mismatch"));
                }
                let publication = driver
                    .publish_host_object(
                        &objects,
                        id,
                        generation,
                        cordis_driver::ServicePort {
                            key: port_key,
                            realm,
                        },
                        key,
                        check,
                    )
                    .map_err(failed)?;
                json!({"publication":publication.to_string()})
            }
            Command::Set {
                id,
                generation,
                publication,
                value,
            } => {
                if value != key.id() {
                    return Err(failed("Host value identity mismatch"));
                }
                driver
                    .set_host_object(&objects, id, generation, publication, key)
                    .map_err(failed)?;
                json!({})
            }
            _ => return Err(failed("Expected an object publish or replacement")),
        };
        Ok(reply.to_string())
    }
    #[napi]
    pub fn resolve_object(&self, env: Env, input: String) -> Result<Option<NativeRead>> {
        self.check_fault()?;
        let Command::Resolve {
            key,
            realm,
            consumer,
            generation,
        } = serde_json::from_str(&input).map_err(failed)?
        else {
            return Err(failed("Expected a resolve request"));
        };
        let mut driver = self.driver.try_borrow_mut().map_err(failed)?;
        let objects = self.objects.try_borrow().map_err(failed)?;
        driver
            .resolve_host_object(
                &objects,
                cordis_driver::ServicePort { key, realm },
                consumer,
                generation,
            )
            .map_err(failed)?
            .map(|(publication, owner, object)| {
                Ok(NativeRead {
                    publication: publication.to_string(),
                    owner: owner.to_string(),
                    object: upgrade(object, env)?,
                })
            })
            .transpose()
    }
}
impl NativeDriver {
    pub(crate) fn check_host_command(&self, input: &str) -> Result<()> {
        if self.host_mode.get() {
            let command: Command = serde_json::from_str(input).map_err(failed)?;
            if matches!(
                command,
                Command::Publish { .. } | Command::Set { .. } | Command::Complete { .. }
            ) {
                return Err(failed("HostBridgeRequired: object writes and callback completion require their native capabilities"));
            }
        }
        Ok(())
    }
}
