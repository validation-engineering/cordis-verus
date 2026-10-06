//! Audited native loader boundary. Plugins are trusted machine code implementing
//! the SDK ABI; descriptor validation is not a sandbox or a pointer validator.
#![allow(unsafe_code)]

use super::super::PluginResult;
use cordis_plugin_api::{PluginApiV1, WakeV1, ABI_MAGIC, ABI_VERSION, MAX_MESSAGE_BYTES};
use libloading::Library;
use serde_json::Value;
use std::{ffi::c_void, mem::ManuallyDrop, path::Path};

use std::sync::atomic::{AtomicUsize, Ordering};
pub(super) const IMAGE_LIMIT: usize = 128;
static IMAGE_COUNT: AtomicUsize = AtomicUsize::new(0);
pub(super) fn image_count() -> usize {
    IMAGE_COUNT.load(Ordering::Acquire)
}

/// A permanently mapped library. Even rejected ABI entry points may have run
/// native constructors, so no loaded image is ever passed to dlclose here.
pub(super) struct Image {
    _library: ManuallyDrop<Library>,
    invoke: unsafe extern "C" fn(
        *const u8,
        usize,
        unsafe extern "C" fn(*mut c_void, *const u8, usize),
        *mut c_void,
        WakeV1,
    ) -> u32,
}

#[repr(C)]
#[derive(Clone, Copy)]
struct Header {
    magic: [u8; 8],
    abi_version: u32,
    struct_size: u32,
}

impl Image {
    /// The caller has verified the bytes and made a private immutable snapshot.
    /// The native module must obey the SDK ABI, including synchronous output.
    pub(super) fn load(path: &Path) -> PluginResult<Self> {
        // SAFETY: This intentionally executes trusted native code. Pin the
        // mapping before looking up symbols or calling any plugin entry point.
        IMAGE_COUNT
            .fetch_update(Ordering::AcqRel, Ordering::Acquire, |count| {
                (count < IMAGE_LIMIT).then_some(count + 1)
            })
            .map_err(|_| "NativeModuleImageLimit")?;
        let library = match unsafe { Library::new(path) } {
            Ok(library) => ManuallyDrop::new(library),
            Err(error) => {
                IMAGE_COUNT.fetch_sub(1, Ordering::AcqRel);
                return Err(format!("NativeModuleLoad: {error}"));
            }
        };
        // SAFETY: The sole symbol is specified by the versioned public C ABI.
        let entry = unsafe {
            library.get::<unsafe extern "C" fn() -> *const PluginApiV1>(b"cordis_plugin_v1\0")
        }
        .map_err(|e| format!("NativeModuleEntry: {e}"))?;
        // SAFETY: Trusted SDK entry points return a static ABI header.
        let api = unsafe { entry() };
        if api.is_null() || !(api as usize).is_multiple_of(std::mem::align_of::<PluginApiV1>()) {
            return Err("NativeModuleInvalidHeader".into());
        }
        // Read only the fixed header before accepting the function-table size.
        // SAFETY: The SDK guarantees the pointer covers the common C header.
        let header = unsafe { api.cast::<Header>().read() };
        if header.magic != ABI_MAGIC
            || header.abi_version != ABI_VERSION
            || header.struct_size as usize != std::mem::size_of::<PluginApiV1>()
        {
            return Err("NativeModuleAbiMismatch".into());
        }
        // SAFETY: Validated SDK header identifies the exact V1 table layout.
        let invoke = unsafe { (*api).invoke };
        Ok(Self {
            _library: library,
            invoke,
        })
    }

    pub(super) fn invoke(&self, request: &Value, wake: WakeV1) -> PluginResult<Value> {
        let input = serde_json::to_vec(request).map_err(|e| e.to_string())?;
        if input.len() > MAX_MESSAGE_BYTES {
            return Err("NativeModuleMessageTooLarge".into());
        }
        let mut output = Output::default();
        // SAFETY: input and output live for this synchronous ABI call. The SDK
        // never retains these pointers and supplies valid borrowed output bytes.
        let status = unsafe {
            (self.invoke)(
                input.as_ptr(),
                input.len(),
                collect,
                (&mut output as *mut Output).cast(),
                wake,
            )
        };
        if status != 0 {
            return Err(format!("NativeModuleInvokeStatus: {status}"));
        }
        if output.invalid {
            return Err("NativeModuleInvalidOutput".into());
        }
        let bytes = output.bytes.ok_or("NativeModuleMissingOutput")?;
        let value: Value =
            serde_json::from_slice(&bytes).map_err(|e| format!("NativeModuleInvalidJson: {e}"))?;
        let object = value
            .as_object()
            .filter(|o| o.len() == 1)
            .ok_or("NativeModuleInvalidResponse")?;
        if let Some(value) = object.get("ok") {
            return Ok(value.clone());
        }
        Err(object
            .get("error")
            .and_then(Value::as_str)
            .ok_or("NativeModuleInvalidResponse")?
            .to_owned())
    }
}

#[derive(Default)]
struct Output {
    bytes: Option<Vec<u8>>,
    invalid: bool,
}

unsafe extern "C" fn collect(context: *mut c_void, bytes: *const u8, len: usize) {
    // SAFETY: Image::invoke passes its live exclusive stack Output, and the SDK
    // promises exactly one synchronous callback, without retaining the pointer.
    let output = unsafe { &mut *context.cast::<Output>() };
    if output.bytes.is_some() || bytes.is_null() || len > MAX_MESSAGE_BYTES {
        output.invalid = true;
        return;
    }
    // SAFETY: The SDK owns these valid bytes for the duration of this callback.
    output.bytes = Some(unsafe { std::slice::from_raw_parts(bytes, len) }.to_vec());
}

// The backend-only regression uses the real invoke/callback marshalling with a
// tiny in-process C table. No fixture build or OS-specific shared object is
// required before Cargo tests run. The process image stays mapped as usual.
#[cfg(test)]
pub(super) fn cancellation_probe() -> Image {
    #[cfg(unix)]
    let library: Library = libloading::os::unix::Library::this().into();
    #[cfg(windows)]
    let library: Library = libloading::os::windows::Library::this().unwrap().into();
    Image {
        _library: ManuallyDrop::new(library),
        invoke: probe::invoke,
    }
}
#[cfg(test)]
pub(super) fn set_probe_token(token: u64) {
    probe::TOKEN.store(token, Ordering::Release);
}
#[cfg(test)]
pub(super) fn probe_observation() -> (usize, bool, bool) {
    (
        probe::CALLS.load(Ordering::Acquire),
        probe::RETIRED.load(Ordering::Acquire),
        probe::CANCEL.load(Ordering::Acquire),
    )
}
#[cfg(test)]
mod probe {
    use super::*;
    use std::sync::atomic::{AtomicBool, AtomicU64};
    pub(super) static CALLS: AtomicUsize = AtomicUsize::new(0);
    pub(super) static TOKEN: AtomicU64 = AtomicU64::new(0);
    pub(super) static RETIRED: AtomicBool = AtomicBool::new(false);
    pub(super) static CANCEL: AtomicBool = AtomicBool::new(false);
    pub(super) unsafe extern "C" fn invoke(
        bytes: *const u8,
        length: usize,
        output: cordis_plugin_api::OutputV1,
        context: *mut c_void,
        _wake: WakeV1,
    ) -> u32 {
        // SAFETY: called only by Image::invoke with its live serialized buffer.
        let request: Value =
            serde_json::from_slice(unsafe { std::slice::from_raw_parts(bytes, length) }).unwrap();
        CALLS.fetch_add(1, Ordering::AcqRel);
        CANCEL.store(
            request["op"] == "cancel" && request["job"] == 7,
            Ordering::Release,
        );
        RETIRED.store(
            !super::super::wakes()
                .lock()
                .unwrap()
                .contains_key(&TOKEN.load(Ordering::Acquire)),
            Ordering::Release,
        );
        let response = b"{\"error\":\"fixture cancel failure\"}";
        // SAFETY: the host-provided callback/context remain valid for this call.
        unsafe { output(context, response.as_ptr(), response.len()) };
        0
    }
}

// Exercise the production SDK wire through the production host adapter without
// requiring a separately built platform cdylib in ordinary Cargo tests.
#[cfg(test)]
pub(super) fn reverse_probe() -> Image {
    #[cfg(unix)]
    let library: Library = libloading::os::unix::Library::this().into();
    #[cfg(windows)]
    let library: Library = libloading::os::windows::Library::this().unwrap().into();
    Image {
        _library: ManuallyDrop::new(library),
        invoke: reverse::invoke,
    }
}
#[cfg(test)]
mod reverse {
    use super::*;
    use cordis_plugin_api as sdk;
    use std::future::Future;
    use std::sync::{Arc, Mutex, OnceLock};
    use std::task::Poll;
    static RUNTIME: OnceLock<sdk::PluginResult<sdk::Runtime>> = OnceLock::new();
    struct Factory;
    struct Instance {
        borrowed: Mutex<Vec<Arc<Object>>>,
        escaped: Arc<Mutex<Option<sdk::JsObject>>>,
        cleanup_import: bool,
        child: Arc<Mutex<Option<sdk::ChildHandle>>>,
        state: Arc<std::sync::atomic::AtomicUsize>,
        capture_attempts: std::sync::atomic::AtomicUsize,
        fail_capture: std::sync::atomic::AtomicBool,
        fail_cleanup: std::sync::atomic::AtomicBool,
        fail_restore: bool,
    }
    impl sdk::PluginFactory for Factory {
        fn descriptor(&self) -> sdk::FactoryDescriptor {
            sdk::FactoryDescriptor {
                name: "reverse".into(),
                inject: vec!["js".into()],
                services: vec![sdk::ServiceDescriptor {
                    name: "native".into(),
                    methods: [
                        ("increment", sdk::MethodKind::Async),
                        ("state", sdk::MethodKind::Async),
                        ("publishChild", sdk::MethodKind::Async),
                        ("mountChild", sdk::MethodKind::Async),
                        ("childStatus", sdk::MethodKind::Async),
                        ("childReady", sdk::MethodKind::Async),
                        ("childRetire", sdk::MethodKind::Async),
                        ("childJoin", sdk::MethodKind::Async),
                        ("childRetry", sdk::MethodKind::Async),
                        ("forward", sdk::MethodKind::Async),
                        ("dropped", sdk::MethodKind::Async),
                        ("parallel", sdk::MethodKind::Async),
                        ("importStream", sdk::MethodKind::Async),
                        ("droppedStreamOpen", sdk::MethodKind::Async),
                        ("droppedStreamNext", sdk::MethodKind::Async),
                        ("importObject", sdk::MethodKind::Async),
                        ("importCallback", sdk::MethodKind::Async),
                        ("retryObject", sdk::MethodKind::Async),
                        ("escapeObject", sdk::MethodKind::Async),
                        ("useEscaped", sdk::MethodKind::Async),
                        ("stream", sdk::MethodKind::Stream),
                        ("object", sdk::MethodKind::Object),
                    ]
                    .into_iter()
                    .map(|(name, kind)| sdk::MethodDescriptor {
                        name: name.into(),
                        kind,
                    })
                    .collect(),
                }],
            }
        }
        fn checkpoint_schema(&self) -> Option<sdk::CheckpointSchema> {
            Some(sdk::CheckpointSchema {
                schema: "probe.counter".into(),
                version: 1,
                accepts: vec![],
            })
        }
        fn create(&self, config: Value) -> sdk::PluginResult<Arc<dyn sdk::PluginInstance>> {
            Ok(Arc::new(Instance {
                borrowed: Mutex::new(Vec::new()),
                escaped: Arc::new(Mutex::new(None)),
                cleanup_import: config["cleanupImport"] == true,
                child: Arc::new(Mutex::new(None)),
                state: Arc::new(std::sync::atomic::AtomicUsize::new(0)),
                capture_attempts: std::sync::atomic::AtomicUsize::new(0),
                fail_capture: std::sync::atomic::AtomicBool::new(config["failCapture"] == true),
                fail_cleanup: std::sync::atomic::AtomicBool::new(config["failCleanup"] == true),
                fail_restore: config["failRestore"] == true,
            }))
        }
    }
    impl sdk::PluginInstance for Instance {
        fn checkpoint(&self) -> sdk::PluginResult<Value> {
            let attempt = self
                .capture_attempts
                .fetch_add(1, std::sync::atomic::Ordering::AcqRel)
                + 1;
            if self
                .fail_capture
                .swap(false, std::sync::atomic::Ordering::AcqRel)
            {
                return Err("ProbeCheckpointFailed".into());
            }
            Ok(
                serde_json::json!({"value":self.state.load(std::sync::atomic::Ordering::Acquire),"attempt":attempt}),
            )
        }
        fn restore(&self, checkpoint: sdk::Checkpoint) -> sdk::PluginResult<()> {
            if self.fail_restore {
                return Err("ProbeRestoreFailed".into());
            }
            self.state.store(
                checkpoint.data["value"]
                    .as_u64()
                    .ok_or("BadCounterCheckpoint")? as usize,
                std::sync::atomic::Ordering::Release,
            );
            Ok(())
        }
        fn setup(&self, context: sdk::PluginContext) -> sdk::PluginFuture {
            let state = self.state.load(std::sync::atomic::Ordering::Acquire);
            Box::pin(async move {
                context
                    .call("js", "setup", serde_json::json!([state]))
                    .await
            })
        }
        fn cleanup(&self, context: sdk::PluginContext) -> sdk::PluginFuture {
            let import = self.cleanup_import;
            let fail = self
                .fail_cleanup
                .swap(false, std::sync::atomic::Ordering::AcqRel);
            let state = self.state.clone();
            Box::pin(async move {
                context.call("js", "cleanup", serde_json::json!([])).await?;
                if fail {
                    state.store(999, std::sync::atomic::Ordering::Release);
                    return Err("ProbeCleanupFailed".into());
                }
                if import {
                    context
                        .open_stream("js", "stream", serde_json::json!([]))
                        .await?;
                }
                Ok(Value::Null)
            })
        }
        fn open_stream(
            &self,
            _: &str,
            _: &str,
            args: Value,
        ) -> sdk::PluginResult<Arc<dyn sdk::PluginStream>> {
            Ok(Arc::new(Stream {
                close_import: args[0] == "close-import",
            }))
        }
        fn open_object(
            &self,
            _: &str,
            _: &str,
            args: Value,
        ) -> sdk::PluginResult<Arc<dyn sdk::PluginObject>> {
            let object = Arc::new(Object {
                borrowed: args[0] == "borrowed",
                panic_drop: args[0] == "panic-drop",
            });
            if object.borrowed {
                self.borrowed.lock().unwrap().push(object.clone());
            }
            Ok(object)
        }
        fn call_async(
            &self,
            context: sdk::PluginContext,
            _: &str,
            method: &str,
            args: Value,
        ) -> sdk::PluginFuture {
            if method == "state" {
                let value = self.state.load(std::sync::atomic::Ordering::Acquire);
                return Box::pin(async move { Ok(serde_json::json!(value)) });
            }
            if method == "increment" {
                let state = self.state.clone();
                return Box::pin(async move {
                    context.call("js", "increment", args).await?;
                    Ok(serde_json::json!(
                        state.fetch_add(1, std::sync::atomic::Ordering::AcqRel) + 1
                    ))
                });
            }
            if matches!(method, "publishChild" | "mountChild") {
                let slot = self.child.clone();
                let named = method == "mountChild";
                return Box::pin(async move {
                    let child = if named {
                        context.mount("probe-leaf", args).await?
                    } else {
                        context.publish(LeafFactory, args).await?
                    };
                    *slot.lock().unwrap() = Some(child);
                    Ok(Value::Null)
                });
            }
            if matches!(
                method,
                "childStatus" | "childReady" | "childRetire" | "childJoin" | "childRetry"
            ) {
                let child = self.child.lock().unwrap().as_ref().unwrap().clone();
                let method = method.to_owned();
                return Box::pin(async move {
                    match method.as_str() {
                        "childStatus" => {
                            return Ok(serde_json::json!(child.status(&context).await?))
                        }
                        "childReady" => child.initialized(&context).await?,
                        "childRetire" => child.dispose(&context).await?,
                        "childJoin" => child.join(&context).await?,
                        _ => child.retry_cleanup(&context).await?,
                    }
                    Ok(Value::Null)
                });
            }
            if method == "useEscaped" {
                let object = self.escaped.lock().unwrap().as_ref().unwrap().clone();
                return Box::pin(async move { object.call("call", args).await });
            }
            if method == "escapeObject" {
                // An async body can store a capability without extending the
                // action that admitted it. Share only a destination slot here.
                let slot = self.escaped.clone();
                return Box::pin(async move {
                    *slot.lock().unwrap() = Some(context.open_object("js", "object", args).await?);
                    Ok(Value::Null)
                });
            }
            match method {
                "importStream" => Box::pin(async move {
                    let stream = context.open_stream("js", "stream", args).await?;
                    Ok(stream.next().await?.unwrap_or(Value::Null))
                }),
                "droppedStreamOpen" => Box::pin(async move {
                    let mut open = Box::pin(context.open_stream("js", "stream", args));
                    std::future::poll_fn(|cx| {
                        assert!(open.as_mut().poll(cx).is_pending());
                        Poll::Ready(())
                    })
                    .await;
                    drop(open);
                    Ok(serde_json::json!("dropped open"))
                }),
                "droppedStreamNext" => Box::pin(async move {
                    let stream = context.open_stream("js", "stream", args).await?;
                    let mut next = Box::pin(stream.next());
                    std::future::poll_fn(|cx| {
                        assert!(next.as_mut().poll(cx).is_pending());
                        Poll::Ready(())
                    })
                    .await;
                    drop(next);
                    Ok(serde_json::json!("dropped next"))
                }),
                "importObject" | "retryObject" => {
                    let retry = method == "retryObject";
                    Box::pin(async move {
                        let object = context.open_object("js", "object", args.clone()).await?;
                        let result = object.call("call", args).await?;
                        if retry {
                            assert!(object.close().await.is_err());
                            object.close().await?;
                        }
                        Ok(result)
                    })
                }
                "importCallback" => Box::pin(async move {
                    context
                        .open_callback("js", "callback", args.clone())
                        .await?
                        .invoke(args)
                        .await
                }),
                "dropped" => Box::pin(async move {
                    let mut call = Box::pin(context.call("js", "wait", args));
                    std::future::poll_fn(|cx| {
                        assert!(call.as_mut().poll(cx).is_pending());
                        Poll::Ready(())
                    })
                    .await;
                    drop(call);
                    Ok(serde_json::json!("returned"))
                }),
                "parallel" => Box::pin(async move {
                    let mut first = Box::pin(context.call("js", "first", args.clone()));
                    let mut second = Box::pin(context.call("js", "second", args));
                    let mut a = None;
                    let mut b = None;
                    std::future::poll_fn(move |cx| {
                        if a.is_none() {
                            if let Poll::Ready(value) = first.as_mut().poll(cx) {
                                a = Some(value);
                            }
                        }
                        if b.is_none() {
                            if let Poll::Ready(value) = second.as_mut().poll(cx) {
                                b = Some(value);
                            }
                        }
                        if a.is_some() && b.is_some() {
                            Poll::Ready(Ok(serde_json::json!([
                                a.take().unwrap()?,
                                b.take().unwrap()?
                            ])))
                        } else {
                            Poll::Pending
                        }
                    })
                    .await
                }),
                _ => Box::pin(async move { context.call("js", "wait", args).await }),
            }
        }
    }
    struct Stream {
        close_import: bool,
    }
    impl sdk::PluginStream for Stream {
        fn next(&self, context: sdk::PluginContext) -> sdk::StreamFuture {
            Box::pin(async move {
                context
                    .call("js", "streamNext", serde_json::json!([]))
                    .await
                    .map(Some)
            })
        }
        fn close(&self, context: sdk::PluginContext) -> sdk::PluginFuture {
            let import = self.close_import;
            Box::pin(async move {
                context
                    .call("js", "streamClose", serde_json::json!([]))
                    .await?;
                if import {
                    context
                        .open_stream("js", "stream", serde_json::json!([]))
                        .await?;
                }
                Ok(Value::Null)
            })
        }
    }
    struct Object {
        borrowed: bool,
        panic_drop: bool,
    }
    impl sdk::PluginObject for Object {
        fn descriptor(&self) -> sdk::ObjectDescriptor {
            sdk::ObjectDescriptor::callback(
                "probe.Object",
                if self.borrowed {
                    sdk::ObjectOwnership::Borrowed
                } else {
                    sdk::ObjectOwnership::Owned
                },
            )
            .unwrap()
        }
        fn call(&self, context: sdk::PluginContext, _: &str, args: Value) -> sdk::PluginFuture {
            Box::pin(async move { context.call("js", "objectCall", args).await })
        }
        fn close(&self, context: sdk::PluginContext) -> sdk::PluginFuture {
            Box::pin(async move {
                context
                    .call("js", "objectClose", serde_json::json!([]))
                    .await
            })
        }
    }
    impl Drop for Object {
        fn drop(&mut self) {
            assert!(!self.panic_drop, "probe object destructor failure");
        }
    }
    struct LeafFactory;
    struct Leaf {
        fail_cleanup: std::sync::atomic::AtomicBool,
    }
    impl sdk::PluginFactory for LeafFactory {
        fn descriptor(&self) -> sdk::FactoryDescriptor {
            sdk::FactoryDescriptor {
                name: "probe-leaf".into(),
                inject: vec!["js".into()],
                services: vec![sdk::ServiceDescriptor {
                    name: "leaf".into(),
                    methods: vec![],
                }],
            }
        }
        fn create(&self, config: Value) -> sdk::PluginResult<Arc<dyn sdk::PluginInstance>> {
            Ok(Arc::new(Leaf {
                fail_cleanup: std::sync::atomic::AtomicBool::new(config["failCleanup"] == true),
            }))
        }
    }
    impl sdk::PluginInstance for Leaf {
        fn setup(&self, _: sdk::PluginContext) -> sdk::PluginFuture {
            Box::pin(async { Ok(Value::Null) })
        }
        fn cleanup(&self, _: sdk::PluginContext) -> sdk::PluginFuture {
            let fail = self
                .fail_cleanup
                .swap(false, std::sync::atomic::Ordering::AcqRel);
            Box::pin(async move {
                if fail {
                    Err("ProbeChildCleanupFailed".into())
                } else {
                    Ok(Value::Null)
                }
            })
        }
    }
    fn module() -> sdk::Module {
        sdk::Module::new("reverse-probe", "1")
            .factory(Factory)
            .factory(LeafFactory)
    }
    pub(super) unsafe extern "C" fn invoke(
        bytes: *const u8,
        length: usize,
        output: sdk::OutputV1,
        context: *mut c_void,
        wake: WakeV1,
    ) -> u32 {
        // SAFETY: forwarded unchanged from Image::invoke's live input/output.
        unsafe { sdk::invoke_export(&RUNTIME, module, bytes, length, output, context, wake) }
    }
}
