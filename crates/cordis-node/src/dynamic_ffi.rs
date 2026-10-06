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
