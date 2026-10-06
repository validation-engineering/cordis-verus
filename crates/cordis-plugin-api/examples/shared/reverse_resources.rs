use super::*;
use cordis_plugin_api::{JsCallback, JsObject, JsStream};
use std::sync::Mutex;

pub(super) struct ReverseResourceFactory {
    pub version: &'static str,
    pub failing: bool,
}
impl PluginFactory for ReverseResourceFactory {
    fn descriptor(&self) -> FactoryDescriptor {
        FactoryDescriptor {
            name: "native-js-resources".into(),
            inject: vec!["jsHost".into()],
            services: vec![ServiceDescriptor {
                name: "nativeJsResources".into(),
                methods: [
                    "stream",
                    "object",
                    "callback",
                    "dropped_open",
                    "dropped_next",
                    "dropped_call",
                    "stream_busy",
                    "object_busy",
                    "stale_stream",
                    "stale_object",
                ]
                .into_iter()
                .map(|name| MethodDescriptor {
                    name: name.into(),
                    kind: MethodKind::Async,
                })
                .collect(),
            }],
        }
    }
    fn create(&self, config: Value) -> PluginResult<Arc<dyn PluginInstance>> {
        Ok(Arc::new(Instance {
            version: self.version,
            failing: self.failing,
            config,
            stream: Arc::new(Mutex::new(None)),
            object: Arc::new(Mutex::new(None)),
        }))
    }
}
struct Instance {
    version: &'static str,
    failing: bool,
    config: Value,
    stream: Arc<Mutex<Option<JsStream>>>,
    object: Arc<Mutex<Option<JsObject>>>,
}
impl PluginInstance for Instance {
    fn setup(&self, ctx: PluginContext) -> PluginFuture {
        let version = self.version;
        let failing = self.failing || enabled(&self.config, "fail_setup");
        Box::pin(async move {
            ctx.call(
                "jsHost",
                "record",
                json!([{"phase":"js-resources-setup","version":version}]),
            )
            .await?;
            if failing {
                Err("CandidateSetupFailed".into())
            } else {
                Ok(Value::Null)
            }
        })
    }
    fn cleanup(&self, ctx: PluginContext) -> PluginFuture {
        let version = self.version;
        let stream = self.config.get("cleanupStreamArgs").cloned();
        let object = self.config.get("cleanupObjectArgs").cloned();
        Box::pin(async move {
            ctx.call(
                "jsHost",
                "record",
                json!([{"phase":"js-resources-cleanup","version":version}]),
            )
            .await?;
            if let Some(args) = stream {
                ctx.open_stream("jsHost", "stream", args).await?;
            }
            if let Some(args) = object {
                ctx.open_object("jsHost", "object", args).await?;
            }
            Ok(Value::Null)
        })
    }
    fn call_async(&self, ctx: PluginContext, _: &str, method: &str, args: Value) -> PluginFuture {
        let version = self.version;
        let mode = method.to_owned();
        let options = normalize_args(args);
        let saved_stream = self.stream.clone();
        let saved_object = self.object.clone();
        Box::pin(async move {
            let service = options["service"].as_str().unwrap_or("jsHost");
            let open_args = options.get("args").cloned().unwrap_or_else(|| json!([]));
            let close = enabled(&options, "close");
            let retry = enabled(&options, "retryClose");
            let method = options["method"].as_str();
            match mode.as_str() {
                "stale_stream" => {
                    let stream = saved_stream
                        .lock()
                        .unwrap()
                        .clone()
                        .ok_or("NoSavedStream")?;
                    stream.next().await.map(|value| json!(value))
                }
                "stale_object" => {
                    let object = saved_object
                        .lock()
                        .unwrap()
                        .clone()
                        .ok_or("NoSavedObject")?;
                    object.call("read", json!([])).await
                }
                "dropped_open" => {
                    let kind = options["kind"].as_str().unwrap_or("stream");
                    match kind {
                        "stream" => {
                            drop_after_poll(ctx.open_stream(
                                service,
                                method.unwrap_or("stream"),
                                open_args,
                            ))
                            .await?
                        }
                        "object" => {
                            drop_after_poll(ctx.open_object(
                                service,
                                method.unwrap_or("object"),
                                open_args,
                            ))
                            .await?
                        }
                        "callback" => {
                            drop_after_poll(ctx.open_callback(
                                service,
                                method.unwrap_or("callback"),
                                open_args,
                            ))
                            .await?
                        }
                        _ => return Err("UnknownResourceKind".into()),
                    }
                    Ok(json!({"version":version,"dropped":kind}))
                }
                "stream" | "dropped_next" | "stream_busy" => {
                    let stream = ctx
                        .open_stream(service, method.unwrap_or("stream"), open_args)
                        .await?;
                    if enabled(&options, "escape") {
                        *saved_stream.lock().unwrap() = Some(stream.clone());
                    }
                    if mode != "stream" {
                        drop_after_poll(stream.next()).await?;
                        if mode == "stream_busy" {
                            let next_error = stream.next().await.err();
                            let close_error = stream.close().await.err();
                            return Ok(
                                json!({"version":version,"nextError":next_error,"closeError":close_error}),
                            );
                        }
                        return Ok(json!({"version":version,"dropped":"next"}));
                    }
                    let limit = options["limit"].as_u64().unwrap_or(16).min(1024);
                    let mut values = Vec::new();
                    let mut failure = None;
                    for _ in 0..limit {
                        match stream.next().await {
                            Ok(Some(value)) => values.push(value),
                            Ok(None) => break,
                            Err(error) => {
                                failure = Some(error);
                                break;
                            }
                        }
                    }
                    let close_error = if close {
                        close_stream(&stream, retry).await?
                    } else {
                        None
                    };
                    if let Some(error) = failure {
                        return Err(error);
                    }
                    if enabled(&options, "probe") {
                        let probe_bytes = values
                            .iter()
                            .map(|value| {
                                serde_json::to_vec(value)
                                    .map(|encoded| encoded.len())
                                    .map_err(|_| "ProbeEncoding".to_owned())
                            })
                            .collect::<PluginResult<Vec<_>>>()?;
                        return Ok(
                            json!({"version":version,"probeBytes":probe_bytes,"closeError":close_error}),
                        );
                    }
                    Ok(json!({"version":version,"values":values,"closeError":close_error}))
                }
                "object" | "dropped_call" | "object_busy" => {
                    let object = ctx
                        .open_object(service, method.unwrap_or("object"), open_args)
                        .await?;
                    if enabled(&options, "escape") {
                        *saved_object.lock().unwrap() = Some(object.clone());
                    }
                    if mode != "object" {
                        let call_method = options["call"]["method"].as_str().unwrap_or("read");
                        let call_args = options["call"]
                            .get("args")
                            .cloned()
                            .unwrap_or_else(|| json!([]));
                        drop_after_poll(object.call(call_method, call_args)).await?;
                        if mode == "object_busy" {
                            return Ok(
                                json!({"version":version,"closeError":object.close().await.err()}),
                            );
                        }
                        return Ok(json!({"version":version,"dropped":"call"}));
                    }
                    let calls = options
                        .get("calls")
                        .cloned()
                        .unwrap_or_else(|| json!([{"method":"read","args":[]}]));
                    let mut results = Vec::new();
                    for call in calls.as_array().ok_or("CallsMustBeArray")? {
                        results.push(
                            object
                                .call(
                                    call["method"].as_str().ok_or("ExpectedMethod")?,
                                    call.get("args").cloned().unwrap_or_else(|| json!([])),
                                )
                                .await?,
                        );
                    }
                    let close_error = if close {
                        close_object(&object, retry).await?
                    } else {
                        None
                    };
                    Ok(
                        json!({"version":version,"descriptor":object.descriptor(),"results":results,"closeError":close_error}),
                    )
                }
                "callback" => {
                    let callback = ctx
                        .open_callback(service, method.unwrap_or("callback"), open_args)
                        .await?;
                    let calls = options.get("calls").cloned().unwrap_or_else(|| json!([[]]));
                    let mut results = Vec::new();
                    for args in calls.as_array().ok_or("CallsMustBeArray")? {
                        results.push(callback.invoke(args.clone()).await?);
                    }
                    let close_error = if close {
                        close_callback(&callback, retry).await?
                    } else {
                        None
                    };
                    Ok(
                        json!({"version":version,"descriptor":callback.descriptor(),"results":results,"closeError":close_error}),
                    )
                }
                _ => Err("UnknownMethod".into()),
            }
        })
    }
}
async fn drop_after_poll<T>(future: impl Future<Output = PluginResult<T>>) -> PluginResult<()> {
    let mut future = Box::pin(future);
    std::future::poll_fn(|cx| match future.as_mut().poll(cx) {
        Poll::Pending | Poll::Ready(Ok(_)) => Poll::Ready(Ok(())),
        Poll::Ready(Err(error)) => Poll::Ready(Err(error)),
    })
    .await
}
async fn close_stream(stream: &JsStream, retry: bool) -> PluginResult<Option<String>> {
    match stream.close().await {
        Ok(()) => Ok(None),
        Err(error) if retry => {
            stream.close().await?;
            Ok(Some(error))
        }
        Err(error) => Err(error),
    }
}
async fn close_object(object: &JsObject, retry: bool) -> PluginResult<Option<String>> {
    match object.close().await {
        Ok(()) => Ok(None),
        Err(error) if retry => {
            object.close().await?;
            Ok(Some(error))
        }
        Err(error) => Err(error),
    }
}
async fn close_callback(callback: &JsCallback, retry: bool) -> PluginResult<Option<String>> {
    match callback.close().await {
        Ok(()) => Ok(None),
        Err(error) if retry => {
            callback.close().await?;
            Ok(Some(error))
        }
        Err(error) => Err(error),
    }
}
