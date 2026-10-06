# 同图 Rust / JavaScript 插件

`cordis-node::plugin` 提供可由用户编译扩展的 Rust SDK。Node facade 用 `ctx.rustPlugin(name, config)` 创建普通 Fiber；它和 JS 插件使用**同一个 NativeDriver、依赖图、publication 与 cleanup 屏障**。Rust 插件不在内部创建另一个 `Runtime`。

当前跨语言接口包括 JSON DTO、双向 pull stream，以及显式 opaque object/callback adapter。服务和方法有声明，Rust 内部状态仍为自己的类型，JS 插件之间继续使用原生 JS 对象。对象和回调通过声明的 factory 方法取得；后续方法参数与结果仍是 JSON，不能把任意句柄、闭包或对象引用混入 DTO。既有 `cordis::Plugin` 的 typed 服务可通过显式绑定接入，且可 opt-in 更新已声明服务的值与 availability，见[typed 插件指南](typed-rust-plugins.md)；显式动态接口表也可接入原 `publish` 和子插件，effect group、配置更新 hook 等剩余 Runtime 能力仍需迁移。

## 运行示例

```sh
node scripts/build-node.mjs --offline
node examples/node/rust-interop.mjs
```

构建会分别生成默认 addon 和 [用户 factory 示例 addon](../crates/cordis-node/examples/interop_fixture.rs)。默认 addon 没有内置 `fixture.counter`；示例通过公开 SDK 注册自己的 factory，导出 `createDriver()`，然后由 `Context({ addon })` 选择。

```js
const ctx = new Context({ addon: '/absolute/path/my-addon.node' })
ctx.provide('jsSource', {
  read: () => 40,
  query: async value => ({ echo: value }),
  record: (phase, value) => { console.log(phase, value); return null },
})
await ctx.rustPlugin('fixture.counter')
await ctx.inject(['rustCounter'], async consumer => {
  console.log(consumer.rustCounter.add(2))
  console.log(await consumer.rustCounter.request('hello'))
})
await ctx.dispose()
```

模块加载和 Rust 编译是两件事：factory 必须先编译进用户的 Node addon。没有通过 Rust 不稳定的动态库 ABI 装载任意 `.rs` 或 trait object；源码变化需要重新构建并重启 environment。配置重启仍可复用已编译的 factory。

## 编写 Rust factory

在自己的 `cdylib` crate 中依赖匹配版本的 `cordis-node`、`napi`、`napi-derive`，使用 `napi-build`。完整可编译实现见示例，而不是复制项目内部的 Driver 状态机。

- `PluginFactory::descriptor()` 声明 factory 名称、注入依赖和导出服务的方法模式：`Sync`、`Async`、`Stream`、`Object`；`create(config)` 创建每一代独立实例。
- `PluginInstance::setup(PluginContext)` 返回普通 `Send + 'static` Rust Future。`ctx.provide(name).await` 通过现有 Fiber 发布服务；`ctx.call(service, method, args).await` 调用已声明的 JS 依赖。
- `call_sync` 只执行有界、不等待 JS 的同步方法；`call_async` 返回 Future。实例可以持有自己的 `Arc`、锁和 typed 状态；不要跨 `.await` 或反调持锁。
- `cleanup(ctx)` 在下游消费者完成后运行，仍可访问本代承诺的 JS 依赖。清理失败保留实例和依赖，`fiber.retryCleanup()` 可重试；插件自己记录已成功执行的外部清理步骤，避免重复副作用。
- `FactoryRegistry::register(factory)` 后用 `NativeDriver::with_factories(registry)` 构造同一图的宿主，向 Node 导出 `createDriver()`。

Future 的 `Wake` 通过非阻塞 Node-API 通知调度，空闲域不保持进程存活；存在在途 Future 时保持事件循环。这个执行器不自动提供 Tokio reactor。需要外部 I/O runtime 的插件应显式持有它，让 worker 返回 owned Rust 数据并唤醒 Future；worker 不接触 JS 引用，也不能阻塞等待 Node 同步返回。

## 双向流

Rust 服务声明 `MethodKind::Stream`，由 `PluginInstance::open_stream(service, method, args)` 返回 `Arc<dyn PluginStream>`。`next(ctx)` 返回 `StreamFuture`：`Some(JSON)` 产生一项，`None` 表示 EOF。`cancel()` 只发出有界的合作取消请求；异步 `close(ctx)` 在在途 pull 及其外部调用真实结束后执行。需要唤醒阻塞读取时应响应 `ctx.cancellation()` 或实现 `cancel()`，不能在取消时销毁仍被读取的资源。

```js
const stream = consumer.rustCounter.stream({ count: 3 })
for await (const value of stream) {
  console.log(value)
  if (value === 1) break  // 等待真正关闭，而不是只丢弃 JS wrapper
}
```

这是单项按需读取，没有自动预取；并发 `next()` 拒绝 `StreamBusy`，避免无界缓冲。自然 EOF、`for await` 提前退出、显式 `return()` 和 consumer/provider 卸载都会关闭流。多个正在进行的 `return()` 共享一次尝试；失败保留资源和旧依赖，后续 `return()` 或 `retryCleanup()` 可重试。空闲流也登记在 provider session 与原 consumer Fiber，不能通过复制给另一 Fiber 转移所有权。每次 pull 和 close 使用新的短动作，检查原代及精确 publication；不延长 opener 的旧动作凭证。清理阶段禁止新建 Rust 流。

Rust 消费 JS 流时使用相反的显式适配器：

```rust
let stream = ctx.open_stream("jsSource", "stream", serde_json::json!([])).await?;
while let Some(item) = stream.next().await? {
    // 处理 JSON item；下一次 next 才请求下一项。
}
stream.close().await?;
```

JS 方法应返回 async iterator，或返回能生成它的 async iterable。必须提供 `next()`、显式 `return()`，且结果有 boolean `done`；元素遵循下面的 JSON 合同。普通 `async function*` 满足这些要求。句柄只属于创建它的 Rust action；提前返回、遗忘显式 close 或丢弃 `JsStream` 后，native journal 仍会调用 JS `return()` 并等待真实完成，随后 Rust job 才能落地。取消会先调用 `return()` 再等待已发的 `next()`，支持依靠 return 唤醒 next 的自定义 iterator。`done:false` 的 return 被视为未关闭；失败资源保留到 owner cleanup 重试。一般异步生成器仍可能自行等待一个永不完成的 Promise，框架不会伪造完成。

Rust 代码显式调用 `JsStream.close().await` 时，应先等待自己的 `next()`；仍有 pending pull 时返回 `StreamBusy`，不改变准入，也不发出新的关闭请求。这避免共享 clone 在反向回调链中等待自身。框架的取消和自动 journal 使用独立控制路径，仍先发 `return()` 再等待 pending `next()`，不能把业务 close 的 Busy 合同当成取消时跳过回收的理由。

反向流的关闭权限绑定具体 pending request，允许沿旧 committed 依赖链完成恢复。取得可调用 `return` 后的异常 `next` getter、晚到的 open 和丢弃的 Rust request future 仍保留资源追踪；原生故障标记清理未确认，GC 不作为成功清理的证据。

## 显式对象与回调

Rust 导出对象时声明 `MethodKind::Object`，实现 `PluginInstance::open_object(service, method, args)`，返回 `Arc<dyn PluginObject>`。`ObjectDescriptor::new(type_name, methods, ownership)` 固定类型名、非空且不重复的方法白名单，以及 `ObjectOwnership::Borrowed` 或 `Owned`。`type_name` 是接口标识，不会触发动态类型转换。`PluginObject::call(ctx, method, args)` 返回 Future；每次调用有独立 job、取消 token 和原始 consumer/publication 校验，不会重定向到新一代实例。

```js
const object = consumer.rustCounter.object() // 示例 addon 的对象 factory 方法
console.log(object.typeName, object.ownership, object.methods)
console.log(await object.call('add', 2))
console.log(await object.call('read'))
await object.close()
```

wrapper 有私有品牌，不能由普通 `{ object: id }` 冒充，也不能传进 JSON DTO。方法可以并发，但 close 会先关闭新调用准入、请求合作取消、等待已发方法及反向 RPC 全部落地，再执行 owned 对象的异步 `PluginObject::close(ctx)`。borrowed 只释放这一 adapter 引用，不调用该 hook；实际对象仍须由插件或另一个明确 owner 持有。并发 JS `object.close()` 加入同一次尝试，失败后保留资源供重试，已关闭的 wrapper 不再接收业务调用。同一 domain 中不能重复接管同一个 owned Rust `Arc`，也不能在它仍有 borrowed adapter 时转为 owned。

回调是仅有 `call` 方法的对象接口：Rust 可用 `ObjectDescriptor::callback(type_name, ownership)` 声明，JS wrapper 另提供 `invoke(...jsonArgs)`。这里的 callback 由 factory 方法取得；它不是允许任意函数作为普通服务参数的隐式桥接。

反向接口由 JS 显式声明 adapter：

```js
import { adaptObject, adaptCallback } from '@cordis-verus/compat-cordis'

ctx.provide('resources', {
  object() {
    let closed = false
    const target = {
      read() { if (closed) throw new Error('closed'); return { value: 7 } },
      release() { closed = true },
    }
    return adaptObject(target, {
      typeName: 'example.Record', methods: ['read'], ownership: 'owned',
      dispose: target => target.release(),
    })
  },
  callback() {
    return adaptCallback(value => ({ echo: value })) // 默认 borrowed
  },
})
```

`adaptObject` 必须声明 ownership；owned 必须提供 `dispose(target)`，borrowed 禁止声明 disposer。多个 borrowed acquisition 各自拥有引用，一个 close 不影响其他引用；active borrowed 引用阻止 owned 接管，已被 owned 接管的同一 JS target 不能再次取得。方法表、getter 结果和 receiver 在取得时固定；元数据验证失败不会悄悄扩展白名单。已接管对象的 method getter 抛错时会尝试清理；失败的 owned disposer 留在 orphan journal，供真实 cleanup request 重试。

Rust factory 声明注入 `resources` 后可以使用：

```rust
let object = ctx.open_object("resources", "object", serde_json::json!([])).await?;
let value = object.call("read", serde_json::json!([])).await?;
object.close().await?;
let callback = ctx.open_callback("resources", "callback", serde_json::json!([])).await?;
let echoed = callback.invoke(serde_json::json!([value])).await?;
callback.close().await?;
```

`JsObject` 和 `JsCallback` 只属于取得它们的 Rust action；保存 clone 到实例或 worker 不会延长该 action 的寿命。action 主 Future 完成后，旧 context 禁止新调用；已经发出的 open 必须真实回复、登记取得的资源，再按 acquisition 次序倒序释放。遗忘 close 或丢弃 handle 不会丢弃 journal。borrowed 解除引用，owned 等待 JS disposer 成功；失败保留资源和相关依赖到 cleanup retry，成功释放的对象不重放。

Rust 显式 `JsObject.close()`/`JsCallback.close()` 遇到尚未落地的方法或关闭请求会返回 `ObjectBusy`，且不改变现有准入状态；先等待调用再 close。自动 journal 仍先关闭准入、等待方法的真实回复，再执行 disposer。对象析构不能像 stream `return()` 一样被用来唤醒仍在使用对象的方法。取消需要合作完成；一般 Promise 等待环没有通用强制解法。

## 调用、取消和清理

每次异步调用同时登记在 Rust provider session 和 JS caller Fiber 上。调用者卸载只请求取消它自己的调用，随后等待真实落地；不会取消其他消费者的调用。provider 撤销会请求取消本代工作，仍须等待已发出的 JS Promise 回应。取消不是超时、强杀或成功清理。

清理阶段保留已承诺的旧 publication。JS consumer 的 inverse 可以调用旧 Rust 服务和已取得的对象，Rust cleanup 也可以反调旧 JS 服务。服务 wrapper、对象和提取的方法绑定原 episode；旧句柄不会重定向到重启后的实例。清理阶段不允许新建跨 action 存活的 Rust 对象或流。框架可见的自卸载，以及等待当前或祖先资源操作的 close，会明确拒绝。

Fiber 清理先请求取消并收拢在途任务和流，再执行普通 inverse。**只有所有普通 inverse 成功，才进入对象释放阶段**：consumer 对象按 acquisition LIFO 关闭；随后该 Fiber 的 Rust sessions 才清理剩余对象、运行 backend cleanup 并 release。session 在 setup 被 poll 之前登记，partial setup 也拥有真实清理路径。普通 inverse 失败时保留对象和 Rust 实例，便于 retry 使用旧 handle；对象 close 失败时停止，保留它和更早取得的对象。这个晚释放阶段不宣称对象 close 与普通 effect inverse 混在同一个全局 LIFO 中。用户显式 close 可以选择更早的释放时机。provider 撤销会停止新准入，但不会提前销毁这些对象；正常 provider 清理仍等待 committed consumers。

DTO 仅接受 `null`、boolean、有限 number、string、无洞数组及普通对象。禁止 BigInt、undefined、Date、函数、accessor、Proxy、循环、symbol 和会被 JSON 静默丢弃的属性；不会执行 `toJSON`。反向 JS 方法返回 `undefined` 视为无返回值，映射为 `null`。需要精确大整数时约定十进制字符串。服务和对象方法的调用参数都是 JSON 数组；adapter、opaque wrapper 和 callback 即使嵌套在普通对象中，也会被 DTO 边界拒绝。

普通 SDK 未隔离的 Rust panic 会 fault 当前 domain，拒绝在途等待者，并标记清理未确认。应关闭相应 Worker/进程并重建；不能把 fault 当作正常 cleanup 或继续复用域。用户的无限 Future 仍可能让正常关闭一直等待。

## 验收与边界

`tests/node-compat/rust-interop.test.mjs`、`rust-streams.test.mjs` 和 `rust-objects.test.mjs` 使用独立编译的 addon，覆盖双向调用、流、对象和回调、Rust worker 唤醒、背压、隔离、取消落地、旧句柄、partial setup、晚到 acquisition、cleanup retry 与重入。`rust-host.test.mjs`、`rust-host-streams.test.mjs` 和 `rust-host-objects.test.mjs` 单独覆盖异常 JS 返回、精确 cleanup token、getter 快照、稀疏元数据、owned/borrowed 冲突和协议失败；它们不代替 Rust E2E。

此 SDK、JSON 转换、Future executor、N-API、JS 对象表和用户回调都是宿主实现边界；测试通过不把它们纳入 Verus 证明。共享 Driver 使用的 verified Kernel/action/publication 不变量仍由原有全内核 gate 检查。

剩余工作包括既有 typed Rust Runtime 的完整迁移、更广的显式接口与 ABI 合同、插件生态验收，以及这些宿主步骤到论文语义的 refinement。当前对象 adapter 不承诺任意句柄参数、跨 Worker 对象身份、自动 typed payload 转换或稳定 Rust 动态库 ABI。预编译产物的选择、校验和离线合包已有工具，各平台的实际构建、完整 release gate 与发布另行验收。

[性能工具](benchmarks.md)提供可重现的生命周期、服务调用、流和卸载测量，以及绑定源码和实际构建的报告/基线比较。性能数字应来自相应环境的实际报告；工具存在、短测或单元测试通过均不表示性能预算已验收。
