# 既有 typed Rust 插件接入 Node

`FactoryRegistry::register_typed` 可以把真实 `cordis::Plugin` 放进 Node 的同一张生命周期图。默认保持静态合同；`.with_service_updates()` 开启声明服务的 payload 更新和 availability；`.with_dynamic_children()` 进一步开启原 `publish/publish_checked`、`mount/mount_in`、`ServiceHandle` 与 typed 子插件。插件继续使用 `Setup` / `AsyncSetup` 的 `get`、`provide` 和清理注册；不创建另一个 `Runtime`，不把 typed payload 序列化后复制到另一张图。

## 注册与使用

同一个 `ServiceKey<T>` 必须在提供者、消费者与绑定表之间共享；重新执行 `ServiceKey::new("counter")` 会创建不同身份，即使名字相同也不能互换。

```rust
use cordis::{Plugin, ServiceKey};
use cordis_node::plugin::{
    FactoryRegistry, TypedFactory, TypedService,
    MethodDescriptor, MethodKind, PluginResult,
};
use serde_json::{json, Value};
use std::sync::{Arc, atomic::{AtomicI64, Ordering}};

struct CounterView;
impl TypedService<AtomicI64> for CounterView {
    fn methods(&self) -> Vec<MethodDescriptor> {
        vec![MethodDescriptor { name: "read".into(), kind: MethodKind::Sync }]
    }
    fn call_sync(&self, value: Arc<AtomicI64>, method: &str, args: Value) -> PluginResult<Value> {
        if method != "read" || args != json!([]) { return Err("invalid call".into()); }
        Ok(json!(value.load(Ordering::SeqCst)))
    }
}

fn register(registry: &mut FactoryRegistry) -> PluginResult<()> {
    let counter = ServiceKey::<AtomicI64>::new("counter");
    registry.register_typed(TypedFactory::new("example.provider", move |_| {
        // One Plugin definition per logical Fiber. This FnMut survives restart.
        let mut activations = 0;
        Ok(Plugin::new("provider", move |setup| {
            activations += 1;
            setup.provide(counter, AtomicI64::new(activations))?;
            setup.on_cleanup(|| Ok(()));
            Ok(())
        }).provides(counter))
    }).provides(counter, "counter", CounterView))?;
    registry.register_typed(TypedFactory::new("example.consumer", move |_| {
        Ok(Plugin::new("consumer", move |setup| {
            let value = setup.get(counter)?; // Original Arc, not a DTO copy.
            value.fetch_add(10, Ordering::SeqCst);
            setup.on_cleanup(move || {
                let _last_value = value.load(Ordering::SeqCst);
                Ok(())
            });
            Ok(())
        }).requires(counter))
    }).requires(counter, "counter"))?;
    Ok(())
}
```

在用户 addon 的 `createDriver()` 中把该 registry 交给 `NativeDriver::with_factories`。编译和装载过程与[普通 Rust factory](rust-node-plugins.md)一致。

```js
const ctx = new Context({ addon: '/absolute/path/my-addon.node' })
await ctx.rustPlugin('example.provider')
await ctx.rustPlugin('example.consumer')
await ctx.inject(['counter'], consumer => {
  console.log(consumer.counter.read()) // 11: same typed state the Rust consumer changed
})
await ctx.dispose()
```

仓库提供[实际 addon fixture](../crates/cordis-node/examples/typed_fixture/mod.rs)、[Node 示例](../examples/node/rust-typed.mjs)及[真实互通测试](../tests/node-compat/rust-typed.test.mjs)：

```sh
node scripts/build-node.mjs --offline
node examples/node/rust-typed.mjs
node --test tests/node-compat/rust-typed.test.mjs
```

## 身份与执行

`TypedFactory` 显式绑定 Rust key 身份、`TypeId`、外部服务名和接口视图。JS 为当前 Context 提供实际 port；NativeDriver 使用 setup ticket 对应的 **committed publication** 解析依赖，不回退到无 owner 的 root lookup。backend 再核对提供者、publication、原生 port、Rust key 与类型，克隆原来的 shared slot。Node realm 通过明确映射进入 typed Context，不比较两个独立分配器碰巧相等的 key 数字。

`TypedService<T>` 的方法取得槽位中同一个 `Arc<T>`，调用前释放内部记账锁。它可提供同步、异步、stream 或 object 方法；后两者复用已有资源协议。JSON DTO 是 JS 接口的显式视图，不能自动把一个纯 JS 服务变成任意 `T`。反向 typed JS proxy 尚未接入；需要反调 JS 时，异步接口 `call_async`（或资源的后续异步方法）可使用该次调用的 `PluginContext` 和已有 SDK。不要把 setup action 的 context 保存为永久调用凭证。

每个逻辑 Fiber 保存一份原始 `Plugin` 定义，直到 Driver 确认 Removed。重启创建新 episode，继续使用原 `FnMut` 闭包；不同 Fiber 的闭包独立。factory、配置或 port 绑定发生变化时，当前适配器明确拒绝复用旧定义；用新 Fiber 承载新配置。配置原地更新和动态重绑定不属于这一个静态合同。

## 动态值与 availability（显式启用）

在 `TypedFactory` builder 上调用 `.with_service_updates()`，允许原插件使用 `provide_checked`、`AsyncSetup::set` 和 `AsyncSetup::refresh`。未调用它的 factory 继续拒绝这些操作，即使插件忽略错误，setup 也不会被记录为成功。

```rust
// Inside the real Plugin setup callback:
let value = setup.provide_checked(counter_key, Counter::new(5), |value, consumer, injection| {
    // The Context contains the explicit realm mapping for this factory's bindings.
    let _consumer_port = consumer.port(counter_key);
    value.current >= injection["minimum"].as_i64().unwrap_or(0)
})?;
let updates = setup.to_async();
// Store `updates` in a declared controller service or an owned background task.
// A current controller method can replace the original shared slot:
updates.set(counter_key, Counter::new(12))?;
// Use refresh after changing predicate state held outside that slot:
updates.refresh()?;
```

检查配置来自消费者对该服务的 injection/intercept 配置，并要求是有限 JSON 数据；它不是消费者插件的普通 config。配置采用最近一层的服务配置，无隐式 schema merge。JS 消费者可以这样声明：

```js
const consumer = await ctx.plugin({
  inject: { counter: { minimum: 10 } },
  apply(c) { console.log(c.counter.read()) },
})
// An inherited service configuration also applies to a typed consumer.
await ctx.intercept('counter', { minimum: 10 }).rustPlugin('example.consumer')
```

每次 predicate 调用携带 Driver 实际发出的 availability ticket；Node adapter 核对 session、publication、port、ServiceKey 映射以及当前 ticket。失效或重放的 ticket 不会进入 predicate。检查是纯同步回调，panic 返回 unavailable；predicate 不应取得资源、修改服务或发起生命周期操作。已排队的值更新会使旧观察返回 unavailable，随后用新通知重新检查。普通 JS `Service.check` 保持原来的零参数调用约定。

`set` 替换同一个 `SharedSlot` 的 payload，保留当前 publication 身份。后续 `setup.get(key)` 和 JS 接口读取新 `Arc<T>`；消费者已经保存的 `Arc<T>` 仍是原值。消费者清理继续按其 episode 的 committed provider 读取同一个槽位，不切换到新 provider。`refresh` 会重新检查该 provider 的已发布端口；通知按 session/generation 过滤，旧 episode 的迟到通知不能影响重启后的实例。

同步 Rust 方法在返回前把通知交给 Node 检查队列，因此随后 `await ctx.settle()` 会等待由更新引起的生命周期变化。异步方法在 managed job 落地时处理通知。后台 Rust 线程通过现有 N-API wake 通知，线程本身的完成仍需插件登记真实 cleanup；框架不会替未登记的线程伪造 join。

保存的 `AsyncSetup` 是原 Runtime 的 **episode 句柄**，不是永久有效的 setup action 凭证。在 Loading/Active 期间可更新声明的槽位；撤销、清理或完成后，`set/refresh` 明确拒绝，旧句柄不重定向到下一代。异步 `TypedService::call_async` 应同时检查本次 `PluginContext` cancellation，参见 fixture 中的 `LiveControlView::setAsync`。这项能力不会延长 `PluginContext` 的反调 JS 权限。

真实 [typed fixture](../crates/cordis-node/examples/typed_fixture/mod.rs) 和[两个 profile 的回归](../tests/node-compat/rust-typed-live.test.mjs)覆盖更新后 Pending/Active 转换、不同 injection 配置、realm 隔离、相同 committed slot 与旧 Arc、旧代次拒绝、部分 setup 失败、predicate panic、失败清理保留以及票据防伪与重放。

## 原 `requires_with_config` 声明

`TypedFactory::requires_with_config(key, name, json)` 把配置依赖预先登记在 Node factory 上，原插件继续使用 `Plugin::requires_with_config(key, json)`。两处应共享同一个 JSON 值。这样消费者处于 Pending、尚未执行 factory/setup 时，原 `provide_checked` predicate 已能取得正确配置。

```rust
let declaration = serde_json::json!({ "minimum": 10 });
let plugin_declaration = declaration.clone();
registry.register_typed(
    TypedFactory::new("example.configured-consumer", move |_| {
        Ok(Plugin::new("configured-consumer", move |setup| {
            let current = setup.get(counter)?;
            // Use the original typed Arc after availability admits this episode.
            let _value = current.load(Ordering::SeqCst);
            Ok(())
        }).requires_with_config(counter, plugin_declaration.clone()))
    }).requires_with_config(counter, "counter", declaration)
)?;
```

配置以原 `ServiceKey` 身份对应。第一次可启动时，adapter 在进入原 setup callback 前核对真实 Plugin 的依赖配置与预登记配置，包括嵌套 JSON；不一致返回 `StaticInjectionConfigurationMismatch`。没有预登记却使用原 `requires_with_config` 的 Plugin 继续被默认静态入口拒绝。这不会通过伪造 setup 或提前执行 factory 来绕过 Pending。

已登记的配置优先于 Context 上继承的服务 intercept；显式 JSON `null` 也是声明，会覆写继承值。普通 `.requires(key, name)` 继续采用已有的继承配置。无隐式合并或 schema 转换，provider predicate 自己判断配置是否可用。JSON 类型不满足 predicate 时，消费者保持 Pending。注册的配置与 Node 预配置都不替代 Rust `ServiceKey`/`TypeId`、realm 和 committed publication 检查。

本入口支持 **每个注册 factory 固定的配置依赖**。如果 Plugin 的配置依赖是根据每个 Fiber 的普通 config 动态生成的，需要新的 descriptor 预检协议；当前不提供这种模式。修改已安装 Fiber 的 factory/config/port 声明仍会被拒绝，应创建新 Fiber。这个限制避免在 availability 已按一种配置放行后，再执行另一种配置的 Plugin。

[配置依赖回归](../tests/node-compat/rust-typed-injection.test.mjs)使用真实原 Plugin，覆盖启动前 Pending、通知后激活、精确声明错配、显式 null、schema 不匹配、realm 隔离、失败 consumer 的 committed slot 保留、显式恢复和旧服务句柄失效。

## 动态 publication 与子插件

在 factory 上显式调用 `.with_dynamic_children()`，并用 `.child_service(key, name, view)` 登记子插件可能提供的接口。父插件已有的 `requires/provides` 绑定也进入目录；`child_service` 本身不为父插件增加依赖或发布服务。每个子插件仍通过它自己的原 `Plugin` 声明决定实际依赖与提供关系，配置依赖直接来自该 child 的 `requires_with_config`，在分配和 Pending availability 检查前完成预检。

下面沿用前文的 `CounterView`：

```rust
let counter = ServiceKey::<AtomicI64>::new("dynamic-counter");
registry.register_typed(
    TypedFactory::new("example.dynamic", move |_| {
        Ok(Plugin::new("dynamic-owner", move |setup| {
            // This is the original ServiceHandle and original SharedSlot.
            let handle = setup.publish_checked(
                counter,
                AtomicI64::new(12),
                |value, _consumer, injection| {
                    value.load(Ordering::SeqCst)
                        >= injection["minimum"].as_i64().unwrap_or(0)
                },
            )?;
            setup.mount(
                Plugin::new("typed-child", move |child| {
                    let current = child.get(counter)?;
                    assert!(Arc::ptr_eq(&current, &handle.get()?));
                    child.on_cleanup(move || {
                        let _last = current.load(Ordering::SeqCst);
                        Ok(())
                    });
                    Ok(())
                }).requires_with_config(counter, json!({"minimum": 10})),
            )?;
            Ok(())
        }))
    })
    .child_service(counter, "counter", CounterView)
    .with_dynamic_children(),
)?;
```

```js
await ctx.rustPlugin('example.dynamic')
await ctx.settle()
await ctx.plugin({
  inject: { counter: { minimum: 10 } },
  apply(c) { console.log(c.counter.read()) },
})
```

原 `AsyncSetup` 可保存在声明的 controller 服务中，在 owner 当前 episode 的 Loading/Active 阶段创建新 publication 或挂载子插件。`TypedService` 的异步方法也可这样调用；后台线程通过已有 wake 机制提交请求。controller 必须使用原句柄，并为自己的后台任务登记 cleanup；它不保存 setup action 的永久权限。

可直接运行的 [dynamic fixture](../crates/cordis-node/examples/typed_fixture/dynamic.rs) 展示 controller、checked publication、typed reader、隔离 child 和 pending setup：

```js
// With the repository's interop-fixture.node addon:
await ctx.rustPlugin('fixture.typedControl')
const owner = await ctx.rustPlugin('fixture.typedDynamic')
const manager = ctx.typedDynamicManager
manager.publish('first', 3)
await ctx.settle()
console.log(ctx.typedDynamicValue.read()) // 3
manager.set('first', 8)
manager.dispose('first')
await manager.join('first')
manager.publish('second', 12, true) // A new provider child and publication.
await ctx.settle()
await owner.dispose()
```

每次 `publish` 创建**真实 native child Fiber**，其真实 setup ticket 发布原 SharedSlot；不会在父节点上模拟 key map。该 child 显式依赖父节点的私有 owner-anchor。anchor 使用真实 fresh Rust key、每个逻辑 Fiber 独立的服务名和隔离 realm，不能与目录中的用户服务混同。初始化完成以 native Active 为准；`dispose` 请求实际撤销；只有真实 cleanup 与 Removed 后 `finished/join` 才确认完成。分配前拒绝和分配后失败分开处理，已分配的 child 必须经过实际退休和清理。

`mount_in` 的原 Rust realm 经显式映射进入同一 Node 图，Rust 与 Node realm 的数值不被当成相同身份。子插件继承父插件的实际依赖端口及配置；隔离时保留父端口，并解析子 Context 对应端口，排除子插件自身提供的同一个端口，保持原 Runtime 的保留规则。嵌套 child 继续拥有原 `FnMut` 定义；失败或 Pending 不等于删除。

`ServiceHandle::set/refresh` 更新原 slot 与 availability，旧 `Arc<T>` 保留原 payload，已 committed 的消费者在清理时仍读取其旧 provider。同步 controller 方法在返回前提交本次 child 工作和通知，随后 `ctx.settle()` 等待图变化。过期 owner、setup 取消或 teardown 后的创建请求被拒绝，不转发到新 episode。恢复事务中只有真实仍在执行的 setup 可创建资源，普通后台请求和恢复 coordinator 没有该权限。

消费者 action 不能等待其 committed provider 或 provider 祖先的 publication `join`；owner setup 也不能等待依赖其自身 anchor 的 publication 完成。服务方法、对象方法和流操作的 native caller scope 在每次 Future poll 时执行此检查，返回 `ReentrantServiceJoin`，不假装 publication 已完成。清理失败仍保留真实节点和依赖；原 `FnOnce` inverse 不能重放。公开的 `ServiceHandle::errors` 和 join 错误用于观察失败，`finished == false` 仍表示尚未确认清理。

[双 profile 验收](../tests/node-compat/rust-typed-dynamic.test.mjs)覆盖原 Arc 共享、动态发布/撤销/再次发布、owner restart、发布冲突、checked availability 与两套 realm、嵌套隔离子插件、消费者清理屏障、pending setup 取消、旧句柄拒绝、自等待保护和不可重放的清理失败。

## 取消与清理

withdrawal 同时更新 SDK token 和旧 `AsyncSetup` 的 episode 状态。已经开始的 setup 必须真正落地，仍可登记其取得资源的 inverse；未开始的异步 setup 可以在取消后不再进入 body。用户 Future 如果永不完成，框架不会伪造完成。

普通 JS inverse 及对象清理成功之后，typed session 才执行原插件的 inverse。typed 与 JS 消费者都保留旧 publication，提供者的清理等它们完成。关闭 episode 与晚到 `on_cleanup` 注册使用同一把日志锁：inverse 要么进入日志被执行，要么因 episode 已关闭而拒绝。旧 `AsyncSetup` 不会重定向到下一代。

旧 API 的 inverse 是 **`FnOnce`**。执行失败或 panic 后无法再次调用同一个函数，因此 static executor 会持续记录失败，保留未执行 inverse、槽位及图中的依赖；`retryCleanup()` 继续返回失败，不能把已被消费的 callback 当成清理成功。此时需要应用处置失败的资源并重建相应隔离环境；关闭进程或 GC 也不等于确认外部资源已恢复。需要可重试清理时，可使用下面的显式 `FnMut` API，或普通 SDK 的 `PluginInstance::cleanup`。

`Setup` / `AsyncSetup` 的 `on_cleanup_retryable` 和 `on_cleanup_retryable_async` 接受并保留 `FnMut` 工厂。失败或受控 panic 后，Node 的显式 `retryCleanup()` 会让 typed bridge 调用 `StaticEpisode::retry_cleanup`，以新的尝试编号重跑失败操作；已成功的 inverse 不重复执行，更早的 inverse 和原槽位继续保留，直到确认成功。异步工厂每次产生新的 Future，插件作者负责处理部分外部效果，使重试安全。被丢弃的静态清理 Future 仍阻塞，不能通过此 API 重试。详细的可执行合同和测试见[清理协议](cleanup-protocol.zh-CN.md)。

既有 Plugin setup/cleanup 的受控 panic 仍按原执行器转换为失败；只有保留了显式可重试工厂的清理才能再次执行。接口视图、FFI 或其他未被旧执行器隔离的 panic 遵循 Node domain fault 合同。强制 abort 和任意不终止代码不在进程内隔离能力之内。

## 当前范围

支持静态 `requires/provides`、显式预登记配置的 `requires_with_config`、`get/provide`、同步或异步 setup/cleanup。`.with_service_updates()` 开启声明服务的 `provide_checked` 和 `set/refresh`；`.with_dynamic_children()` 同时开启服务更新、原动态 publication 与子插件。默认静态入口仍拒绝这些 opt-in 操作；setup 吞掉不支持操作的返回值也不会被记录为成功。

effect group、typed 配置更新 hook、任意纯 JS 服务自动转换成 `T`，以及 factory 按每个根 Fiber 配置动态生成依赖 descriptor，尚未接入这一 adapter。根 factory 的代码仍通过 Cargo 编译进 addon，修改 Rust 源码需要重新构建；Node 模块 HMR 不等于 Rust 动态库代码替换。普通 Rust Runtime 保持原有完整宿主入口。

`static_host` 不自建图、不持有第二份 publication lease，其公开入口要求嵌入方已验证 owner、generation、依赖和真实清理结果。Node 适配器执行这些检查；模块 API 本身不能成为绕过 Driver 的证明。任意回调、Future、槽位适配和 N-API 仍属于宿主边界，行为测试不构成整篇论文 refinement。
