# 既有 typed Rust 插件接入 Node

`FactoryRegistry::register_typed` 可以把真实 `cordis::Plugin` 的**声明式服务子集**放进 Node 的同一张生命周期图。默认保持静态合同；显式启用 `TypedFactory::with_service_updates()` 后，可更新已声明服务的 payload 并使用动态 availability。插件继续使用 `Setup` / `AsyncSetup` 的 `get`、`provide` 和清理注册；不创建另一个 `Runtime`，不把 typed payload 序列化后复制到另一张图。

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

## 动态 publication 的后续实现合同

`Setup::publish` / `AsyncSetup::publish` **尚未接入 Node adapter**。原 Rust Runtime 会创建独立 provider child，并用显式 owner-anchor 依赖保留父插件资源；`ServiceHandle` 同时表示该 child 的初始化、撤销与真实清理结果。把它改写成 owner 上的 `provide/revoke` 或一个可删除的 key map，会丢失这些语义。

后续实现需要一套同图协议，至少同时满足以下合同：

| 阶段 | 必要行为 | 必须验证的边界 |
| --- | --- | --- |
| 声明 | 区分始终存在的 `provides` 与允许动态发布的 typed key/interface；明确允许的名称、类型和 realm。 | 未声明 key、同名不同 ServiceKey、端口冲突不得发布。 |
| 请求 | `publish` 返回原 ServiceHandle，把原 SharedSlot 和 owner episode 绑定的请求交给外部 host；不创建第二个 Runtime。 | 请求必须有独立身份；取消或重启后的晚到请求不得挂到下一代 owner。 |
| 分配 | 在当前 NativeDriver 中分配真实 child，建立显式 owner-anchor 依赖。child 的可见性等待 owner 初始化完成。 | ownership 不替代服务依赖；父 setup 内等待这个 child 初始化仍不能伪造完成。 |
| 发布 | child 的真实 setup ticket 绑定原 typed slot、View、publication 和 native port。JS 与 Rust 消费者使用这个 child 的 committed publication。 | 导入失败、publish 冲突、取消中的部分 setup 都必须保留已取得资源的 inverse。 |
| 撤销 | handle.dispose 关闭新业务准入，由同一 Driver 撤销 child、等待所有 committed 消费者和资源调用落地。 | 不能在依赖自身的 consumer action 中等待 handle.join，造成自等待。 |
| 完成 | 只有 child 的真实 cleanup 成功后，handle.join/status 才报告完成；父清理等该 anchor 的所有使用者完成。 | FnOnce inverse 失败必须保持 sticky failure；进程退出和 GC 不代表恢复成功。 |
| 更新 | handle.set/refresh 只影响这次 publication 的 SharedSlot/check，并按 owner generation 与 child/publication 身份过滤通知。 | 旧 handle 不转向替代 publication；旧 Arc 和旧 committed lease 仍保留到实际释放。 |

实现前还需要明确 Node host 对“无活跃 Rust action 的后台 publish/dispose”的事务排队，以及已开始的请求如何与 shutdown、ConfigEditor revision、失败恢复互相等待。不能借用已完成的 setup token 或在恢复 coordinator 中任意新增资源。应先补齐 queued request → native child → typed child session →真实 cleanup completion 的单向状态记录，再开启原 API 的 feature gate。

验收应包括真实 JS 和 typed Rust 消费者同时保留一个动态 publication、在消费者清理挂起时 dispose/re-publish、owner restart、发布冲突、异步 setup 取消、失败清理不伪造 join 成功，以及旧句柄和晚到通知。当前 `with_service_updates` 和配置依赖能力不表示这些验收已完成。

## 取消与清理

withdrawal 同时更新 SDK token 和旧 `AsyncSetup` 的 episode 状态。已经开始的 setup 必须真正落地，仍可登记其取得资源的 inverse；未开始的异步 setup 可以在取消后不再进入 body。用户 Future 如果永不完成，框架不会伪造完成。

普通 JS inverse 及对象清理成功之后，typed session 才执行原插件的 inverse。typed 与 JS 消费者都保留旧 publication，提供者的清理等它们完成。关闭 episode 与晚到 `on_cleanup` 注册使用同一把日志锁：inverse 要么进入日志被执行，要么因 episode 已关闭而拒绝。旧 `AsyncSetup` 不会重定向到下一代。

旧 API 的 inverse 是 **`FnOnce`**。执行失败或 panic 后无法再次调用同一个函数，因此 static executor 会持续记录失败，保留未执行 inverse、槽位及图中的依赖；`retryCleanup()` 继续返回失败，不能把已被消费的 callback 当成清理成功。此时需要应用处置失败的资源并重建相应隔离环境；关闭进程或 GC 也不等于确认外部资源已恢复。需要可重试清理时，应使用普通 SDK `PluginInstance::cleanup` 并显式保存重试状态。

既有 Plugin setup/cleanup 的受控 panic 仍按原执行器转换为失败；清理 panic 同样不可重试。接口视图、FFI 或其他未被旧执行器隔离的 panic 遵循 Node domain fault 合同。强制 abort 和任意不终止代码不在进程内隔离能力之内。

## 当前范围

支持静态 `requires/provides`、显式预登记配置的 `requires_with_config`、`get/provide`、同步或异步 setup、同步或异步 cleanup；显式 opt-in 支持已声明服务的 `provide_checked` 和 `set/refresh`。`publish`、子插件、effect group 和配置更新 hook 尚未接入这个 adapter，均明确拒绝；setup 期间忽略不支持操作的返回值，也不会使该次 setup 成功。

这是真实旧 API 的一个同图实现切片，不是完整 typed Runtime 迁移。创建/撤销动态 publication、Loader 更新、更完整的 context/realm 映射与反向 typed JS 服务仍需逐项接入。当前更新同一个 publication 的槽位及 availability 不等于支持 `Setup::publish` 的动态 provider 子图。普通 Rust Runtime 保持其原有完整宿主入口和合同。

`static_host` 不自建图、不持有第二份 publication lease，其公开入口要求嵌入方已验证 owner、generation、依赖和真实清理结果。Node 适配器执行这些检查；模块 API 本身不能成为绕过 Driver 的证明。任意回调、Future、槽位适配和 N-API 仍属于宿主边界，行为测试不构成整篇论文 refinement。
