# 既有 typed Rust 插件接入 Node

`FactoryRegistry::register_typed` 可以把真实 `cordis::Plugin` 的**静态服务子集**放进 Node 的同一张生命周期图。插件继续使用 `Setup` / `AsyncSetup` 的 `get`、`provide` 和清理注册；不创建另一个 `Runtime`，不把 typed payload 序列化后复制到另一张图。

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

## 取消与清理

withdrawal 同时更新 SDK token 和旧 `AsyncSetup` 的 episode 状态。已经开始的 setup 必须真正落地，仍可登记其取得资源的 inverse；未开始的异步 setup 可以在取消后不再进入 body。用户 Future 如果永不完成，框架不会伪造完成。

普通 JS inverse 及对象清理成功之后，typed session 才执行原插件的 inverse。typed 与 JS 消费者都保留旧 publication，提供者的清理等它们完成。关闭 episode 与晚到 `on_cleanup` 注册使用同一把日志锁：inverse 要么进入日志被执行，要么因 episode 已关闭而拒绝。旧 `AsyncSetup` 不会重定向到下一代。

旧 API 的 inverse 是 **`FnOnce`**。执行失败或 panic 后无法再次调用同一个函数，因此 static executor 会持续记录失败，保留未执行 inverse、槽位及图中的依赖；`retryCleanup()` 继续返回失败，不能把已被消费的 callback 当成清理成功。此时需要应用处置失败的资源并重建相应隔离环境；关闭进程或 GC 也不等于确认外部资源已恢复。需要可重试清理时，应使用普通 SDK `PluginInstance::cleanup` 并显式保存重试状态。

既有 Plugin setup/cleanup 的受控 panic 仍按原执行器转换为失败；清理 panic 同样不可重试。接口视图、FFI 或其他未被旧执行器隔离的 panic 遵循 Node domain fault 合同。强制 abort 和任意不终止代码不在进程内隔离能力之内。

## 当前范围

支持静态 `requires/provides`、`get/provide`、同步或异步 setup、同步或异步 cleanup。`publish`、子插件、effect group、`set/refresh`、`provide_checked`、`requires_with_config` 和配置更新 hook 尚未接入这个 adapter，均明确拒绝；setup 期间忽略不支持操作的返回值，也不会使该次 setup 成功。

这是真实旧 API 的一个同图实现切片，不是完整 typed Runtime 迁移。动态 publication、availability/check 协议、Loader 更新、更完整的 context/realm 映射与反向 typed JS 服务仍需逐项接入。普通 Rust Runtime 保持其原有完整宿主入口和合同。

`static_host` 不自建图、不持有第二份 publication lease，其公开入口要求嵌入方已验证 owner、generation、依赖和真实清理结果。Node 适配器执行这些检查；模块 API 本身不能成为绕过 Driver 的证明。任意回调、Future、槽位适配和 N-API 仍属于宿主边界，行为测试不构成整篇论文 refinement。
