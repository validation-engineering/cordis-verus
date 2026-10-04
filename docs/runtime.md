# Rust runtime 使用与边界

`cordis` 提供 typed service、异步初始化、effect iterator、动态子插件、事件、timer、配置树和 Rust factory 热更新。生命周期转移与 cleanup token 栈调用 `cordis-kernel` 的 Verus 实现；宿主的 future 调度、锁、payload、factory 和任意回调仍由普通 Rust 实现。具体证明义务见 [semantics.md](semantics.md)，上游对应见 [upstream-parity.md](upstream-parity.md)，配置用法见 [loader.md](loader.md)。

## 挂载、服务与生命周期

创建 `ServiceKey::<T>::new("name")` 后，将同一个 key 传给 provider 与 consumer。名称用于诊断；再次用相同名称创建 key 会得到不同身份。`Plugin::requires(key)` 声明依赖，`Plugin::provides(key)` 声明固定服务端口。`Setup::provide` 提交 payload，`Setup::get` 读取当前 activation 已 committed 的具体 provider，返回 `Arc<T>`。子插件还可以访问 runtime 为其继承的父依赖。

```rust
use cordis::{Context, Plugin, Runtime, RuntimeError, ServiceKey};

async fn application() -> Result<(), RuntimeError> {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let message = ServiceKey::<String>::new("message");

    runtime.mount(&context, None, Plugin::new("provider", move |setup| {
        setup.provide(message, "hello".to_owned())?;
        setup.on_cleanup(|| Ok(()));
        Ok(())
    }).provides(message))?;

    runtime.mount(&context, None, Plugin::new("consumer", move |setup| {
        let bound = setup.get(message)?;
        setup.on_cleanup_async(move || async move {
            println!("cleanup still reads {bound}");
            Ok(())
        });
        Ok(())
    }).requires(message))?;

    runtime.settle().await?;
    runtime.dispose_all()?;
    runtime.settle().await?;
    if let Some(error) = runtime.take_cleanup_errors().into_iter().next() {
        return Err(error);
    }
    Ok(())
}
```

消费者可以先于 provider 挂载：缺少依赖时保持 Inactive，`settle()` 仍可正常返回。依赖齐备后，runtime 安装 committed bindings 并进入 Loading；根 setup 和初始化 effect stages 完成、声明的 payload 都已提供后，才进入 Active 并向新消费者发布服务。Loading 中已经 provide 的值不会提前暴露为可解析服务。

服务撤回、target 变化、显式 restart 或退休请求会使 activation 进入 Unloading。provider 在新解析中撤下后，其值仍保留给当前 committed 消费者；恢复资源前必须通过消费者 barrier。`dispose(id)`、`cancel(id)` 和 `dispose_all()` 提交退休请求；调用方继续 `settle().await` 或 `join(id).await` 才会推进清理和删除。`join(id)` 驱动 runtime 并等待该 owner 的初始化/恢复完成，其他无关插件的 Pending 不阻挡其完成；它本身不提交退休请求。

## 异步 setup 与 effect iterator

`Plugin::new_async(name, |ctx: AsyncSetup| async move { ... })` 是异步初始化入口。`AsyncSetup` 为拥有所有权的 episode handle，支持跨 await 的 get/provide、cleanup、effect 与 child 注册。同步 setup 可以通过 `to_async()` 取得同一种 handle；`Runtime::owner_context(id)` 可取得现存 activation 的 handle。异步方法的注册操作返回 `Result`，应传播错误。

`Effect::new().step(...)` 构造有限的多阶段效果；每个 stage 接收 `AsyncSetup`，完成后返回 `Inverse::new(...)` 或 `Inverse::new_async(...)`。`EffectIterator` trait 支持自定义异步 iterator。`Setup::effect`、`AsyncSetup::effect` 与 `Runtime::effect(owner, ...)` 返回 `EffectHandle`，提供 cancel/dispose、initialized/finished、errors 和 join。

同一组内的 stages 顺序运行，已完成 stage 的 inverse 先收集，再允许下一 stage 开始；组内逆序逐个等待清理。不同 effect groups 可以交错初始化与恢复，某组 Pending 不阻止其他组推进。直接登记的 `on_cleanup`/`on_cleanup_async` 形成根 cleanup 组。`EffectHandle::join()` 等待该组结束；它不自行轮询 Runtime，调用方仍需驱动 runtime。

取消或丢弃 `EffectJoin` 只撤销该等待者，并立即注销其 Waker；不会取消 effect。`EffectHandle::cancel()` 才提交组取消请求。已开始并返回 Pending 的 stage 仍由 runtime 持有，等待返回并收集 inverse 后再恢复。根 setup 使用明确的未开始、排队、运行中和完成状态，只有尚未首次 poll 的 setup 可以直接撤销。等待者的 Waker 克隆、替换、析构和唤醒均在状态锁外执行。

取消发生时，在途的 setup/stage 继续到达可收集 inverse 的边界，随后停止后续 stages 并恢复已登记效果。每个新 stage 前都会重新检查当前依赖，而不是只在整段初始化开始时检查。`AsyncSetup::is_cancelled()` 支持协作退出；`ensure_active()` 用于在获取新资源前检查 owner/group 是否仍接受新效果。保留的 `CANCELLED` 结果仅在已取消的 episode/group 中视作协作终止，活跃 callback 返回它仍算失败。

完成的旧 episode 不接受新登记；即使 owner 用同一 ID restart，旧 `AsyncSetup` 也不能向新 activation 登记资源。在途 stage 获知取消后仍可登记已经产生效果的 inverse，使该效果被正常收回。框架不会强制终止永不完成的 future。

## Context、依赖继承与子组件

`context.isolate(key)` 为单个服务建立新 realm，其他服务保持原路由；`context.share(key, &other)` 显式共享一个服务 realm。插件挂载后 required/provided ports 与 realm 固定。同一 `(key, realm)` 被仍存在的 provider 占用时，第二个 provider 不能挂载，即便前者 Inactive 或正在退休。

`mount(&context, Some(parent), plugin)` 建立所有权关系。`Setup::mount`/`mount_in` 和 `AsyncSetup` 的同名方法可在 setup 或 effect stage 中动态创建子插件，返回 `ChildHandle`。请求在当前 callback 的 poll 返回后被处理；通过 handle 的 `id()`/`error()` 观察结果。

runtime 将父节点的实际依赖 ports 加入子节点声明，同时将相同 service key 在子 context 中的 realm 加入解析需求；子节点自身提供的端口会被排除。这样父依赖作为实际 committed binding 保持存活，显式隔离的子节点也能解析其新 realm。单纯的 parent 字段不把父节点变成 service provider，不能以所有权关系代替所需的服务依赖。

子组件创建登记一个位于对应 effect 组中的 inverse。该 inverse 执行到自身的 LIFO 位置时只请求 retire child，不等待 child 完成，符合论文 Def. 52 的注册逆操作。父节点可以继续其后的 inverse；child 的资源顺序由真实依赖守卫约束。父节点从 registry 删除仍须等待全部子节点删除，`settle()`/退休后的 `join(parent)` 提供完整子树完成边界。父节点 Unloading/已退休，或旧 episode/group 已取消时，拒绝新建子插件。

## 更新、替换与配置树

`Setup::set`、`AsyncSetup::set` 和 `Runtime::set(owner, key, value)` 只替换该 owner 已提供的 payload，provider ID 不变。先前返回的 `Arc<T>` 是旧值快照；需要共享可变状态时，服务类型应明确采用锁或原子字段。`Runtime::get` 返回的外部 Arc 没有登记 consumer，不能延长 provider 的资源生命周期。

`restart(id)`、`update(id, callback)` 和 `update_async(id, callback)` 保留 ID，并清理旧 activation 后启动新 activation。它们是额外宿主操作。`replace(id, plugin).await` 按退休、清理、删除、重新挂载执行论文配置 revision，返回永不复用的新 ID；直接替换不会重建旧子树。

`loader::Loader` 实现 JSON tree、group 启停、Include 文件、Schema/interception、typed metadata 与 FactoryRegistry。配置变更先验证整棵树并构造候选插件，再差分退休和重建，保留未变化节点；失败时使用旧 factory/config/scope 恢复已提交树。`load_file`/`poll_reload` 处理配置文件变化；同名 `register` 产生 factory revision，`reload` 更新 Rust 插件代码。具体配置和可取消事务协议见 [loader.md](loader.md)。这套接口不解释 JS、装载 npm 模块或复制 Node 模块缓存。

## 事件与 middleware

| 类型 | 调用与语义 |
| --- | --- |
| `Event<T, R>` | on/once/prepend/off/emit，`EventOptions` 控制 once 与顺序 |
| `Event<T, Option<R>>` | bail 返回第一个 Some，包括 Some(false)，未访问的 once 保留 |
| `AsyncEvent<T, R, E>` | parallel 同时轮询监听器并等待所有结果，按注册顺序返回成功值；错误/构造或 poll panic 汇总为 AggregateError；emit 等待同样的调度并丢弃值 |
| `AsyncEvent<T, Option<R>, E>` | serial 顺序等待，遇第一个 Some 或 error 即返回，后续 callback 不被构造 |
| `Waterfall` / `AsyncWaterfall` | around middleware 可以在 next 前后运行、转换结果或短路；next 只能调用一次，重复调用返回 NextCalledTwice |

`EventScope::Relevant(context.port(key))` 比较完整 key/realm；Global listener 绕过过滤。`emit_filtered`、`parallel_filtered`、`serial_filtered` 与 `run_filtered` 接收显式 predicate，可以结合应用自己的 scope metadata 进行路由。typed payload 和 continuation 替代动态事件参数与 JS middleware。

派发捕获监听器快照，然后在 registry 锁外调用 callback。once 在调用前原子 claim，重入/并发派发至多执行一次。subscription 的 `dispose()`/off 幂等；丢弃 subscription 不退订。将退订放入 owner 的 cleanup 后可以随 owner 生命周期取消后续注册可见性。

**退订不撤回已进入派发快照的普通 listener，也不会等待其 callback/future 结束。** 普通订阅没有自动 dispatch drain barrier；需要随插件退出等待 handler 时，使用新增的 `on_in` 绑定 Setup/AsyncSetup，或显式 `on_owned` 管理 close/drain。派发期间保存的服务 Arc 不形成 committed dependency；普通订阅跨 owner teardown 的进行中派发需要应用自己协调等待或取消；owned 订阅的 admission/drain 会等待已登记 handler、闭包/future 析构和 continuation lease。用户主动保留的返回值、payload、外部 service Arc 或 detached 任务仍不由 drain 延长生命周期。直接丢弃异步派发 future 会丢弃尚未完成的 listener futures，这不同于 runtime 对在途 setup/stage 的保留协议。同步 event 和同步/异步 waterfall 的 panic 传播给调用方；AsyncEvent 的 parallel/serial 将监听器 panic 转成错误。

## Timer

`timer::TimerService` 提供 timeout/set_timeout、interval/set_interval、sleep、ticks、debounce 和 throttle。`Setup` 与 `AsyncSetup` 提供对应的 owner-bound 便利方法，`timer()` 返回一个绑定该 activation 的 service；已有 service 可通过 bind/bind_async 绑定。TimerService clone 共享 scheduler，handle 是显式取消 token。

真实时间 service 使用一个 worker 执行定时 callback；interval 按 fixed delay 调度并跳过错过的 ticks。`TimerService::manual()` 与 `ManualClock::advance` 提供确定性测试驱动。`ticks().next()` 等待一个 tick，无 waiter 时不积累 ticks；关闭会拒绝待处理和后续 next。sleep 取消会唤醒并返回 Cancelled；debounce 保留最新 payload，throttle 支持 leading 和最新 trailing payload。

`TimerHandle::cancel` 阻止未来启动，外部 `cancel_and_join` 还等待进行中的 callback；owner cleanup 调用 service shutdown 并等待外部执行完成。**在同一个 service 的 callback 内调用 shutdown/cancel_and_join 只请求停止，不等待其他 callback**，以避免相互 join 死锁；从 callback 外再次 shutdown/join 才是完整结束屏障。同步 throttle 的 leading callback 在调用者线程运行，因此可能与 worker callback 并行。callback panic 被记录，后续 shutdown 返回相应 TimerError；这里没有 arbitrary callback 正确性证明。

## 具体可逆资源与条件证明

`resources::ReversibleStore` 是实际调用 Verus `resources::Store` 的整数 cell 资源。`transaction().write(index, value)` 取得独占 owner 并记录不允许复制的 inverse；同一 owner 可以嵌套写，其他 owner 的冲突写被拒绝。rollback 按逆序消费 token，错误的顺序保持 store 与 token 供以后重试，独立 cell 的修改得到保留。`Setup::reversible`/`AsyncSetup::reversible` 将 rollback 绑定到 owner cleanup。单独创建的 transaction 需要显式 rollback，drop 不自动回滚。

Verus 证明这些具体 forward/inverse 操作的状态变化、恢复与独立 cell 的交换律。`calculus` 还条件证明有限 sequence 的 observational recovery、inverse 与独立外部 trace 的交换，以及独立 effect groups 的交换；前提包括 inverse witness、观测等价及必要的独立性。它们不会为普通 I/O closure 自动生成 witness。ReversibleStore 的 Mutex、journal 编排与 owner 绑定仍是经过测试的宿主代码。

## 驱动、错误与运行示例

Runtime 由持有 `&mut Runtime` 的调用方驱动，没有自己的后台 executor。Send 允许外部 executor 移动 future；TimerService 单独管理其 worker。丢弃 settle/join 暂停驱动并保留在途 setup/cleanup，之后继续驱动会更新 waker。直接 `Runtime::replace` 不是可回滚事务，取消可能留下正在退休或新插入的 fiber；通过 ids/name/phase 检查并继续驱动。Loader 对自己的 mutation 另外保存 pending transaction，支持 recover。

setup/stage 返回 Err，或其 callback factory/poll panic，会锁存失败并清理已登记 inverse；显式 restart/update/replace 才重新尝试。cleanup 的 Err/panic 记入 `take_cleanup_errors()`，继续剩余清理；EffectHandle 还提供本组 errors。`settle()` 成功不表示每个外部 inverse 都正确恢复资源，应检查 cleanup errors。保留 inverse 的调度机制也不能恢复在登记 inverse 前就被任意 callback 破坏的外部状态。

单独丢弃 Runtime 不执行异步 inverse。没有公平轮询、future 终止和有效 inverse witness，安全性证明不会变成任意应用必然退出的保证。内核 ID 单调递增，保留 identity tombstone；失效 binding 和已删除声明会自动或显式回收。同一节点反复 activation 不再无限累积 binding 历史，但全新 ID 的累计数量仍影响空间与节点扫描成本。

以下例子使用标准库构造最小 executor，也可由应用已有的 executor 驱动：

- [basic.rs](../crates/cordis/examples/basic.rs)：typed service 与依赖清理。
- [async_lifecycle.rs](../crates/cordis/examples/async_lifecycle.rs)：异步 setup、多阶段 effect、动态子组件与逆序恢复。
- [config_reload.rs](../crates/cordis/examples/config_reload.rs)：Include、隔离、fresh identity、文件重载与 group 禁用。

分别运行 `cargo run -p cordis --example basic`、`cargo run -p cordis --example async_lifecycle`、`cargo run -p cordis --example config_reload`；根目录 `./scripts/check.sh` 执行正式验证、测试、示例和负向变异检查。计数以当前 revision 的实际检查报告为准。

## 维护与集成接口

事件新增显式 `on_owned/on_in` admission/drain；与普通 snapshot 订阅的差异、析构和 continuation lease 见 [events.md](events.md)。Loader 可显式 prepare_save/commit_save/save，保留 Include 来源并检测冲突，见 [loader.md](loader.md)。

`Runtime::snapshot` 提供状态、缺失依赖、在途 effect 与消费者恢复屏障的 JSON/DOT 诊断；`compact` 回收失效绑定和已删除声明，节点 ID 不复用。`shutdown().await` 等待清理并汇总 lifecycle/setup/cleanup 错误，取消后可继续。自动维护策略与 tombstone 限制见 [diagnostics.md](diagnostics.md)。
