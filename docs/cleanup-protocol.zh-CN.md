# 清理确认与依赖释放

[English](cleanup-protocol.md) | 简体中文

本指南审查一条合同：执行器必须先对已接纳的清理给出明确结果，共享生命周期 API 才能
释放该 episode 的 committed 依赖。它把实际使用的 `LifecycleActions` 协议接到内核
守卫，以及 Node 和 Rust 的真实完成路径。限定范围的协议安全合同现已覆盖请求、
结果确认、依赖保留、显式重试与旧票据拒绝，并组合到真实清理 API 的有限执行上。
这组合同已在 [A07 / F1](adoption-plan.zh-CN.md) 范围内闭合；调用执行、外部 inverse
效果及不受限的宿主 refinement 仍是独立工作。
[论文清单](paper-obligations.json)仍有 **18 项 partial 和四项未完成集成义务**。

## 从论文条款到可执行协议

论文 §4.2.2 的定义 54 与 L-Unload（第 36–37 页）区分两项职责：执行 accumulator
期间保留消费者的 committed 视图，以及 provider 仍被依赖时推迟它的恢复。第 37 页
明确把丢弃 committed 视图作为 L-Unload 的最后一步。

| 审查条款 | 与执行代码的连接 | 边界 |
| --- | --- | --- |
| **BindingPersistence** | `Kernel::begin_cleanup` 保留 committed 绑定，`Kernel::finish_cleanup` 才释放它们；`LifecycleActions` 在调用 finish 前检查匹配的清理确认。 | 协议把报告与确切的未完成票据匹配，不证明任意 inverse 确实成功。 |
| **RestorationGuard** | 清理接纳调用真实内核守卫；provider 仍被存活消费者的 committed 视图引用时会被拒绝。共享 API 还用 owner 自身未完成的 action 阻止该 owner 的清理接纳。 | 依赖顺序不等于 parent/child 生命周期顺序，也不是调度定理。 |
| **先逆操作，后释放** | 清理 action 必须先变为显式 outcome，finish 才能释放 commitment；失败 outcome 持续阻塞，直到显式重试。 | Rust 的 `Drained` 确认工作已消耗，不代表恢复成功，不能替代论文的 inverse 定律。 |

粗体名称是项目的审查标签，不是新论文命题。底层投影及独立的具体逆操作执行结论，见
[PR-01](paper-review-guide.zh-CN.md#pr-01-episode-保留其已提交的-provider-身份)
和[进展合同](progress-contracts.zh-CN.md)。本里程碑不使任何论文条目完成，也不为
任意回调建立推论 69。

## 沿真实调用链审查

1. [LifecycleActions](../crates/cordis-kernel/src/lifecycle_actions.rs) 组合
   setup/cleanup 接纳、[ActionLedger](../crates/cordis-kernel/src/action_ledger.rs)
   票据消费、outcome receipt 与受保护的 finish。这些是接受 Verus 检查的内核源码中
   的可执行 Rust 函数，不是另一份 dispatcher 的平行模型。
2. [shared::LifecycleDriver](../crates/cordis-driver/src/shared.rs) 现在持有
   [LifecycleState](../crates/cordis-kernel/src/lifecycle_state.rs)。这个经过验证的类型
   一起构造并拥有 Kernel 和 action 协议；所有公开变更保持两者的不变式。宿主只能取得
   只读 Kernel 视图，不能向其清理方法传入另一个 Kernel。`pending_views` 仍仅用于
   序列化，不授予转换权限。生产 Driver 通过此类型已验证的 `execute_cleanup`
   分派清理命令；受管资源释放也满足同一个 `cleanup_step` 合同。
3. [Driver::complete](../crates/cordis-driver/src/lib.rs) 对 Node 清理记录
   `Succeeded` 或 `Failed`；失败返回时保留资源。成功调用共享状态的
   `finish_cleanup_resources`，其实现位于
   [cleanup_release.rs](../crates/cordis-kernel/src/cleanup_release.rs)：检查当前清理
   凭据和注册表所属域，完整检查并执行资源批次，然后调用实际 Kernel 的受保护 finish。
   普通宿主随后按返回的 slot 删除不透明值句柄，并更新自身记录。
4. [Domain.dispatch / Fiber._cleanup](../packages/compat-cordis/runtime.js)
   执行真实回调并发送完成报告。独立的 Rust
   [Runtime::poll_settle](../crates/cordis/src/runtime.rs) 通过经过验证的
   `CleanupJournal` 管理真实 inverse。保留的失败报告 `Failed`；日志排空后报告
   `Succeeded`，如果有已消耗的 `FnOnce` 失败则报告 `Drained`。

清理接纳预先分配 Pending receipt；completion 原位更新它，不在消费 action 后再分配
新 receipt。setup 完成不能代替 cleanup 完成。票据标识确切的 domain、owner、generation、action
和 kind；重复、类型错误或过期完成不能授权新的尝试。取消不会悄悄丢弃已有 setup
票据，因为它的返回结果仍可能带有必须收集的 inverse。

## 真实清理 API 的组合安全性

[`cleanup_protocol.rs`](../crates/cordis-kernel/src/cleanup_protocol.rs) 为生产共享
dispatcher 提供 `cleanup_step` 合同。`run_cleanup` 对每条命令调用这个同一入口，
并从实际调用构造状态历史。历史是编译时擦除的 `Ghost` 数据；运行时只保留命令结果。
被拒绝的命令保持其入口状态，循环继续执行，保留此前成功命令的变化，不回滚整个批次。

| 义务 | 可执行合同与组合结论 |
| --- | --- |
| 请求接纳 | `begin_cleanup` 公开 action 容量／owner 与 Kernel 守卫的精确接受条件。未完成 setup 阻止清理；成功请求保留绑定并签发下一个 action 身份。generation-zero reservation 有自己的接纳规则。 |
| 成功／失败确认 | `complete_cleanup` 精确匹配未完成清理凭据的 domain、owner、generation、action 与 kind。`Succeeded` 或策略特定的 `Drained` 可授权 finish，`Failed` 不可。`release_has_accepted_report` 在执行入口尚无释放许可的前提下，推出释放前存在同一 owner、当前 generation 的已接受授权报告。 |
| 依赖保留 | `binding_at` 将具体绑定保持到该消费者成功释放之前。真实 Kernel 的顺序不变式保证 provider 仍注册、未恢复且不能开始清理；其他消费者可独立完成。 |
| 显式重试 | `retry_cleanup` 要求失败凭据，保持 Kernel 并签发新 action。`failed_prefix_retains_dependencies` 覆盖没有新接受授权报告的任意有限前缀，包括反复失败、重试及其他 owner 的操作。 |
| 旧票据拒绝 | `consumed_ticket_never_returns` 证明已消费清理票据不会重新出现，之后用它报告任何 outcome 都被拒绝。拒绝保持一起拥有的 Kernel／协议状态。 |

定理覆盖从真实良构状态出发，由 Request、Report、Retry、Release、SettleSetup、
Withdraw、Retire 和 Remove 构成的任意有限序列。受管 `finish_cleanup_resources`
也证明 `cleanup_step`，同时保留更强的资源批次合同与精确错误，因此可以接入相同的
控制历史推理。新 episode 激活不在此命令集合内；真实 `begin` 方法另外保持票据
历史合同，回归测试覆盖跨真实 episode 重启的旧回执拒绝。

历史从这个 API 边界开始，并非从整个应用启动开始。回调调用及其外部效果不是这些
历史步骤，报告仍作为输入。结论是有限前缀安全，不是公平调度或最终排空，也不使
整个 F1 或论文未完成的集成义务关闭。canonical 负控
`cleanup-dispatch-promotes-failure` 与 `cleanup-dispatch-bypasses-receipt`
直接变异真实 dispatcher 的这两项合同。局部选定证明实验与完整发布负控门槛仍分开。

## 真实资源批次在释放 commitment 之前接受检查

受管租约记录实际消费者 owner 和 generation；真实 Driver 为下一次接纳的 episode
获取这些租约。`PublicationRegistry` 绑定 Driver 的 domain。普通未标记租约不能
被受管清理消费；携带不同 domain 的注册表即使有相同的本地 publication／lease ID，
也会被拒绝。这里检查 domain 数值；实际 Driver 的 domain 唯一分配仍属于宿主责任。

[`PublicationRegistry::cleanup_batch`](../crates/cordis-kernel/src/publication_cleanup.rs)
检查租约消费者、publication 的 owner/generation、撤销和保留状态、重复项以及剩余
持有者。它还对照注册表检查**完整性**：不能遗漏该消费者 episode 的租约，也不能
遗漏该 owner/generation 仍保留的 publication。调用者不需要假设清单正确。

整个预检查通过后才释放租约和回收 publication。可执行合同给出精确接受条件、拒绝
时注册表完全不变、精确的 publication/slot 返回结果、其他资源保持，以及
`episode_resources_cleared`。组合入口随后释放 committed 绑定并证明实际 L-Unload；
generation-zero reservation 分支仍保留其独立的 Kernel 不变合同。批次被拒绝时，
Kernel、协议凭据和注册表都保持**进入 finish 时**的状态。此前已记录的成功回调
报告仍然保留；该定理不回滚更早的 completion 或外部回调效果。

[回归案例](../crates/cordis-driver/tests/cleanup_resources.rs) 覆盖失败／重试、旧确认、
遗漏／重复／外来资源、具有相同本地 ID 的外域注册表、其他消费者仍持有租约，以及
reservation 清理。标准负控目录也新增了“去掉租约归属检查”和“批次校验前释放
commitment”两种源码变异。局部选定证明实验不替代完整发布负控验收。

这一轮补齐了一个具体的资源释放组合环节。全局 domain 分配、租约获取路由、序列化
视图、不透明值句柄删除、JS/FFI 和回调报告真实性仍是宿主边界。下面的 Rust
回调日志增加了显式重试，但不证明任意 inverse 的外部效果。

## 可重试 Rust inverse 使用经过验证的日志

[`CleanupJournal`](../crates/cordis-kernel/src/cleanup_journal.rs) 包装 Rust Runtime
和静态 typed episode 实际使用的 `StageProtocol` 栈。它的可执行合同检查：恢复选择
最后一个待处理 token；失败保留该 token；只有显式重试才以新的尝试编号继续执行它。
失败或 pending 的选中操作使日志保持非空。重复确认、旧尝试确认和外域确认都不能将其
清除。晚到的登记排在已选中操作之后，在该操作成功后先于更早的待处理操作执行。

[`CleanupQueue<T>`](../crates/cordis-kernel/src/cleanup_queue.rs) 同时拥有日志与实际
保存回调载荷的 `Vec<Option<T>>`。两个宿主都使用这个可执行容器，不要求载荷实现
`Clone` 或 `Debug`。登记将 token 分配与精确载荷存入合为一个操作；选择时从该
token 的槽位移出载荷，每次尝试只交付一次。匹配的失败确认把传入的重试载荷原样
放回该槽；旧尝试、外域、重复或其他被拒绝的确认保持队列，并原样返回传入载荷。
只有仍有载荷才允许重试，已消耗的失败不能产生空重试。每个仍保存的载荷都对应
等待或选中的 token，因此队列为空意味着没有保存的载荷，也没有已交付但未确认的
工作。宿主不再另行维护未经验证的 token 到载荷向量。

通过 `Setup::on_cleanup_retryable` / `on_cleanup_retryable_async` 注册，或在 effect
中使用 `Inverse::retryable` / `retryable_async`。`AsyncSetup` 与 `Runtime` 也提供
同名登记方法。它们接受 `FnMut` 工厂，每次尝试创建新的 Future；当前 pending Future
由 Runtime 保管，调用者丢弃 `Settle` 或 `Join` 不会丢失它。

```rust
let mut attempts = 0;
setup.on_cleanup_retryable(move || {
    attempts += 1;
    if attempts == 1 { Err("temporary cleanup failure".into()) }
    else { Ok(()) }
});
```

失败后可查询 `Runtime::cleanup_failure(id)` 或快照中的 `CleanupFailed` 阻塞项。
再次调用 `settle` 或 `shutdown` 不会重试。本次尝试的所有回调都已结束后，调用者可
显式接纳并驱动下一次尝试：

```rust
runtime.retry_cleanup(id)?;
runtime.settle().await?;
```

实际 Runtime 先取得新的 `LifecycleActions` 清理尝试，再重试各个失败日志。
committed provider 和载荷持续保留，已成功的操作不再执行。一个 effect group 阻塞时，
其他独立 group 可以完成当前工作，但失败 group 中更早的操作必须等待。单独 dispose
effect 后发生可重试失败，会使所属 episode 退出，依赖保留因此覆盖它的重试。
历史错误仍可通过 `take_cleanup_errors` 和 effect handle 查看。

`StaticEpisode::retry_cleanup` 为外部驱动的 typed 插件提供同样的工厂保留行为。
外部宿主负责接纳新的 action 并保留依赖租约；只有后端收到新的清理尝试请求时，Node
typed bridge 才使用这个入口。静态宿主中已消耗的 `FnOnce` 失败，或被丢弃的静态
清理 Future，仍保持阻塞，不能通过该 API 重试。普通 Runtime 则保留原来消耗失败
`FnOnce` inverse 并继续 drain 的策略。

工厂作者必须保证部分外部工作发生后仍可安全重试；`FnMut` 不代表自动幂等。
Verus 检查 token／凭据转换及实际载荷存储与移动，将载荷本身视为不透明值。
执行器调用后选择返回哪个工厂、闭包捕获、domain 分配、panic 处理和回调结果
真实性仍是宿主义务。证明原样保存传入的重试值，不等于证明任意执行器返回了
原来的工厂。[容器回归](../crates/cordis-kernel/tests/cleanup_queue.rs)检查对象身份
与析构；[Rust 宿主回归](../crates/cordis/tests/retry_cleanup.rs)检查不同 effect group
的工厂和成功重试，并有[typed 后端回归](../crates/cordis-node/tests/plugin_runtime.rs)。
标准 `cleanup-journal-discards-failed-inverse` 与
`cleanup-queue-discards-retained-payload` 变异分别针对选中 token 和实际载荷的保留。
局部选定证明实验仍与完整发布验收分开。

## 清理结果与宿主策略

| Outcome | 协议含义 | 宿主策略 |
| --- | --- | --- |
| `Succeeded` | 更新 receipt，使其允许匹配 generation 的 finish。 | Node 和 Rust 在清理排空且没有已消耗失败时报告成功；回调结果真实与否仍是宿主义务。 |
| `Failed` | 保留阻塞 receipt；共享 API 不能 finish/remove。显式重试以新 action 原位替换状态和票据。 | Node 与可重试 Rust inverse 保留失败工作和依赖，成功 inverse 不再重放。静态 typed 宿主已消耗的 `FnOnce` 失败没有重试工厂，会持续阻塞。 |
| `Drained` | 更新 receipt，确认工作已消耗并允许匹配 generation 的 finish。 | 普通 Rust 记录已消耗的 `FnOnce` 错误并继续 drain；保留的可重试失败仍然阻塞。`Drained` 不代表恢复成功。 |

被拒绝的 finish 保持 Kernel 状态与 committed 绑定；成功 finish 才消费 receipt。
仅 `Failed` 可以重试，使用新票据原位更新已有 receipt，
旧尝试的票据仍已消费。调用者不能通过重放 completion 把保留的
`Failed` receipt 变成 `Succeeded`，必须执行显式重试协议。这些 outcome 都不会使
回调自动幂等，也不会撤销已经发生的部分外部效果。

首次 episode 前登记的资源使用 **generation-zero reservation** 路径。内核保持
Inactive，接纳与 finish 分别跟踪；这是宿主扩展，不是论文的 L-Unload 转换。
它与普通清理使用相同的 receipt 表示，由 phase 和 generation 检查区分 reservation
与已安装 episode，并不是另一种 receipt 类型。

## 证据与仍需承担的假设

接受了哪些验证运行，以[绑定源码的证据指南](evidence-guide.md)及实际验证报告为准；
本文不新增证明或发布计数。审查成功清理、失败时保留依赖、显式重试和拒绝旧票据重放，
并对照协议与实际宿主测试。[清理案例](cases/lifecycle-cleanup.md)及
[Node disposal-failure 回归](../tests/node-compat/disposal-failure.test.mjs)
运行真实回调；[Rust runtime 回归](../crates/cordis/tests/runtime.rs)覆盖其独立 drain
策略。以下定向命令运行行为测试，不能替代 Verus 验证或完整开发／发布 gate。

```sh
cargo test --offline -p cordis-driver --test shared_lifecycle --test cleanup_outcomes --test cleanup_resources
cargo test --offline -p cordis-driver --test episode_failure --test reservation_effects
cargo test --offline -p cordis-kernel --test cleanup_protocol --test cleanup_journal --test cleanup_queue
cargo test --offline -p cordis --test retry_cleanup
cargo test --offline -p cordis-node --test plugin_runtime typed_retryable_cleanup_recovers_only_on_a_new_host_attempt -- --exact
```

证明边界包括协议状态及指定内核调用，不包括回调报告的真实性、任意 inverse 的效果、
不透明值句柄删除和宿主路由、JavaScript、N-API/FFI、OS／文件／网络行为、调度及任意
Future 的终止。pending 回调可能永远不返回；安全保留不等于最终清理。文件案例独立
检查写入回调和结果内容，不把 disposal 宣传为文件持久化保证。

工程上的提升，是把清理权限与内核转换放到共享 API 实际执行的代码中，一起审查和
检查。协议证明通过不会让外围运行时自动获得端到端定理；API 与证明的组合缺口，也
不是已经观察到上游 bug 的证据。
