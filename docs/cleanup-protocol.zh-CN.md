# 清理确认与依赖释放

[English](cleanup-protocol.md) | 简体中文

本指南审查一条合同：执行器必须先对已接纳的清理给出明确结果，共享生命周期 API 才能
释放该 episode 的 committed 依赖。它把实际使用的 `LifecycleActions` 协议接到内核
守卫，以及 Node 和 Rust 的真实完成路径。这是 [A07 / F1](adoption-plan.zh-CN.md)
中的一项有限进展，不是任一宿主的完整证明，也不是新确认的上游或运行时缺陷。
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
2. [shared::LifecycleDriver](../crates/cordis-driver/src/shared.rs) 调用该协议。
   `pending_views` 只作序列化视图，不授予转换权限。API 不暴露能绕过协议的可变 Kernel
   引用；普通共享 owner 也负责维护此 Kernel 与此协议实例的配对。公开核心模块不意味
   着任意跨实例组合都已获证明；实例配对与宿主路由仍是集成义务。
3. [Driver::complete](../crates/cordis-driver/src/lib.rs) 区分 setup 与 cleanup
   完成。Node 清理报告为 `Succeeded` 或 `Failed`；失败在 `finish_cleanup` 及
   resource/publication 释放循环之前返回。成功先调用受保护的 finish，再释放依赖
   leases、回收自身 publications。这些普通 Rust 循环仍是宿主边界，即使其使用的
   publication 原语各自已有证明。
4. [Domain.dispatch / Fiber._cleanup](../packages/compat-cordis/runtime.js)
   执行真实回调并发送完成报告。独立的 Rust
   [Runtime::poll_settle](../crates/cordis/src/runtime.rs) 在消耗完清理工作后报告
   `Drained`。

清理接纳预先分配 Pending receipt；completion 原位更新它，不在消费 action 后再分配
新 receipt。setup 完成不能代替 cleanup 完成。票据标识确切的 domain、owner、generation、action
和 kind；重复、类型错误或过期完成不能授权新的尝试。取消不会悄悄丢弃已有 setup
票据，因为它的返回结果仍可能带有必须收集的 inverse。

## 三种 outcome，两种宿主策略

| Outcome | 协议含义 | 宿主策略 |
| --- | --- | --- |
| `Succeeded` | 更新 receipt，使其允许匹配 generation 的 finish。 | Node 仅在受管理清理过程没有报告错误时使用它；报告真实与否仍是宿主义务。 |
| `Failed` | 保留阻塞 receipt；共享 API 不能 finish/remove。显式重试以新 action 原位替换状态和票据。 | Node 保留失败 inverse 的登记与依赖 leases；成功 inverse 已移除，不在重试时重放。 |
| `Drained` | 更新 receipt，确认工作已消耗并允许匹配 generation 的 finish。 | 普通 Rust 消耗 `FnOnce` inverses，记录错误并继续 drain；这既不是恢复成功的断言，也不是可重试 inverse 队列。 |

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
cargo test --offline -p cordis-driver --test shared_lifecycle --test cleanup_outcomes
cargo test --offline -p cordis-driver --test episode_failure --test reservation_effects
```

证明边界包括协议状态及指定内核调用，不包括回调报告的真实性、任意 inverse 的效果、
完整 publication 释放路由、JavaScript、N-API/FFI、OS／文件／网络行为、调度及任意
Future 的终止。pending 回调可能永远不返回；安全保留不等于最终清理。文件案例独立
检查写入回调和结果内容，不把 disposal 宣传为文件持久化保证。

工程上的提升，是把清理权限与内核转换放到共享 API 实际执行的代码中，一起审查和
检查。协议证明通过不会让外围运行时自动获得端到端定理；API 与证明的组合缺口，也
不是已经观察到上游 bug 的证据。
