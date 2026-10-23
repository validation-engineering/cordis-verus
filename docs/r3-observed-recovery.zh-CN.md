# R3：从被观察的执行所有者推出恢复

[English](r3-observed-recovery.md) · [共同检查点](r3-common-recovery-cut.zh-CN.md) · [交错恢复](r3-interleaved-recovery.zh-CN.md)

native 中间截面的完整 publication／owner／pending 观察与恢复现见[第 2 包](r3-observation-recovery.zh-CN.md)。下文相关边界说明限定于本页较早的入口；普通宿主迁移与一般合法删除仍未完成。

当另一个执行仍保管较晚写入的逆操作时，当前执行可能无法恢复该值。恢复证明现从那个
写入的实际注册逆操作、清理历史和已排空队列推出它确实完成了恢复，无需调用方另行
假设外部恢复成功。**R3 仍在进行；完整来源覆盖和值轨迹仍是明确条件。**

## 运行路径与证明

| 真实执行来源 | 建立的合同 |
| --- | --- |
| `RecordedExecution::run_function` | 每个成功步骤对应实际原始队列／token 和注册，包含后续失败前保留的成功前缀 |
| `run_function_observed` | 调用真实解释器，将返回的全部正向观察追加到双方所有者的历史 |
| `dispatch_observed` | 调用真实混合清理派发器，将同一份受管成功或失败观察追加到双方历史 |
| 成功的组移除或 native Unload | 保留通过真实排空守卫的终态队列 |
| `drained_forward` | 从槽位保留合同推出每个被覆盖的原始逆操作都有真实的成功受管恢复 |
| `unload_recovers_from_observed_owners` | 将来源推出的外部恢复闭合接入既有共同检查点上的值、Child 和 pending 注册证明 |

`owns_forward` 将真实报告步骤绑定到原始动作、准确的组、队列、token 及逆操作注册。
移除不会丢弃原始槽位；队列不能通过丢失受管逆操作，或用普通回调的 `Drained` 代替
受管恢复来通过排空合同。

观察方可以保留多个组的历史。`observations_extend` 证明两个观察入口追加实际输出后，
已有的派发覆盖仍然成立，可组合有限次调用、失败与重试。它不能补回此前已经遗漏的
观察。`retain_forward_source` 将注册来源沿同一原始槽位历史的扩展保留下来。提前移除
某个组足以证明该组已有写入的恢复，不要求整个外部执行都已经卸载。

## 因果边界与成本

两个观察入口执行前，来源所有者会在同一 Journal 内，将自己的保留边界与观察方的真实
收据合并。因此，写入和清理位于相关先前观察之后。执行后，观察方保留来源所有者的真实
完成或清理边界；较早收据保持被覆盖，不会被冒充为实际前驱。

这些合并比较持久证明凭据，不增加运行时锁、值复制或历史缓存。受管调用保留原有的
返回时 Journal 读取。观察入口借用两个真实所有者，普通执行仍进入既有解释器和混合
派发器。独立 Journal 保持各自的边界。

## 来源覆盖与剩余边界

`foreign::covered` 要求目标历史中每个相关外部正向写入，均能关联到所给记录所有者的
真实注册步骤、该步骤所属的终态组，以及正向写入之后相应的派发观察。它检查实际
派发的覆盖，包括失败，不要求预先指出哪次派发成功。`closed_from_owners` 使用真实
排空边界推出成功恢复闭合。所有者映射支持多个来源及已移除的历史组；缺少来源或
组尚未排空时，合同不成立。

在被观察区间内持续使用这些真实入口，可以保持观察覆盖。它们不会拦截任意 raw 写入、
不透明回调、未观察的派发或其他宿主。共同切点定理仍要求真实值衔接与顺序、完整 Child
端点及尾部值不再变化。本地或外部释放都不会证明调度公平或最终恢复。一般 publication／
pending 恢复、普通宿主全面接入及合法保留执行的构造仍待完成。

## 审查与验证

- [reversible_value/managed/interleaving/history/lifecycle/observer.rs](../crates/cordis-kernel/src/reversible_value/managed/interleaving/history/lifecycle/observer.rs)：可执行的观察调用／派发及收据边界合并。
- [reversible_value/managed/interleaving/history/lifecycle/function.rs](../crates/cordis-kernel/src/reversible_value/managed/interleaving/history/lifecycle/function.rs)：从实际返回前缀建立来源归属。
- [reversible_value/managed/interleaving/history/lifecycle/recovery/cut/foreign.rs](../crates/cordis-kernel/src/reversible_value/managed/interleaving/history/lifecycle/recovery/cut/foreign.rs)：观察保持、终态槽位恢复及记录所有者的恢复闭合。
- [reversible_value/managed/interleaving/history/lifecycle/recovery/cut.rs](../crates/cordis-kernel/src/reversible_value/managed/interleaving/history/lifecycle/recovery/cut.rs)：组合恢复入口。
- [reversible_value/managed.rs](../crates/cordis-kernel/tests/managed_function.rs)：`observed_foreign_owner_restores_failed_prefix_before_native_retry` 使用两个真实所有者，覆盖失败调用前缀、typed 同值写入干扰、拒绝释放、外部清理及 native 重试。

当前定向结果及复现命令见[交错恢复说明](r3-interleaved-recovery.zh-CN.md#审查与验证)。
运行案例不等于建立组合证明的全部前提。集成验收仍需非空贯通证明调用者，以及遗漏派发、
替换队列／token／所有者、丢弃失败前缀、把保留失败视作排空或宣称跨 Journal 顺序的变异
控制。完整开发验收和新增变异控制仍待进行；全量负向回归／校准保持 `not_run`。

[来源连续性组合](r3-source-continuity.zh-CN.md)现已跨这些接口保留真实 typed 历史资源，并从实际 Journal 间隙推出值连续性；创建来源和成功观察唯一性条件进一步推出逆操作仍可用。完整观察与生命周期删除的边界仍然保留。
