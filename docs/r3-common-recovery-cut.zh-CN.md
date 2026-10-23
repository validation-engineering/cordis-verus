# R3：共同生产检查点上的恢复

[English](r3-common-recovery-cut.md) · [Child 来源](r3-child-recovery.zh-CN.md) · [值恢复](r3-interleaved-recovery.zh-CN.md)

native 中间截面的完整 publication／owner／pending 观察与恢复现见[第 2 包](r3-observation-recovery.zh-CN.md)。下文相关边界说明限定于本页较早的入口；普通宿主迁移与一般合法删除仍未完成。

父插件可以先于已退休 Child 卸载。因此，恢复证据需要对应同一个真实的较晚检查点，
不能只汇总不同时间的终态观察。受管恢复路径现在将已恢复值、原始 native Child 义务
以及已完成的正向注册组合到这个检查点。**这是限定范围的组合，R3 仍在进行。**

## 已建立的结论

`RegisteredReport::unload_recovers_with_children` 使用实际注册函数报告、记录执行、
该 Episode 自己的 native Unload、运行时收集的 Child 来源，以及真实 native `Snapshot`，
一起推出：

| 共同检查点上的投影 | 结论 |
| --- | --- |
| 注册调用触及的对象 | 解码得到的 scalar／typed 值等于实际 Begin 值 |
| 创建者保留的原始逆操作中，每个已分配 native Child | 没有 Episode owner 或保留 publication；若仍注册，则为 retired 且 Inactive |
| 已取消或拒绝的未分配请求 | 保留的持久决策为未分配，之后不能变为 Assigned |
| 本报告中实际成功的受管写入 | 对应原始正向位置已不在该检查点的 pending registration 表中 |

检查点来自既有 `NativeRuntime::publication_snapshot` 的实际读取，其合同包含 Child
账本来源覆盖。调用方不提供预期终值、空 pending 表或虚构的 Child 状态。新增集合、
来源比较及遍历都会擦除，本批不增加运行时历史缓冲区、额外快照读取或锁。

## Child 端点为何能保持到较晚观察

可执行 Kernel 为插件分配高于此前全部分配身份的新身份，Remove 不会回退分配上界。
注册和 Begin 包装层现在沿实际调用链导出这些事实。`NativeRuntime` 将
`History::allocated_below` 和 `fresh_insertions` 作为不变式维护，认证 native 快照
保留这个性质。

`terminal_retained` 证明：已退休、Inactive 且没有 owner／publication 的 Child，
经过后续实际 native 转换仍保持终态。其他插件可以注册、运行和释放，Child 自身也可以
单独 Remove；后续 Insert 不能将旧身份重新解释成新插件。该结论来自实际分配历史，
不要求整个 native 后缀没有变化。`Ledger::resolution_at_cut` 在完整历史中定位真实
出生、退休和 Unload 收据，再把结论推进到共同检查点。

取消没有需要推进的出生或 Unload。持久共享槽决策独立于 native Journal 位置排除
后续分配，不会被表示成一个虚构的 native 取消事件。

## 值与 pending registration

值部分先使用既有来源恢复定理，在该 Episode 的真实 Unload 处建立恢复。
`observe_later` 再在较晚检查点解码同一批对象，要求实际 Journal 后缀没有再次修改这些
对象。恢复后的写入会使条件不成立，即使写入相同可见值也是如此；其他对象及 native
生命周期事件仍可变化。

scalar 和 typed 解释器路径现在导出：同 Journal 的逆操作注册实际消费了准确的正向
位置。`registered_pending_at_cut` 利用真实注册收据和 Journal 的不重新出现定理，
推出这些位置在较晚检查点不再 pending。其他调用仍可能有 pending 写入；这里不宣称
整张 pending 表为空，也不表示所有可能的中间暂存状态都已恢复。

[被观察所有者版本](r3-observed-recovery.zh-CN.md)
`unload_recovers_from_observed_owners` 现从真实注册步骤、终态组及被覆盖的派发历史推出
外部恢复闭合；可执行观察入口沿调用与重试保持已有派发覆盖。上面的原始入口仍保留
其明确的闭合前提。

## 来源条件与剩余工作

Child 完成覆盖仍是明确条件：`native_children_resolved` 检查全部记录组的每个原始
native 逆操作。父插件排空或 Unload 不会推出它。证明从这些来源覆盖推出共同切点的
终态，不负责调度 Child 清理，也不假设公平性。

值恢复保留既有条件：相关实际观察完整、值衔接、外部写入有匹配的成功恢复，以及值
尾部无修改。新端点须覆盖同一 native member／Journal 中的实际 Unload 和收集的 Child
来源，不会把独立 Journal 拼成虚构的全局时钟。

R3 剩余工作包括：通过完整宿主编排建立所需观察／恢复覆盖，推广到中间切点上的一般
publication 和 pending 效果恢复，完成普通宿主迁移，并构造删除目标 Episode 后的合法
剩余执行，包含 owner 创建的 Child 和 consumer。原论文审计结论及 R3 退出条件保持
不变。本批补充式 (55)／(56)、定理 68 和推论 69 所需的恢复对应，不证明原文的无限制结论。

## 审查与验证

| 源码 | 审查入口 |
| --- | --- |
| [lifecycle_state/native/runtime/history/lifetime.rs](../crates/cordis-kernel/src/lifecycle_state/native/runtime/history/lifetime.rs) | 实际分配上界、Insert 新鲜性、终态保持及来源索引 |
| [lifecycle_state/native/runtime.rs](../crates/cordis-kernel/src/lifecycle_state/native/runtime.rs) | 实际转换维护不变式，既有快照导出来源覆盖 |
| [lifecycle_state/native/runtime/child_history/cut.rs](../crates/cordis-kernel/src/lifecycle_state/native/runtime/child_history/cut.rs) | 每个已分配 Child 在较晚真实检查点上的终态 |
| [managed_child_cut.rs](../crates/cordis-kernel/src/managed_child_cut.rs) | 全部原始 native Child 义务使用同一检查点 |
| [managed_pending_cut.rs](../crates/cordis-kernel/src/managed_pending_cut.rs) | 实际正向注册在检查点保持已完成 |
| [managed_recovery_cut.rs](../crates/cordis-kernel/src/managed_recovery_cut.rs) | 值解码及组合定理 `unload_recovers_with_children` |

验证结果和命令维护在[交错恢复说明](r3-interleaved-recovery.zh-CN.md#审查与验证)中。
新增变异控制与完整集成验收仍待进行，全量负向回归／校准保持 `not_run`。

集成验收时覆盖：复用分配身份、Remove 后重新分配新身份、遗漏或使用未来 Child 来源、
替换 native member／Journal、父插件先于 Child 释放、恢复后再次写入，以及注册未消费
对应正向位置。增加同时含非空值义务和 Child 义务的证明调用者；单独的运行拒绝案例
不能验证组合证明的来源条件。

更强的 [`unload_recovers_from_source_history`](r3-source-continuity.zh-CN.md) 入口先从所有者持有的真实来源和轨迹条件推出值连续性及逆操作仍可用，再组合本共同截面定理。
