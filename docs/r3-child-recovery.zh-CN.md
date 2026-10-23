# R3：原生 Child 退休与释放

[English](r3-child-recovery.md) · [交错恢复](r3-interleaved-recovery.zh-CN.md) · [里程碑](paper-refinement-roadmap.zh-CN.md)

native 中间截面的完整 publication／owner／pending 观察与恢复现见[第 2 包](r3-observation-recovery.zh-CN.md)。下文相关边界说明限定于本页较早的入口；普通宿主迁移与一般合法删除仍未完成。

Child 清理请求成功表示 Child 已退休，不表示 Child 自己的 Episode 已释放。
原生恢复路径现在把真实共享槽决策接到该 Child 的真实 Unload，包含保留的 publication、
清理守卫和 Episode 身份。**R3 仍在进行。**

## 运行代码建立的保证

`NativeRuntime::retire_shared_child_observed` 调用既有共享槽退休操作。
擦除的 `Retirement` 凭据保留持久槽位决策及原生运行时的真实 Journal 收据，区分：

| 实际观察 | 已建立的结论 |
| --- | --- |
| Pending 请求被取消，或请求此前已拒绝 | 此共享槽未分配，之后不能变成 Assigned；该请求没有需要卸载的 Child Episode。 |
| 已分配 Child，但没有未释放 Episode | 此观察处没有该 Child 的 Episode 所有者或保留 publication；若仍注册，则为 Inactive 且 retired。 |
| 已分配 Child，仍有未释放 Episode | 退休保留准确的 Episode 所有者及 publication；完成需要该 Episode 自己的成功释放。 |

`Retirement::belongs_to` 核对真实共享槽来源和创建它的父插件 Episode。
`matches_unload` 另核对同一 native member、Journal、准确的 `EpisodeOwner`
（动作来源及 work domain）、父插件，以及早于 Unload 的退休收据。实际释放路径让
native 提交同时晚于退休收据与已封闭的清理成员收据，复用既有 Journal 写锁；所存
收据与比较都会擦除。

`Unload::lifecycle_source` 导出实际 native 及论文生命周期的 Unload 转换，包含真实
前后投影。`unload_releases_assigned_episode` 由这些来源推出：

- Child 仍在注册表中，处于 Inactive 且 retired；
- 原生运行时中已没有它的 Episode 所有者和 publication；
- Unload 守卫处不存在依赖它的其他非 Inactive 已提交 consumer；
- 端点携带真实清理来源。

`from_release` 将结论接到准确的成功返回和实际已排空清理组。
`released_child_cannot_begin` 排除在该端点执行 Begin。注册表移除仍是独立操作。
删除运行时的 publication 不等于证明逃逸 `Arc` 已析构，也不等于外部 I/O 已恢复。

## 使用可执行入口

普通 Rust 调用者可以使用组合入口，无需提供证明状态：

```rust,ignore
// 宿主此前已撤回 Child，并驱动它的清理。
let result = runtime
    .retire_and_release_child(&child_handle, &mut child_execution)
    .into_release()
    .0;
```

该入口执行真实退休，检查传入执行是否属于已分配 Child 的当前 Episode，再尝试带守卫
的释放。传入父插件或过期执行、仍有 consumer、清理未排空都会被拒绝。成功返回自动
携带属于该 Child 的释放关系。失败不产生 Unload 或排空组凭据，传入执行和 publication
保持不变，但退休可能已经成功。此调用不会替调用方执行撤回、轮询、重试或等待清理。

对已取消／未分配请求，组合释放入口返回 `InvalidState`，因为没有已分配 Episode
可以释放。若取消本身就是预期结果，应使用退休观察。重复释放会被拒绝，不产生新的
完成凭据。

受验证调用者可以保留 `Retirement`，直接使用 `release_retired_child`，其明确来源
条件要求同一 native member、Journal、捕获的 Episode 和实际父插件。
`ChildRelease` 也提供擦除凭据借用供证明调用者使用；普通运行结果维持既有释放结构。

## 自动收集实际来源

原生运行时现在持有擦除的 `Ledger`，由既有实际修改入口维护三个只追加的来源序列：

| 实际成功操作 | 保留来源 |
| --- | --- |
| `register_shared_child` | `Birth`：持久 Assigned 决策、准确的 native Insert 收据及创建者当时的真实 `EpisodeOwner` |
| `retire_shared_child_observed`（普通退休入口也使用它） | 实际取消或已分配 Child 的退休观察 |
| `release_managed_execution_following`（普通 managed 释放也使用它） | 该 Episode 自己的真实 Unload 及清理来源 |

`Birth::retirement_agrees` 通过持久共享槽身份连接登记与退休，只有相同数字插件 ID
还不够。出生凭据同时保留父插件动作票据和 work domain，后续父 Episode 不能替代
创建者。每份保留的 native 收据都包含于同一 native member 已提交的 Journal 前缀；
其他 native 操作保持这些来源，不能重置历史或引入未来收据。集合、索引及遍历都会
擦除，不增加运行时历史缓冲区、载荷复制或锁。

`Ledger::records` 区分未分配取消、退休时没有未释放 Episode，以及退休后该 Child
自身已 Unload。实际退休入口在来源条件成立时推出前两种结论；
`retire_and_release_child` 成功且该运行时已收集 Child 出生来源时，自动推出第三种。
被阻塞或失败的释放不能制造 Unload 端点，已有端点证据继续保留。这些是历史观察，
[共同切点组合](r3-common-recovery-cut.zh-CN.md)现利用可执行分配器的新鲜性保证，将被覆盖的
已分配 Child 端点推进到同一个实际较晚 native 检查点。

`RecordedExecution::native_children_resolved` 对全部记录组保留的**每个原始 native
逆操作**检查完整性，包括父插件最终释放前已移除的组，核对原始共享槽与创建者
Episode；已分配 Child 的出生来源还须匹配准确的父插件动作与 work domain。
`native_child_endpoint` 随后提取对应真实来源及终态事实；后续
账本追加保持已有证据。父插件排空或 Unload 不会自动推出这个完整性条件。
来源收集范围是上述共享槽与 managed 释放入口，不包含绕过它们的任意 raw 注册或宿主路径。

## 与创建者 Episode 及论文的对应

`RecordedExecution::owned_child_retirement` 将保留逆操作的真实共享槽与创建它的
父插件 Episode、Journal 对应。即使 token 已离开存活队列，仍使用原始动作。
`native_child_unassigned` 排除取消后的迟到分配；`native_child_released` 使用匹配的
Child Unload 推出终态。父插件的成功确认或 Unload 不能满足这个端点关系。

这些是式 (55)／(56)、定理 68 和推论 69 恢复对应所需的来源义务，将具体退休和 Unload
规则接到生产执行路径；尚不建立完整生产效果上的全部等式，也不改变原论文审计状态。

| 审查入口 | 作用 |
| --- | --- |
| [shared_child.rs](../crates/cordis-kernel/src/shared_child.rs)：`Decision`、`retain_decision`、`agrees` | 真实共享槽的持久凭据与终态一致性 |
| [native_runtime.rs](../crates/cordis-kernel/src/native_runtime.rs)：`retire_shared_child_observed`、`release_managed_execution_following` | 真实退休观察与具有因果顺序的释放 |
| [native_child_recovery.rs](../crates/cordis-kernel/src/native_child_recovery.rs)：`Retirement`、`retire_and_release_child`、`release_retired_child` | 可执行组合、准确端点关系及推导的释放事实 |
| [native_episode_origin.rs](../crates/cordis-kernel/src/native_episode_origin.rs)：`lifecycle_source`、`current_unload` | 真实 Unload 转换及前后投影 |
| [managed_lifecycle_children.rs](../crates/cordis-kernel/src/managed_lifecycle_children.rs)：`owned_child_retirement`、`native_child_released`、`native_child_unassigned` | 与创建者 Episode 所保留逆操作的对应 |
| [native_child_history.rs](../crates/cordis-kernel/src/native_child_history.rs)：`Birth`、`Ledger`、`child_birth`、`covered` | 实际 Insert／父 Episode 来源、自动收集及已提交前缀覆盖 |
| [native_child_completion.rs](../crates/cordis-kernel/src/native_child_completion.rs)：`records`、`settle_retirement`、`settle_release` | 由来源推出取消、退休时无 Episode 或自身 Unload 完成 |
| [managed_child_completion.rs](../crates/cordis-kernel/src/managed_child_completion.rs)：`native_children_resolved`、`native_child_endpoint` | 对保留原始逆操作的完整性检查及准确创建者身份 |

## 验证与剩余工作

[native 运行测试](../crates/cordis-kernel/tests/native_runtime.rs)覆盖父插件先卸载、
已退休 Child 仍被 consumer 阻塞、consumer 清理失败及新票据重试、成功 Child 释放和
单独 Remove。另覆盖用父插件执行替代、重复释放、已退休端点上的 Begin，以及迟到
请求派发前的取消。当前定向验证结果和复现命令见[交错恢复](r3-interleaved-recovery.zh-CN.md#审查与验证)。
新增变异控制与完整开发验收仍待进行，全量负向回归／校准保持 `not_run`。

出生、退休和 managed Unload 来源现已自动收集。[共同切点定理](r3-common-recovery-cut.zh-CN.md)
已将被覆盖的 Child 端点、调用值恢复及本次写入的注册完成接到同一实际检查点。
跨中间切点的一般 publication／pending 效果仍待完成。
完整外部观察、值来源衔接、合法剩余执行和普通宿主迁移仍待完成。
特别是，父插件释放不推出 `native_children_resolved`。这里不推出公平性、清理最终完成
或全局终止。

集成验收时补充以下变异控制：遗漏出生／退休／Unload 来源、重置历史、替换共享槽或
父动作／work domain、使用实际 native 前缀之外的收据，以及把父插件排空当作 Child
完成。这些证明控制仍待进行，既有运行案例不能替代它们。
