# R3：在目标宿主真实执行保留的 managed 调用

[English](r3-target-execution.md) · [自动来源链](r3-source-chain.zh-CN.md) · [路线图](paper-refinement-roadmap.zh-CN.md)

显式的 `run_replayable_root` 入口现在保留真实注册调用使用的可执行输入。其来源可以在另一个 native runtime 注册并运行同一程序，经过原有 Begin、managed 解释器、work 完成和记录清理历史的执行所有者。目标执行从 Kernel 控制重放推进到了**一次真实注册的 managed 调用**。**R3 仍未完成。**

共享对象扩展现已组合多次真实目标调用，包括 provider 发布及失败 owner 保留。
共同命名域合同、当前执行范围和剩余源到目标模拟工作，见
[共享目标执行](r3-shared-target-batch.zh-CN.md)。

## 同一条可执行路径

1. 从真实注册复制函数，保留标量计算、分支和替换用的 `Arc<T>`。将副本绑定到实际返回的调用报告、版本及 action／work 来源。失败调用已经完成的前缀仍保留失败结果。
2. `Source::bind_control` 在实际调用返回凭据之后观察完整共享 Journal，并绑定自动记录的生命周期命令。覆盖关系在真实 Journal 锁内导出，无需调用方再提供一份命令列表或假设历史前缀相容。
3. `Source::instantiate` 用保存的函数及声明创建目标注册，在 Begin 前检查实际解析出的依赖、提供列表和指令端口。在修改目标前拒绝复用源 lifecycle／work 域，避免混用源票据。
4. 真实目标 Begin 创建执行所有者，并捕获目标 provider。补强后的准入合同证明：合法且已绑定的函数使用该新所有者时，**一定进入原解释器并返回真实调用报告**。随意返回一个准入错误不满足这条合同；具体操作或服务访问失败仍如实保留在报告中。
5. 目标报告关联目标 action／work 票据、目标写入凭据及实际进入目标清理队列的逆操作。返回的 `RecordedExecution` 继续使用原有 Finish、撤回、清理失败、重试、Unload 和最终恢复观察接口。

执行输入不包含期望的目标结果、伪造的 Journal 记录或源逆操作。保存的程序实际读取目标服务，因此目标输入不同可能产生不同结果；输入对应仍是需要建立的证明条件。

## 局部对应保证

真实源步骤与目标步骤都按保存的同一程序解释。对于执行到相同程序位置的两个成功步骤：

- 标量值和深度相同，可以推出结果及后续分支相同。
- opaque payload 值相同，可以推出载荷结果和后续分支相同；目标对象的 head 及严格逆操作仍来自目标执行。
- 目标逆操作保留在真实队列槽位中，其注册引用目标侧实际创建它的操作。

`TargetRun::pair_step` 从两份真实报告建立该局部关系。它不假设每个目标操作都会成功，也没有证明整个选择后的 Journal 已得到重现。即使替换输入使用同一个 Arc，目标上的更新版本仍会正确阻塞旧逆操作。

## 实际输入保留及单个目标资源初始化

`run_replayable_root` 现在还从返回 owner 真实队列中保留的逆操作提取每个成功步骤的原始输入：标量的值／深度，或 typed 写入前的 Arc／head／深度。`Input::wf` 将这些运行数据绑定到实际步骤、程序位置、队列 token 和写入／分配来源。捕获不会重读已经变化的对象，也不消费或复制恢复权限。失败操作不会凭空产生输入记录，已成功的前缀按原顺序保留。

保留的 Arc 是 typed 值载体，不会为任意内部可变业务状态制作快照。

`Source::inputs()` 提供不可变输入记录。`Input::seed(journal)` 使用捕获值在目标 Journal 创建单个资源。标量输入若深度非零，则返回 `OutstandingScalarHistory`：这种状态必须由之前的真实目标操作及其持有的逆操作产生。typed 新资源保留实际 Arc 值，并建立自己的 head／深度历史。`seeded_operation` 证明源指令在这一支持的初始状态有定义，且结果、后续分支对应；它不再只比较两个已经成功的原语步骤。可执行的 `Source::seed_input` 入口直接调用这段证明，从真实来源导出 `initializes` 合同；若索引超出成功执行的前缀，则返回 `MissingStep`。

```rust,ignore
let seed = captured.source.seed_input(0, &target_runtime.execution_journal())?;
// 通过目标 provider 发布返回的 Seed::Scalar 或 Seed::Payload。
// 再让保存的函数读取这些实际目标服务。
```

这**尚不是保留共享关系的重放堆**。若对每个输入分别分配资源，会破坏别名。调度器仍须保留可执行对象身份，为每个对象选择第一个保留输入，再通过真实操作产生后续状态。当前输入捕获没有证明目标服务选择、无干扰或完整窗口执行。

## 用法与资源保留

```rust,ignore
let (mut source_owner, captured) = source_runtime.run_replayable_root(id, execution);
let captured = captured?;
let source_cut = captured.source.bind_control(&source_runtime)?;
let mut target = captured.source.instantiate(&mut target_runtime, Destination {
    parent: None,
    anchor: target_anchor,
    host: (),
    work_domain: fresh_work_domain,
})?;
// 检查 target.report，继续通过正常生命周期接口操作 target.owner。
```

来源对象在释放前保留函数输入和成功前缀的实际输入，包括替换载荷与写入前载荷的 Arc 引用，保留量与存储函数及实际执行前缀成比例。这是显式选择的保留行为，默认调用不变，也不增加无限增长的事件缓冲。源插件注销后，这些输入仍可使用。控制记录仍采用独立的可选容量和耗尽策略。

目标沿用保存的 realm 上下文。首个执行入口要求解析后的声明及端口完全一致，尚不支持的 parent／alias 变化会在执行前拒绝。注册失败退还 host；绑定或 Begin 失败返回已创建的 inactive 注册 ID，供调用方清理，不承诺回滚。已执行的报告即使包含失败前缀，也始终带回真实清理所有者。

## 审查与验收

| 义务 | 代码／证明入口 |
| --- | --- |
| 实际保存的函数及来源回执 | `reversible_value/managed/replay.rs`：`run_replayable_root`、`Source::wf` |
| 完整来源切面 | `Source::bind_control`、`lifecycle_state/native/runtime.rs`：`publication_snapshot_following` |
| 新目标 work 确实进入解释器 | `registered_root_ready`、`root_ready`、`managed_invocation_ready`、`Source::instantiate` |
| 输入捕获与目标资源初始化 | `reversible_value/managed/replay.rs`：`Source::seed_input`；`reversible_value/managed/replay/inputs.rs`：`capture`、`captured`、`initializes`、`seeded_operation` |
| 标量与 typed 步骤的真实对应 | `reversible_value/managed/replay/transport.rs`：`derive`、`paired`、`TargetRun::pair_step` |
| 目标逆操作及恢复 | 返回的 `RecordedExecution`、`capture_release_census` |

运行用例覆盖源注销、目标 ID 偏移、不同资源、不同输入上的真实失败前缀、typed 清理干扰、新重试票据、最终恢复切面及执行前拒绝。`python3 scripts/check-profile-controls.py target-execution` 单独检查跳过真实解释器或用空函数替换保留源函数时，指定证明合同必须拒绝。

本轮输入捕获通过了**七个受影响模块的 206 项 Verus 检查**及**五个 managed replay 运行案例**，包含源清理后继续修改、由真实保留输入初始化目标并执行，以及拒绝伪造未恢复标量历史。此前的[开发验证记录](development-report.json)对应更早的源码快照；本轮尚未重跑完整开发验收、严格负控或发布验收，不能沿用旧快照的通过结论。

## R3 剩余工作

固定的 R3-A 至 R3-D 验收项、依赖、风险与当前工作量估计见 [R3 剩余工作](r3-remaining-work.zh-CN.md)。


需要把保留调用和宿主操作组合为整个选择后的 Journal 执行：跨调用、publication、逆操作创建和清理导出输入对应及目标引用／票据映射；扩展一般交错、动态 Child 插入、按所有权选择效果以及 revision／alias 变化。目前控制命令的删除掩码尚未自动调度这些目标调用。opaque 回调、更广的异步落地及 Node 协议还需要各自的迁移合同。本轮不宣称完整窗口重放、一般 Equation (55)、全局终止或整篇论文完成。
