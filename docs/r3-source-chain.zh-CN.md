# R3：生产源命令的自动关联

[English](r3-source-chain.md) · [控制重放](r3-control-replay.zh-CN.md) · [完整 Journal 删除](r3-effect-deletion.zh-CN.md) · [恢复切面](r3-final-recovery.zh-CN.md)

开启记录的 `NativeRuntime` 现在从真实成功的状态转换入口生成重放命令，并将命令与确切的 native 历史、分配上界及完整共享 Journal 快照绑定。调用方不再维护另一份命令列表，也不再额外证明它与快照对应。

本次补齐的是**控制源命令的自动关联**，并将它接入真实 managed 清理与恢复链。**R3 仍未完成**：重放目前执行 Kernel 控制投影；合法的剩余 Journal 关系，尚不等于在新宿主资源上执行了每一个保留效果。

## 同一条来源链

1. 成功的 root／Child 注册从实际保存的 `RegisteredPlugin` 记录解析后的依赖／提供集合、parent 与私有 anchor；其余成功转换记录真实 actor 和规则。失败调用不增加命令。
2. 生产不变式证明每条命令对应真实 native 后继和标签。分配上界来自快照，不再由调用方提供。
3. `Source::command_at` 与 `command_for` 双向对应命令和真实 Journal 位置。typed `Finish` publication 保留原始值、capture、action 来源、work domain 与 committed provider；交错的其他记录保留完整 Journal 已有合同。
4. 运行时新增 **Unload 来源完整覆盖**不变式：每个真实 Unload 都有来源账本中的成功释放凭据。`Source::unload_at` 从命令位置导出该凭据、清理来源和已覆盖的 Journal 前缀。同一 Journal 中的清理检查点严格早于 Unload。已有队列／token 完成证明可以沿该凭据继续追溯；不能从一个控制标签凭空推出清理成功。
5. `Source::inverse_source` 使用同一 Journal 找到逆操作注册对应的 managed 正向操作，并证明唯一消费。标量与 typed payload 操作、work／cleanup attempt、host／control 记录和 publication 元数据仍位于这一共享来源载体中。
6. `capture_release_census`／`capture_unload_census` 将命令绑定到**已经捕获的恢复切面**。`with_deletion`、`with_effects` 和 `replay_control` 在该切面组合值／Child 恢复、合法 Journal 删除及实际 Kernel 重放。完整 Journal 删除成功时，还证明实际重放终点等于其 native 控制终点在同一名称置换下的结果。绑定过程不增加第二次 Journal 读取，不执行回调，也不克隆 payload。

来源证书字段私有。另一切面的证书不能满足已验证的重放合同。共享别名和后续写入仍受已有来源连续性与效果选择义务约束。

## 有界记录

`NativeRuntime::new` 和 `NativeDriver::new` 默认关闭记录，历史仍是擦除的证明状态。有限审查或恢复场景可使用 `new_recorded`：

```rust,ignore
let mut runtime = NativeRuntime::new_recorded(domain, 4096);
// 注册插件，并调用原有生命周期／managed 效果方法。
let captured = runtime.control_source_snapshot()?;
let replay = captured.source.replay(&captured.cut, &keep, Ghost(window))?;
```

显式容量限制保留的命令条数；命令保存控制声明，不保存服务 payload 引用。第一个超限的成功转换将记录状态设为 `Exhausted`，但**不拒绝该生命周期操作**。`Disabled` 和 `Exhausted` 均返回明确捕获错误，截断记录不能冒充完整来源。没有在执行中途清空记录后声称从空状态开始的接口。已捕获的来源不受后续运行时变化影响。

窗口及删除掩码仍需要来源可采纳条件。该接口不是擦除 Journal 的序列化导出、通用事件调试器，也不会自动选择应删除的全部效果。

## 审查与验证

| 义务 | 入口 |
| --- | --- |
| 有界来源记录及不可替换的切面绑定 | [lifecycle_state/native/runtime/control_source.rs](../crates/cordis-kernel/src/lifecycle_state/native/runtime/control_source.rs)：`Recorder::append`、`bind_control_source`、`Source::replay` |
| 每次真实转换参与记录 | [lifecycle_state/native/runtime.rs](../crates/cordis-kernel/src/lifecycle_state/native/runtime.rs)：`transition`、`wf` |
| 每个 Unload 都有真实清理来源 | [lifecycle_state/native/runtime/control_source/cleanup.rs](../crates/cordis-kernel/src/lifecycle_state/native/runtime/control_source/cleanup.rs)：`complete`、`unload_collected`、`Source::unload_at` |
| 命令、typed publication 与逆操作来源共用 Journal | [lifecycle_state/native/runtime/control_source/chain.rs](../crates/cordis-kernel/src/lifecycle_state/native/runtime/control_source/chain.rs) |
| 复用真实 managed 恢复切面 | [reversible_value/managed/interleaving/history/lifecycle/unload_capture.rs](../crates/cordis-kernel/src/reversible_value/managed/interleaving/history/lifecycle/unload_capture.rs)、[reversible_value/managed/interleaving/history/lifecycle/deletion_capture.rs](../crates/cordis-kernel/src/reversible_value/managed/interleaving/history/lifecycle/deletion_capture.rs) |
| 普通 Rust driver 入口 | [native.rs](../crates/cordis-driver/src/shared/native.rs)：`NativeDriver::new_recorded` |

运行回归改用自动命令完成 24→13 步控制重放，并覆盖继承声明和 anchor、关闭／零容量／耗尽、失败调用不记账和独立快照。已有的标量／typed 干扰、清理失败、新重试票据及 Child 后续释放场景，也从相同真实恢复快照重放控制，并检查捕获没有额外保留 payload 引用。

`python3 scripts/check-profile-controls.py source-chain` 检查漏记命令或漏收 Unload 来源的严格负向对照，要求匹配正例、变异体完整编译以及指定语义合同拒绝。完整负向回归仍单独标记 `not_run`。[开发验证记录](development-report.json)提供绑定源码的集成结果；定向检查和开发验收均不代表发布验收或整篇论文完成。

## R3 剩余工作

本次接通来源侧；完整目标执行仍需建立。还需要通过保留部分的实际宿主执行，构造并关联目标 Journal 引用、action／work／cleanup 票据、逆操作生产者和 typed payload。基于 Episode 所有权的完整效果选择、更广的共享／revision 变化效果、获准异步路径及独立 Node 协议也仍开放。本证书不改变原论文审查结果，也不升级 Equation (55)、全局终止或合流的完成状态。

[真实 managed 目标执行](r3-target-execution.zh-CN.md)已在此来源链上补充可执行输入保留及目标调用。完整 Journal 的目标调度和跨调用对应仍未完成。
