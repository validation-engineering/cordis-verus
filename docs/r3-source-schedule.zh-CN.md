# R3：源执行顺序与 typed 连续性

[English](r3-source-schedule.md) · [共享目标执行](r3-shared-target-batch.zh-CN.md) · [剩余工作](r3-remaining-work.zh-CN.md)

有限 native batch 现在从真实调用完成事件导出顺序。typed 操作也有从生产历史推出的输入连续性，以及原子的捕获输入落地路径。这些是可执行的 R3 组成部分；**一般剩余执行定理仍未完成**。

## 真实源顺序

生产 recipe ledger 在擦除的历史之外维护受检的可执行 revision。`run_replayable_root` 在原 root 完成后捕获该 revision 和真实 recipe 分配身份，合同把编号绑定到对应的 `Recipes::Call` 凭据。计数耗尽后返回 `None`，不会回绕，也不会阻止普通宿主执行。

`order::plan` 先检查保留调用是否来自同一真实 recipe 流，再对原始输入下标排序，证明完整置换、位置严格递增及完成凭据的真实时间顺序。身份不可用、位置耗尽、混入其他流或重复位置都会在创建目标 provider 前拒绝。比较仍要求已有的共同命名域，不把生命周期 domain 数字当作身份。

`batch::run` 用该计划选择首次操作数，并调用原 registered root 执行器。`Batch::order` 把返回的调用顺序映射回源输入下标，失败诊断也使用原始下标。倒置传入顺序现在可以正常执行；若省略此前仍持有标量逆操作的必要步骤，仍会明确拒绝。这里排序的是选定调用，还不是全部 Begin/publication/Child/cleanup/Unload 事件。

## typed 输入与落地

`Input::continues_payload` 比较真实分配身份和可执行的源 head。匹配后，通过实际逆操作 owner 的两份持久历史凭据，推出前一步完整输出等于后一步输入，包括值与深度。不要求 `T: Eq`，不转换指针，不重新读取源对象，也不要求调用方假设值相等。清理或退休不能改写已保留历史。head 不匹配时拒绝；该接口不会补造中间的恢复或替换操作。

`payload::Capture::apply` 在**执行写入的同一把写锁内**重新检查目标的防陈旧 revision，成功后在解锁前构造下一份 capture。其值、语义 head、revision 和提交凭据都对应实际生成的逆操作。陈旧、容量不足和退休失败保留真实拒绝观察，并返回待写入载荷。成功恢复同样推进防陈旧 revision，因此即使语义值恢复，旧 capture 仍然陈旧。

`capture_native_payload` 与 `native_payload::Capture::land` 将此路径接入真实选中的服务句柄和清理 owner。落地重新检查 owner/work/queue 准入，通过原清理实现登记实际逆操作；成功返回下一份 capture，失败不添加逆操作。普通 typed 解释器共用同一写入和登记实现。具有内部可变性的载荷仍遵守既有显式边界；`Arc<T>` 不代表任意用户内部状态的深拷贝。

## 审查路径

| 义务 | 可执行实现与合同 |
| --- | --- |
| 真实位置，不虚构序号 | [`lifecycle_state/native/runtime/recipes.rs`](../crates/cordis-kernel/src/lifecycle_state/native/runtime/recipes.rs)、[`managed_replay.rs`](../crates/cordis-kernel/src/managed_replay.rs)：`Ledger::revision`、`Source::wf`、`run_replayable_root` |
| 同一流、完整时间顺序置换 | [`managed_replay_order.rs`](../crates/cordis-kernel/src/managed_replay_order.rs)：`plan`、`prefix`、`chronological` |
| 顺序计划驱动实际调用 | [`managed_replay_batch.rs`](../crates/cordis-kernel/src/managed_replay_batch.rs)：`run`、`actual_prefix` |
| typed 源连续性 | [`managed_replay_payload_history.rs`](../crates/cordis-kernel/src/managed_replay_payload_history.rs)：`continues_payload` |
| 原子输入守卫与实际逆操作 | [`payload_inverse.rs`](../crates/cordis-kernel/src/payload_inverse.rs)：`apply_captured_following` |
| 实际服务选择与清理所有权 | [`native_payload.rs`](../crates/cordis-kernel/src/native_payload.rs)、[`payload_cleanup.rs`](../crates/cordis-kernel/src/payload_cleanup.rs)：`land`、`apply_payload_captured_following` |

这些支持论文条目 68、69、79 对应的既有 recovery 工作包，不改变式 (55) 的审查解释与验收标准。batch 尚未把 typed 连续性和捕获落地接口自动组合为完整剩余生命周期调度器；跨调用标量／typed 状态模拟、动态绑定、owner publication、Child 和区间内部 Unload 仍需完成。[效果边界案例](r3-effect-boundary.zh-CN.md)还揭示了通用重放成功所需的接口决策。

## 复现与证据

```sh
cargo test -p cordis-kernel --test managed_replay --test replay_effect_boundary --locked --offline
python3 -B scripts/check-profile-controls.py source-schedule
bash scripts/check-r3-effect-boundary.sh
```

选定负向控制要求：对应正向证明成功、变异代码可以编译、在指定源位置或 typed 输入断言处被拒绝。超时或无关诊断不算通过。运行案例包括倒置输入、混入其他源流、真实槽位替换、清理后的 typed 历史、连续两次 typed 落地及实际逆序清理、错误 owner、中间替换、退休，以及语义恢复但 revision 已推进的情况。限定范围证据不代表 R3 整体验收或发布验收。
