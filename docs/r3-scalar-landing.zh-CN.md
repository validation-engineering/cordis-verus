# R3：从真实源操作推出标量落地条件

[English](r3-scalar-landing.md) · [共享目标执行](r3-shared-target-batch.zh-CN.md) · [R3 剩余工作](r3-remaining-work.zh-CN.md)

保留的真实源成功操作，现在可以驱动目标 Episode 中的一次受检查标量操作。操作有定义来自实际源报告；目标端通过宿主捕获已声明服务，读取当前数值和逆操作深度，运行保留的计算，并使用 managed 解释器原有的 native effect 路径落地。

**本轮关闭的是基本操作层面的成功义务，还不是完整 R3-A 模拟。** batch 调度器仍需从生产执行历史推出输入对应和允许的干扰条件。

## 执行与合同

```rust,ignore
let prepared = source.prepare_scalar(step_index, &target_owner, group_id)?;
let target_step = prepared.land(&mut target_owner, group_id)?;
```

`step_index` 选择源调用实际成功执行前缀中的操作，不能传入期望的目标结果，也不能选择任意未执行指令。

| 阶段 | 实际执行与已验证保证 |
| --- | --- |
| 源记录 | `Source::wf` 将保留的函数、端口列表、操作数及逆操作绑定到真实注册调用报告，并补上函数与端口列表长度一致的不变式。 |
| 目标读取 | `Source::prepare_scalar` 通过真实目标 owner 捕获源端口。`Capture::prepare_at` 在计算前检查数值及逆操作深度。`InputMismatch` 保留实际选中 binding、认证快照及读取凭据；这些证据运行时擦除。 |
| 计算 | 原 `ScalarEffect` 在服务／数值锁之外运行。源成功及检查过的输入共同证明语义操作有定义。 |
| 落地 | `PreparedStep::land` 调用原有 `apply_native_effect`。准备成功后，落地只会返回对应的真实 `Step`、`Closed` 或 `Interference`，证明排除了 `Capacity` 和 `Rejected`。 |
| 成功 | 实际输入、输出、结果及分支与源步骤相等。新逆操作及其注册凭据属于目标 owner 的真实队列，没有复用源逆操作。 |
| 失败 | 错误或已关闭的准入不会落地。干扰失败具有真实拒绝凭据；拒绝提交保持当时的联合状态和待处理义务，不给 owner 新增逆操作。 |

对于准入仍有效的落地，合同给出：

```text
落地成功 ⇔ 落地时的实际状态等于捕获的源输入
```

这里使用实际落地凭据，包含失败尝试，不要求先提供一个成功目标步骤。`quiet_input` 还给出了充分条件：从目标真实读取到落地，期间没有帧改变该目标对象的状态。`unchanged` 从实际 Journal 帧推出落地输入，可执行 `land` 会调用这段证明。期间可以修改其他对象，也可以发生不改变状态的拒绝尝试。修改后又实际恢复，也可能满足精确状态检查；无状态变化是充分条件，而非必要条件。

## 本轮暴露的不确定性

`ScalarEffect::compute` 证明的是返回值合同，不代表计算过程不会修改共享状态。即使实现经过验证，也可能执行额外操作；其他参与者同样可能在捕获后、落地前修改该对象。复制 effect 也不会自动重映射实现内部隐藏的引用。

因此，不能仅从源调用成功就推出任意宿主行为下的目标成功，现有干扰检查仍然必要。R3 还需从所有权和捕获历史推出目标输入对应，以及相应调度／效果修改范围条件。处于 mediated scalar／typed 范围之外的效果需要独立来源和修改范围合同。不能暗中假定计算纯净，也不能把“目标成功”变成新的调用方前提。

新入口执行单次标量操作，不负责调度注册 root／Child、结算 work、执行 typed 替换或结束 Episode。`batch::run` 仍使用原注册解释器，范围未改变，没有切换为另一套重放解释器。此处端口与输入一致，也不能替代 batch 的对象身份／别名对应。

## 论文到代码的审查路径

基本操作的定义域、结果、延续及严格逆操作，使用 R1/R2 同一份 `managed::semantics` 解释。这是[论文计划](paper-refinement-map.md)中 R3 恢复条目 68、69、79 所需的“构造真实剩余执行”的局部成果，还不是公式 (55) 的一般恢复结论。

审查时结合[可执行源桥接](../crates/cordis-kernel/src/managed_replay_scalar.rs)、[原生捕获与落地](../crates/cordis-kernel/src/native_effect.rs)及[标量计算合同](../crates/cordis-kernel/src/scalar_effect.rs)。源操作数仅由显式 replay 捕获保留；本轮新增的读取、Journal 和逆操作对应证据在普通构建中擦除。

[运行案例](../crates/cordis-kernel/tests/managed_replay.rs)覆盖实际分支／深度推进与清理、数值相同但深度不同的拒绝、干扰后的真实恢复重试、其他对象写入，以及错误／已撤销 owner。严格负控 `scripts/check-r3-scalar-landing-controls.py` 删除深度检查，要求错误实现仍可编译，并在指定输入相等断言处被验证器拒绝。限定范围证据不替代完整开发验收、全量负控或发布验收。
