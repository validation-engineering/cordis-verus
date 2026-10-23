# R3：从真实值来源推出恢复

[English](r3-source-continuity.md) · [跨 owner 观察](r3-observed-recovery.zh-CN.md) · [共同恢复截面](r3-common-recovery-cut.zh-CN.md)

native 中间截面的完整 publication／owner／pending 观察与恢复现见[第 2 包](r3-observation-recovery.zh-CN.md)。下文相关边界说明限定于本页较早的入口；普通宿主迁移与一般合法删除仍未完成。

生产 RecordedExecution 路径现在从真实 Journal 和 payload 历史资源推出值连续性。
新的恢复入口不再要求调用方直接提供“每个事件实际读到的值等于恢复解释器重建值”的条件。

**R3 整体仍在进行中**。已准入同步 Fresh 类别的删除／重放结果见[独立文档](r3-closed-region-deletion.zh-CN.md)。
[最终恢复组合](r3-final-recovery.zh-CN.md)现已在真实 native 截面消费完整生产者区间；
更广的观察范围与普通宿主迁移仍需继续完成。

## 真实代码保留了什么

`Inverse::restore_following` 在实际存储锁内取得 payload 历史证据。恢复成功时，
记录恢复后的历史；干扰失败时，记录实际读取的历史；payload 已关闭时，保留真实
退休观察，不伪造仍然存在的值历史。

`Sources` 为每个 payload 来源保留最长的可信前缀，合并时使用 Verus 持久资源的一致性。
仅仅具有相同的数字槽位或版本号，不足以证明两个值相等。历史包含 payload 身份、head
和 depth，所以“在新版本恢复到旧 head”与“写入内容相等的新值”仍然有区别。

`RecordedExecution` 在拥有真实清理队列的同时拥有这些证据：

- `run_recorded_root` 收集实际 root／Child 函数的 typed 历史。
- `run_function` 收集已成功执行的部分，包括后续指令失败的前缀。
- `dispatch` 收集 typed 清理成功、失败和已关闭的观察。
- 跨 owner 的观察接口合并实际来源证据。
- `apply_scalar_observed`／`apply_payload_observed` 执行原始可逆写入，并自动保留真实来源。
- `restore_scalar_observed`／`restore_payload_observed` 执行原始恢复，记录成功和失败；
  scalar 失败返回原来的线性逆操作，typed 失败保留实际锁内观察。
- `observe_payload_restore` 仍可显式导入原始 restore 接口产生的 tracked Attempt。
- 其他已支持的生命周期操作保留累积证据。

所有者的不变式保证：每个已记录事件的 typed 解码器都由这些来源覆盖。
证明接口 `observe_foreign` 也要求来源覆盖，不能插入没有证据的 payload 历史。
这些数据及合并、历史遍历都会被擦除，不增加运行时日志、锁、分配或用户依赖。

## 从存储所有权推出完整生产来源

`RecordedExecution` 的真实读取入口 `scalar_source_snapshot` 和
`payload_source_snapshot` 现在导出 `Producer::certified` 证明。对每个已经采集的
allocation，该证书从代码合同推出三项结论：

1. 每个真实同 allocation Journal 记录都有来源位置，包括绕过 recorded facade 的原始调用。
2. 每个成功恢复都对应更早的真实创建操作，地址、前后值与创建位置一致。
3. 每个创建位置最多成功消费一次。

这些是存储／宿主代码的后置条件，不要求调用方预先提供完整覆盖或唯一消费条件。
scalar 存储使用擦除的线性逆操作凭据：普通操作、一般效果、游标和批处理在实际写入时
创建凭据；恢复失败保留凭据，成功则消费凭据。真实 Restore 事件记录创建位置。
即使后续操作产生相同的值和 depth，也会使用不同的凭据。Journal 另有线性的最后写入
前沿，保证 owner 不能跳过同 allocation 的提交，即使两次记录相等。

typed 存储则证明恢复确实回到该逆操作创建时的前驱。语义历史重建当前 head 栈；
恢复后，被移除的 head 不能通过后续新版本重新成为当前状态。因此，即使接口是
`restore(&self)`，也能推出唯一成功消费。普通替换和退休仍完整保留在清点中，明确作为
不可逆恢复的边界。退休后的历史由不回指 owner 的擦除记录保存，因此 `capture()` 返回
`None` 后仍能采集完整来源。

证书覆盖单个 allocation 已采集的生命周期，不冻结未来修改，也不证明 payload 内部
任意可变数据。证明资源和退休历史都会擦除；显式来源采集读取已有存储锁，不克隆用户
payload 的 Arc。

## 从来源条件推出恢复

`run_recorded_root` 在真实函数返回处建立 `source_order`。后续 managed 调用、
清理调度、四个原始操作观察入口，以及同 Journal 的跨 owner 观察，都导出
`source_order_extends`。工作、Child、注册、回调确认、重试和释放步骤保留该证据。
验证客户端可以连续组合这些公开后置条件，不必在每次调用后重新提供顺序条件。
不同 Journal 保持独立时钟；手动导入证明事件不自动建立时间顺序。

`capture_invocation_census` 现会捕获真实共同终点，读取声明范围内实际 scalar／typed
所有者，保留 typed 来源证据，构造区间并调用 `recorded_census`。它是
`RecordedExecution` 的可执行方法；root 和 Child 共用注册报告合同。底层
`capture_recovery_interval` 接受真实起止回执，可复用已有生命周期终点。

`Interval::new` 按实际 Journal 提交位置生成来源明确的 `Event::Produced`，包含绕过
记录 facade 的原始操作。同一 `(Journal, allocation)` 的别名合并，每个实际可逆提交
只产生一个事件。历史回执由持久资源提取，不能伪造。typed 捕获现在会在真实存储锁内
读取共同 Journal 截面，退休后的对象也能捕获，证据不再止于该对象最后一次修改。

`Interval::initial` 从创建和消费历史推导区间开始前尚未消费的逆操作。
`Interval::origin` 证明每次成功恢复都来自这份初始清点或区间中的更早创建事件。
物理消费唯一性与每个提交只投影一次共同排除重复成功观察。这份清点描述来源，
不转移可执行 inverse 的所有权，也不声称任意历史逆操作序列都可以执行。

`recorded_census` 不再要求调用方提供 `coverage::complete`、`origins::admitted`、
顺序、读取间隙或末尾无修改条件。它推导这些条件，并证明剩余逆操作序列能从真实终点
恢复注册调用的 Begin 值，**或者返回具体的证明层阻断证据**：

- `Change` 指出可逆投影之外实际改变状态的 Journal 位置，包括破坏性替换或退休。
- `Earlier` 指出实际成功恢复的创建位置早于区间，但 inverse 不属于本次调用保留的
  逆操作序列。外部恢复可能合法地越过 Begin，此时不能宣称恢复到本次 Begin。

实际对象声明范围、有效注册报告及其清理保留关系仍是输入。证书不会自动发现任意
JavaScript 对象，也不证明外部回调。区间及诊断会擦除，这个接口不实现自动回滚或运行时
状态提示。显式收集会取得真实存储／Journal 读锁，但不保留运行日志或额外用户 Arc。
原来手工观察的低层路径保留为 `observer_census` 与 `recover_observer_censused_prefix`，
其来源条件仍需明确提供。

`recover_recorded_prefix` 将上述结果与真实注册调用保留的逆操作组合。
对任意满足条件的观察前缀，构造出的剩余严格逆操作序列有定义，并恢复本次调用的
Begin 值。此时可以仍存在外部写入或失败的清理尝试。这是公式 (55) 在 managed 值上的
特化，其中包含已准入外部 forward 的逆操作，并不意味着本地 owner 可以消费其他
owner 的资源。

`unload_recovers_from_source_history` 进一步组合已经完成的外部 owner、实际 native
Unload、原始 Child 完成记录和 forward 登记清偿，在同一个真实 native snapshot 上
证明值恢复及 Child 终态。Child 完整性、外部观察覆盖和末尾无相关写入等原有条件仍然保留。

新的 [capture_release_census](r3-final-recovery.zh-CN.md) 路径使用覆盖至真实 native
快照的完整生产者区间，从 Unload 推出本地恢复，检查全部外部创建和原始 Child 义务，
返回同一截面上的恢复结果或具体阻断。非空终态 owner／Child 客户端推导恢复闭合，
无需观察覆盖或 Unload 后无相关写入前提。

| 审查环节 | 代码 |
| --- | --- |
| 锁内取得真实恢复证据 | [payload_inverse.rs](../crates/cordis-kernel/src/payload_inverse.rs)、[payload_attempt.rs](../crates/cordis-kernel/src/payload_attempt.rs) |
| 持久前缀合并与一致性 | [shared_value_sources.rs](../crates/cordis-kernel/src/shared_value_sources.rs) |
| 函数／清理来源与值解码 | [managed_value_sources.rs](../crates/cordis-kernel/src/managed_value_sources.rs)、[cleanup_recovery.rs](../crates/cordis-kernel/src/cleanup_recovery.rs) |
| 实际原始写入／恢复的自动捕获 | [managed_lifecycle_values.rs](../crates/cordis-kernel/src/managed_lifecycle_values.rs) |
| 生产路径保持的顺序证据 | [managed_source_order.rs](../crates/cordis-kernel/src/managed_source_order.rs)、[managed_lifecycle_order.rs](../crates/cordis-kernel/src/managed_lifecycle_order.rs) |
| 线性最后写入所有权与完整 allocation 投影 | [joint_owner_history.rs](../crates/cordis-kernel/src/joint_owner_history.rs)、[joint_execution.rs](../crates/cordis-kernel/src/joint_execution.rs) |
| 实际 scalar 逆操作凭据、创建与唯一消费 | [scalar_ownership.rs](../crates/cordis-kernel/src/scalar_ownership.rs)、[reversible_value.rs](../crates/cordis-kernel/src/reversible_value.rs) |
| typed 前驱、唯一恢复与退休来源 | [payload_semantic_history.rs](../crates/cordis-kernel/src/payload_semantic_history.rs)、[payload_source_history.rs](../crates/cordis-kernel/src/payload_source_history.rs) |
| 宿主实际返回的统一生产者证书 | [managed_producer_sources.rs](../crates/cordis-kernel/src/managed_producer_sources.rs)、[managed_lifecycle_values.rs](../crates/cordis-kernel/src/managed_lifecycle_values.rs) |
| 完整 Journal 清点及间隙／尾部推导 | [managed_source_coverage.rs](../crates/cordis-kernel/src/managed_source_coverage.rs) |
| 从来源推出值连续 | [managed_source_link.rs](../crates/cordis-kernel/src/managed_source_link.rs) |
| 从来源推出逆操作仍可用 | [managed_source_obligations.rs](../crates/cordis-kernel/src/managed_source_obligations.rs) |
| 所有者不变式及恢复入口 | [managed_lifecycle_history.rs](../crates/cordis-kernel/src/managed_lifecycle_history.rs)、[managed_lifecycle_sources.rs](../crates/cordis-kernel/src/managed_lifecycle_sources.rs) |
| 自动区间及区间前义务 | [managed_producer_interval.rs](../crates/cordis-kernel/src/managed_producer_interval.rs)、[managed_producer_event.rs](../crates/cordis-kernel/src/managed_producer_event.rs) |
| 实际宿主捕获与 root／Child 恢复 | [managed_producer_capture.rs](../crates/cordis-kernel/src/managed_producer_capture.rs)、[managed_producer_recovery.rs](../crates/cordis-kernel/src/managed_producer_recovery.rs) |
| 实际共同 native 截面 | [managed_recovery_cut.rs](../crates/cordis-kernel/src/managed_recovery_cut.rs) |

## 历史区间验证与剩余边界

以下结果属于上一轮生产者区间批次。当前最终组合的验证见[最终恢复](r3-final-recovery.zh-CN.md)；
开发记录会检测完整检查后发生的源码变化。

生产者区间批次于 2026-10-19 通过集中局部验证，使用固定版本
Verus `0.2026.10.04.1687598`：**541 项通过，0 错误**。检查范围为受影响的
历史、Journal、typed 来源和 managed 恢复模块，并非整个 crate：

```bash
source scripts/toolchain-env.sh
./scripts/verify.sh \
  --verify-only-module reversible_value::history \
  --verify-module reversible_value::joint \
  --verify-only-module reversible_value::payload \
  --verify-module reversible_value::payload::source \
  --verify-module reversible_value::payload::semantic_history \
  --verify-module reversible_value::payload::restoration \
  --verify-module reversible_value::managed \
  --num-threads 2 --triggers-mode silent --output-json
```

`managed_function`、`native_runtime`、`registered_value_function` 和
`reversible_value` 四组内核测试共 **69 项通过**。内核 Clippy
（`--all-targets --all-features -- -D warnings`）、格式检查以及论文覆盖、审查和
refinement 检查也通过；Cargo 检查使用 `--locked --offline`。
本批全内核开发验收及全量负向控制：**not_run**。

两个非空 registered root 回归覆盖新的实际采集入口：
`invocation_census_collects_raw_aliases_without_retaining_payloads` 包含原始写入、
重复句柄别名、清理干扰、恢复及 native 重试，并检查值、深度和用户 Arc 引用计数；
`invocation_census_reads_destructive_and_retired_producers` 检查破坏性替换后采集，
以及退休后的重复采集。区间和 `Issue` 值会擦除，运行断言不验证这些证明对象；
其来源、恢复结论和阻断合同由 Verus 检查。

新增回归 `producer_snapshots_cover_raw_calls_repeated_states_and_retirement` 位于
[managed_function.rs](../crates/cordis-kernel/tests/managed_function.rs)，执行绕过 facade 的
原始调用、scalar 恢复失败与重试、重复 scalar 状态、重复 typed 内容、旧 typed 逆操作
拒绝、替换、退休及重复读取退休来源，同时检查来源采集不额外保留用户 Arc 引用。
运行时断言不检查已经擦除的来源证明，该保证由 Verus 检查。

现有非空跨 owner 回归通过本轮修改后的生产接口执行 scalar／typed 写入、函数失败
前缀、清理干扰、外部恢复、native 重试及成功释放。它属于运行时回归，仍不是对共同
恢复截面定理所有前提的完整实例化。[开发验收记录](development-report.json) 才是
全流程检查的依据；局部证明检查不能代替它。

这一接口后续的负向控制需拒绝：使用旧 inverse 的 witness 代替锁内当前状态、丢弃
观察者的来源、遗漏冲突写入、使用没有创建来源的逆操作，以及重复成功观察。
全量负向回归和局部校准仍应独立标注状态，开发验收通过不意味着执行了它们。
新增待补控制应拒绝：跳过 owner 写入前沿更新、不带创建凭据的 scalar 恢复、重复消费
同一凭据、typed 恢复到无关旧 head，以及丢弃退休历史。
自动区间还需补充控制，拒绝遗漏／重复的修改、伪造的收据前缀、隐藏的区间前恢复义务，
以及被静默忽略的破坏性屏障。

本结果没有构造删除 owner 后的合法生命周期执行，没有将值观察推广到所有中间截面的
publication／pending 效果，也不证明任意回调、调度公平性或终止。这些都不能由公式
(55) 的值相等直接推出。原论文审计结论与 R3 退出条件保持不变。
