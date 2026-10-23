# R3：中间截面上的 publication 与 pending 恢复

[English](r3-observation-recovery.md) · [值与 Child 最终恢复](r3-final-recovery.zh-CN.md) · [里程碑](paper-refinement-roadmap.zh-CN.md)

本页对应 R3 剩余工作的第 2 包，完成 native 生产观察中的精确 typed publication、
Episode owner，以及等待逆操作登记的受管写入。每个中间截面都来自真实共享 Journal，
包括加载、清理失败和重试期间。**R3 整体仍在进行中。** [第 3 包](r3-host-recovery.zh-CN.md)现已完成普通 Rust 宿主所有权迁移；合法剩余生产执行仍属于后续工作。

## 保证是什么

`NativeRuntime::recovery_snapshot` 在较早的真实 Journal 快照之后捕获新快照，
从运行时完整 typed 历史构造恢复证据。调用方无需提供预期终值或成功清理列表。

```rust,ignore
let before = world.publication_snapshot();
// 实际执行 root/Child、发布、清理和重试。
let recovery = world.recovery_snapshot(before.joint());
```

捕获的区间解释两次读取之间的**每个截面**，将三项观察重建如下：

| 观察 | 原有保留部分 | 新创建部分 |
| --- | --- | --- |
| typed publication | 较早发布的完整 payload 引用、imports 和 Begin 捕获，保留至该 provider 的 Unload | 实际 Finish 创建、尚未被随后 Unload 消费的发布 |
| Episode owner | 较早 owner 保留至其 Unload | 实际 Begin 创建、尚未被随后 Unload 消费的 owner |
| pending 逆操作登记 | 较早受管写入保留至其实际 RegisterInverse 提交 | 实际受管正向写入中尚未完成登记的项 |

这些是从来源推导的重建公式，不使用预设目标表。native 状态下标由原始 Journal
记录确定，生命周期转换之间的值、work 和清理提交也保留在区间中。当前每个
publication／owner 都有唯一且尚未消费的创建来源。同一 provider 的多轮 Episode
即使使用相同 Arc，也以不同的创建位置区分。pending 项对应实际创建写入及对象，
真实登记只能消费它一次，后续截面不能重新出现这项义务。

捕获还自动执行完整观察查询。证明结果为 `None`，当且仅当这三项观察的全部来源效果
闭合；由此推出前后 publication、owner 和 pending 表精确相等。否则提供具体阻断：

| 观察 | 诊断 |
| --- | --- |
| publication／owner | `Removed`：第一次实际 Unload 消费了起始截面已存在的项。`Introduced`：实际 Finish／Begin 创建的项在新截面尚未被消费。 |
| pending | `SettledInitial`：实际登记消费了起始截面的 pending 义务。`Outstanding`：区间中新产生的受管写入仍未登记逆操作。 |

这些是相对于所选截面的**恢复边界诊断，不是运行错误**。登记原有 pending 逆操作是
正常进展，但确实改变了该截面的 pending 表。新 Episode 发布相同数据，也不等于
恢复旧创建身份。来源效果闭合比终值碰巧相等更强。

## 与值和 Child 恢复组合

`RecordedExecution::capture_release_census` 现包含 `observations` 和
`observation_issue`。它们与值／Child 查询使用**同一份实际 native 快照**，起点是
真实 Begin 之前的截面。因此调用期间的 publication 和 pending 变化也进入解释，
不会只从调用返回处开始观察。需要分别审查两份结果：值恢复不能自动推出发布／owner／
pending 观察恢复；逆操作登记也不能代替逆操作实际执行成功。

`Interval::completed_lifetimes` 是消费真实来源的非空证明客户端。它要求区间实际
包含 Begin 和受管正向写入，保留起始资源，并为新生命周期及写入关联真实的后续
Unload 和登记提交，随后推出来源闭合与三张表恢复；终点相等不是输入前提。
多个 provider、重复 Episode 和中间失败可以交错。

`registration_microsteps` 检查一项实际成功登记：创建写入之后、队列插入之前的每个
截面都有对应 pending 项；登记之后的每个截面都没有它，其他登记也不能再次消费。
因此函数返回快照看不到的内部步骤也进入证明。

## 生产边界与运行成本

这些 API 面向验证使用。调用方建立较早快照的同 Journal／native 来源关系，实际
读锁建立后续捕获的时间顺序。历史 typed 观察取自当前 native 所有者持续维护的完整
历史，不比较两份由外部独立提供的 typed 历史。

`interval`、`issue`、`observations` 和 `observation_issue` 都是会被擦除的 `Ghost`
证据，普通 Rust 不能将它们作为运行时恢复状态读取。捕获读取既有 Journal 锁，不保存
运行日志，也不增加用户 payload Arc。它观察执行，不执行回滚或调度清理。

本包恢复的投影是 native publication／owner 表和 Journal 的受管逆操作登记表，
不宣称所有 control／heap／configuration 记录相等，不恢复任意回调内部状态，
不证明外部 I/O 真实性，也不涵盖 Node 独立的多版本 publication 协议。
值／Child 保证及其声明对象范围仍单独约定。普通 Rust 宿主现已使用[记录型所有权](r3-host-recovery.zh-CN.md)；一般合法删除、公平性、
全局终止与合流尚未由本包完成。

## 审查与复现

| 入口 | 审查内容 |
| --- | --- |
| [native_registry_recovery.rs](../crates/cordis-kernel/src/native_registry_recovery.rs) | 唯一创建来源、第一次消费 Unload、精确重建与恢复查询。 |
| [joint_pending_recovery.rs](../crates/cordis-kernel/src/joint_pending_recovery.rs) | 中间 pending 完整记录、真实登记来源及唯一消费。 |
| [native_observation_recovery.rs](../crates/cordis-kernel/src/native_observation_recovery.rs) | 原始截面定位、完整来源范围及组合观察恢复。 |
| [native_runtime.rs](../crates/cordis-kernel/src/native_runtime.rs) | 实际有序快照与恢复捕获。 |
| [managed_unload_capture.rs](../crates/cordis-kernel/src/managed_unload_capture.rs) | 与真实注册调用的值／Child 恢复共用截面。 |
| [native_observation_client.rs](../crates/cordis-kernel/src/native_observation_client.rs) | 非空完整生命周期与登记微步骤。 |
| [native_runtime.rs 测试](../crates/cordis-kernel/tests/native_runtime.rs) | 失败、重试、provider 释放阻塞、相同 Arc 再发布，以及保留快照时的 payload 回收。 |

运行案例检查实际状态、payload 所有权和新 Episode 身份，不能读取擦除的诊断，也不
代替全部证明客户端前提的实例化。受管值／Child 回归还使用实际 scalar／typed 写入
及保留的逆操作登记，执行合并后的捕获入口。

```bash
python3 scripts/record-development.py --offline
python3 scripts/check-r3-observation-controls.py
```

准确的证明、运行及包检查结果以绑定源码的[开发记录](development-report.json)为准。
`--check` 只检查哈希，不重新验证。两个定向控制故意省略 publication 或 pending
查询，必须整体编译成功、通过新的匹配正向基线，并在指定来源闭合合同处被拒绝；
超时、求解超限或无关错误不算通过。本地报告位于
`target/r3-observation-controls/report.json`。

上述命令的全量负向回归及 scoped calibration 均为 **not_run**。开发验收区别于
发版和整篇论文验收。原始编号论文审计结论不变：本包扩展与式 (55)／(56) 配合使用的
生产观察；pending 逆操作登记仍是明确的实现 refinement，不冒充论文原子规则，也不
代表原论文不受限制的一般恢复定理已经成立。
