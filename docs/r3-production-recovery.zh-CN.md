# R3：从受管执行历史推出恢复条件

[English](r3-production-recovery.md) · [全 Episode 恢复](r3-episode-recovery.zh-CN.md) · [里程碑](paper-refinement-roadmap.zh-CN.md)

本批将生产混合 scalar／typed 解释器的真实 Begin、调用返回观察接到其保留的逆操作队列。
typed 历史还通过带索引的 Apply／Replace／Restore 事件解释已恢复的干扰和实际清理重试。R3 仍在进行：这是生产恢复的组合基础，
尚不是所有生产 Episode 的完整式 (55)，也不是合法生命周期删除定理。

## 真实入口保证什么

存储 root 和 Child 使用的 `Execution::run_function`，现在对成功函数和失败前保留的前缀
建立 `Report::recovery_history`。`NativeRuntime::run_managed_root` 传递同一合同。

每次写入采用真实的 `(Journal, allocation)` 地址。两次写入同一地址之间的 **quiet gap**
要求所有中间 Journal 提交都保留该分配对象的完整记录状态；允许其他对象上的提交，也允许
被拒绝的 scalar 尝试。服务名称不同不代表独立，不同 Journal 中数值相同的 key 也不代表
同一个对象。

typed 间隔也可以在更高 revision 上回到先前的**语义 head**。持久来源历史进一步证明
完整语义状态相等；仅 payload 内容相等不够。`restored::between` 会定位两次写入之间
真实的 `PayloadRestore`。因此允许外部临时写入后完成恢复，不必把这个间隔误判为 quiet。

证明从真实历史和这些间隔条件推出：同一对象相邻写入的输出／输入状态衔接。
`recovery_word` 随后推出正向重放与逆操作有定义，不要求调用方预先假设其中任何一个成功。
`recover_retained` 将结果应用到实际混合清理队列的后缀；`recovered_aliases` 再将恢复结果
映射到指向这些对象的全部服务名称。

输入表是**函数对每个分配对象首次写入时的真实观察**，不宣称它是跨 Journal 的同时快照。
恢复起点是函数记录的各对象最终写入状态；之后的外部写入仍可能阻塞真实清理。quiet gap
是根据 ghost 历史检查的充分条件，不是调度器承诺，也不要求禁止其他插件运行。

## 真实 Begin 的来源

registered root 与 Child 分发现在通过 `NativeRuntime::current_begin` 保留持久的 `Begin`
见证。位置来自当前 native owner 及其带索引的真实执行历史，不由调用方提供期望检查点；
同时保留实际 setup 票据和工作域。

`run_function_following` 在首个效果之前向实际收据表加入该见证。同一 Journal 中的每次
成功写入都在这个检查点之后，包括失败函数已保留的前缀。原 `run_function` 使用同一个
解释器，不传入前置见证。registered 返回收据也在该检查点之后，覆盖空函数和准入拒绝。
`RegisteredReport::episode_interval` 将这些事实连接到实际返回的 owner 和工作票据。
其他 Journal 的收据保持独立的域，不由此虚构跨 Journal 顺序。

`managed_endpoint` 现在从真实 Journal 检查点解释 scalar／typed 值。typed 值由逆操作
保留的真实来源历史按记录的 revision 解码，不为缺失、退休或历史不足的记录虚构值。
`RegisteredReport::begin_values` 使用真实 Begin 之后的保留检查点，`return_values`
使用真实调用返回收据。

实际 `run_managed_root` 返回时建立 `endpoint_recovery` 和 `retained_recovery`。
在 `endpoint_source` 条件下，证明：

```text
正向重放（真实函数步骤，Begin 值）= Some（返回值）
逆向执行（实际保留的混合队列后缀，返回值）= Some（Begin 值）
```

条件要求相关写入属于同一 Journal；从 Begin 到每个对象的首次写入、从最后一次写入到
返回之间保持 quiet；同一对象相邻写入的间隔满足可衔接条件。内部间隔允许上述 typed
恢复。期望堆状态和逆操作成功都不是前提。函数失败时，对已成功执行的前缀保持同一保证。

这些表覆盖本次调用实际触及的分配对象。混合派发器现在保留真实队列边界，并建立严格
恢复、失败保留和重试合同。[清理组合](r3-cleanup-recovery.zh-CN.md) 从实际返回结果
出发，在真实读取衔接已证明的返回轨迹时，推出有限尝试成功及 Begin 值恢复。
[交错恢复](r3-interleaved-recovery.zh-CN.md) 现在纳入外部受管写入、阻塞尝试和恢复，
从后续真实成功恢复推出逆操作全部消费，并解码同一个真实 Unload 检查点。这个值结论
具有明确来源及尾部无修改条件；完整 publication／Child 效果、生产轨迹构造及任意中间
检查点仍是独立待完成工作。

此前 native Begin、受管执行、typed payload、Mixed／Fresh 脚本及 Xor 子树的组合
定向验证通过：401 verified，0 errors。当前交错恢复／Unload 集成的已验证范围与待验收项
记录在[交错恢复](r3-interleaved-recovery.zh-CN.md)。此前完整开发记录器在打包验收前被中断，其全内核、Rust 与 Node 原始结果
不能认证后续修改的源码；下次集成验收仍需刷新完整开发记录。

端点与恢复合同组合后的待验收清单：

- 多次激活及动态注册的 Child root 选中自己的真实 Begin，覆盖其他 owner 的交错提交。
- 空函数、准入拒绝和保留的失败前缀保持同一调用来源与返回因果关系。
- 外部 Journal 不被赋予虚构的 native Journal 位置。
- 替换为旧 Episode 或丢弃首个因果收据的合同突变，在指定因果合同处被拒绝。
- 别名和失败前缀恢复真实 Begin 值；边界上的写入及退休对象不能被当作 quiet 端点。
- 交错的 typed 写入／恢复在更高 revision 上返回旧 head；单纯同值替换不满足条件。
- 将替换误分类为恢复、或切断实际队列与端点关系的突变，应在指定语义合同处被拒绝。

## typed 历史为什么需要真实见证

公共 Journal 记录 payload 身份与单调版本，typed 语义历史保留在其类型所有者内。
仅凭版本号，无法证明两次 payload 观察具有相同语义。

`history::Witness::prefix` 现在比较真实的持久资源见证。typed admission 保留这个见证，
函数报告把它与既有写入／注册收据一起保存。`linked_pair` 将 Journal 间隔接到 typed
历史前缀的一致性，而不是要求调用方提供“历史相等”的前提。新增资源和表都会擦除，不为
保存这些见证增加运行时历史缓冲、payload 克隆或锁操作。

`payload::semantic_history::valid` 还将每个保留的 typed 版本对应到带索引的真实
Journal 变更。实际构造、原始 replace、受管 apply 和 restore 维护该不变式：Apply
分配新 head 并增加一个未完成逆操作；原始 Replace 分配新 head 并重置 depth；Restore
返回更小的 head 并减少一个未完成逆操作。只有真实 Restore 才能落到更早的 head。
这些合同直接约束运行中的存储操作，不接受调用方另行提供一份历史。

## 实际清理、冲突与重试

真实持锁 typed 读取现在明确保证，其历史包含逆操作产生时的正向历史。
`Attempt::strict_domain` 证明：

```text
这次真实恢复尝试成功
    当且仅当其存活对象的语义状态等于逆操作捕获的输出
    当且仅当其语义 head 等于逆操作期待的 head
```

成功恢复捕获的输入。单调读取版本可以更新：外部逆操作恢复语义 head 时，防止旧读取被
重新接受的 revision 仍会递增。因此语义可以恢复，而旧读取仍保持失效。
`Attempt::resumed_origin` 现在还证明：若本次尝试在更高 revision 上成功，读取之前
必有一个真实 `PayloadRestore`，并定位其索引。真实 restore／cleanup 返回同时建立
这项来源保证、严格定义域和冲突见证。

存活对象的失败尝试通过 `conflicting_write` 定位到同一对象上的真实后续变更；关闭对象
通过 `retirement_write` 定位到真实 `PayloadRetire`。如果从正向提交到持锁读取之间保持
quiet，就能推出恢复成功。这些结论由实际 restore 与 typed 清理返回路径建立。既有队列
合同继续保留失败逆操作，并区分新重试票据和旧确认。上述结果不承诺冲突插件最终会撤销
写入，也不承诺调度器最终重试清理。

## 审查与复现

| 连接 | 源码 |
| --- | --- |
| 可比较的真实历史 | [reversible_value/history.rs](../crates/cordis-kernel/src/reversible_value/history.rs)：`Witness::prefix`、`compatible_map` |
| 运行 admission 与报告保留 | [cleanup_groups/payload.rs](../crates/cordis-kernel/src/cleanup_groups/payload.rs)、[reversible_value/managed.rs](../crates/cordis-kernel/src/reversible_value/managed.rs) |
| Journal 间隔到实际 scalar／typed 状态衔接 | [reversible_value/managed/recovery.rs](../crates/cordis-kernel/src/reversible_value/managed/recovery.rs)：`linked_pair`、`establish_recovery` |
| 混合逆序列及真实队列后缀 | [reversible_value/managed/recovery/word.rs](../crates/cordis-kernel/src/reversible_value/managed/recovery/word.rs)：`defined`、`recover_retained` |
| 真实 Begin 及 registered 执行区间 | [lifecycle_state/native/runtime/episode.rs](../crates/cordis-kernel/src/lifecycle_state/native/runtime/episode.rs)、[reversible_value/managed/episode.rs](../crates/cordis-kernel/src/reversible_value/managed/episode.rs)、[reversible_value/managed/root.rs](../crates/cordis-kernel/src/reversible_value/managed/root.rs) |
| 真实 Begin／返回值与保留队列恢复 | [reversible_value/managed/episode/endpoint.rs](../crates/cordis-kernel/src/reversible_value/managed/episode/endpoint.rs)、[reversible_value/managed/root/recovery.rs](../crates/cordis-kernel/src/reversible_value/managed/root/recovery.rs) |
| typed 变更历史与已恢复干扰 | [reversible_value/payload/semantic_history.rs](../crates/cordis-kernel/src/reversible_value/payload/semantic_history.rs)、[reversible_value/managed/recovery/restored.rs](../crates/cordis-kernel/src/reversible_value/managed/recovery/restored.rs) |
| typed 尝试、失败原因与严格定义域 | [reversible_value/payload/restoration/attempt.rs](../crates/cordis-kernel/src/reversible_value/payload/restoration/attempt.rs)、[reversible_value/payload/restoration/attempt/recovery.rs](../crates/cordis-kernel/src/reversible_value/payload/restoration/attempt/recovery.rs) |

[运行案例](../crates/cordis-kernel/tests/managed_function.rs)包括：两个 provider 的别名指向
同一 scalar／typed 对象；外部同值写入仍会阻塞清理；真实逆操作保留；新票据重试；混合
LIFO 队列恢复原值；旧读取拒绝；重复恢复与退休对象恢复拒绝。

```sh
source scripts/toolchain-env.sh
cargo test -p cordis-kernel --test managed_function --locked --offline
python3 scripts/check-profile-controls.py production
python3 scripts/record-development.py --offline
```

局部负控分别把真实变更误判为 quiet，以及放宽实际 typed head 守卫、允许已消费的 head
通过。每项都要求新鲜匹配正例、完整突变编译及准确合同拒绝。绑定源码的报告位于
`target/r3-production-controls/report.json`，完整负控／calibration 仍标为 `not_run`。
开发验证记录独立保存；旧记录的通过不能自动应用于变化后的源码。

## R3 尚待完成

- 将真实 Begin／Unload 的条件值恢复扩展到完整生产历史和所有中间检查点。
  [释放守卫组合定理](r3-interleaved-recovery.zh-CN.md#从真实释放守卫推出成功恢复)已推出本地闭合；
  注册成员关系已由运行中的解释器给出，仍需从准入生产执行构造完整消耗确认覆盖。外部恢复闭合保留为显式条件。
- 将 publication、动态 Child、待注册逆操作接到已建立的外部写入／失败／恢复／重试
  轨迹，不预设一致快照或撤销成功。
- 为明确允许的 Child／consumer 情况构造合法剩余执行，完成式 (55)／(56) 的整体审查。

原文定理 68／推论 69 仍为 `partial`，R3 退出条件和整篇论文审计不变。任意 payload 内部
状态、宿主回调和外部 I/O 不属于 typed replacement 的保证。
