# R3：同一真实 native 快照上的最终恢复

[English](r3-final-recovery.md) · [来源连续性](r3-source-continuity.zh-CN.md) · [里程碑](paper-refinement-roadmap.zh-CN.md)

本页对应 R3 剩余工作的第 1 包：将自动捕获的生产者区间、实际 native Unload、
外部恢复和原始 Child 义务组合到同一个真实快照。**R3 整体仍在进行中。**
这将公式 (55)／(56) 附近的受管值恢复式连接到真实存储和生命周期代码，
并未完成原论文不受限制的一般恢复或合法删除定理。

## 保证是什么

`RecordedExecution::capture_release_census` 接收真实成功的释放结果、注册调用报告，
以及该调用声明对象范围内的 scalar／typed 句柄。它读取真实 native 快照和生产者历史；
调用方不需要提供成功恢复列表或期望的最终值。

擦除的 `FinalCensus` 要么指出具体的来源阻断，要么在**同一个快照**上证明：

- 本次调用涉及的 scalar／typed 值等于真实 Begin 时的值。
- 全部原始 native Child 义务都有匹配的完成来源，Child 的 owner／publication 已移除；
  随后的注册表 Remove 保持这一终态。
- 本次正向写入没有尚待登记逆操作的 pending 条目。
- 本次真实 Begin 和实际 native Unload 都在保留的 Journal 前缀中。

证明查询返回 `None` 当且仅当调用边界清晰、区间内全部正向写入都有后续匹配恢复，
且全部原始 native Child 义务都有匹配的已收集完成记录。
父插件 Unload 本身不能推出外部恢复或 Child 完成。

```rust,ignore
// owner.release(...) 已返回真实成功的 ReleaseOutcome：
let recovery = owner.capture_release_census(
    &world, &report, group, offset, &release, &scalars, &payloads,
);
```

这是面向验证的 API。受验证调用方还需满足报告保留所有权、登记和同 Journal 来源顺序
合同，生产方法负责维护这些证据。`RecoveryCapture::evidence` 是 `Ghost`，普通 Rust
不能将其作为运行时恢复状态读取。捕获只观察已经完成的工作，不调度清理或执行回滚。
显式捕获会读取既有存储／Journal 锁，不保留运行历史或额外用户 payload Arc。

## 每个结论来自哪里

| 义务 | 真实来源与证明 |
| --- | --- |
| 本地恢复 | 真实逆操作登记、保留的派发历史和实际 Unload 守卫强制存在成功匹配的确认；`restoration_before_unload` 定位其实际写入。 |
| 完整区间 | 存储所有权证书产生每次相关提交，包括记录入口之外的原始调用。`includes_restore` 按来源身份、创建位置和 typed 历史一致性，将真实清理接到独立投影。 |
| 外部恢复闭合 | `unload_census` 检查每个实际区间正向写入；非空客户端还能从第二份真实注册报告的终态队列及 Unload 推出闭合，无需提供成功观察覆盖。 |
| Child 完成 | 对照全部原始 native 逆操作，匹配共享槽出生、退休和 Child 自身 Unload。native Ledger 将终态推进到同一个后续快照。 |
| 终点值 | 来源覆盖和唯一消费推导剩余逆操作；本地与外部完成将其排空，实际快照解码得到 Begin 值。 |

区间一直覆盖到共同快照，包括本地 owner Unload 后的写入；不假设 Unload 到捕获之间
没有相关修改。来源边界继续明确保留：

| 阻断 | 含义 |
| --- | --- |
| `Boundary(Change)` | 破坏性替换、退休等真实变化没有可逆投影。 |
| `Boundary(Earlier)` | 实际成功恢复越过调用边界，不属于本次保留的逆操作序列。 |
| `Foreign` | 区间中的真实创建写入在该截面前没有后续匹配恢复。 |
| `Child` | 某个原始 Child 逆操作在该截面没有匹配的已收集完成来源。 |

## 非空组合与运行复现

`nonempty_unload_client` 组合两份非空真实注册报告、含外部正向写入的非空区间，
以及一个已分配的 native Child。其来源范围指出每次区间写入对应的创建报告，以及
真实 Child 出生／退休／Unload。它推出外部恢复闭合和 Child 完整性，只可能剩下真实的
调用边界阻断。因此，边界清晰即可推出完整终点保证。该有限范围允许失败和重试，
不要求预先假设逆操作成功或期望终点值。

可执行回归 `final_recovery_capture_spans_foreign_retry_and_a_later_child_unload` 包含：

1. 父插件与外部 writer 修改同一 scalar／typed 对象；writer 同时消费父插件所创建
   Child 的 publication。
2. 实际 Child 退休，以及外部写入导致的父插件清理失败。
3. 外部恢复并 Unload，父插件用新票据重试后成功 Unload；此时 Child 仍 Active。
4. Child 随后自行 Unload，Remove 后再次捕获，用户 Arc 计数不增加。
5. 本地 Unload 后的原始写入、恢复及破坏性替换；捕获不会修改这些真实值。

运行断言检查状态、值、票据及所有权，不检查擦除的 `Obstruction` 变体，
也不代替非空证明客户端全部来源前提的实例化。相关合同由 Verus 独立检查。

## 审查与验证

| 入口 | 作用 |
| --- | --- |
| [managed_release_path.rs](../crates/cordis-kernel/src/managed_release_path.rs) | 实际 Unload 守卫定位本地成功恢复。 |
| [managed_producer_matching.rs](../crates/cordis-kernel/src/managed_producer_matching.rs) | 将实际 scalar／typed 恢复匹配到完整生产者投影。 |
| [managed_unload_census.rs](../crates/cordis-kernel/src/managed_unload_census.rs) | 完整来源查询、具体阻断及同快照恢复定理。 |
| [managed_unload_capture.rs](../crates/cordis-kernel/src/managed_unload_capture.rs) | 从实际释放结果、快照和存储执行捕获。 |
| [managed_unload_client.rs](../crates/cordis-kernel/src/managed_unload_client.rs) | 非空外部 owner／Child 组合。 |
| [managed_function.rs](../crates/cordis-kernel/tests/managed_function.rs) | 可达的失败重试与 Child 延后释放案例。 |

使用固定工具链复现集中检查：

```bash
python3 scripts/record-development.py --offline
python3 scripts/check-r3-final-cut-controls.py
```

[开发记录](development-report.json) 将全内核证明、运行、文档和包检查绑定到准确的源码
哈希。`python3 scripts/record-development.py --check` 只检查记录是否过期，不会重新
运行证明。来源连续性页面保留的旧局部计数不能认证已经修改的源码。

两个定向控制分别故意跳过外部恢复或 Child 完成。严格运行器要求新的正向基线、
变异代码整体编译成功，并在指定恢复合同处拒绝；无关错误或求解超限不算通过。
本地报告位于 `target/r3-final-cut-controls/report.json`。
这些命令的全量负向回归与 scoped calibration 均为 **not_run**。
开发验收与发版验收、整篇论文完成分别记录。

## R3 仍未完成的部分

[第 2 包](r3-observation-recovery.zh-CN.md)现已补齐 native 中间截面的完整 publication／owner／pending 观察，并在本页捕获结果中提供同一快照上的独立证明查询。
[第 3 包](r3-host-recovery.zh-CN.md)现已将普通 Rust 宿主修改入口接到记录型所有者。Node 独立协议的恢复及合法剩余生产执行仍需要后续工作。声明对象范围、实际报告所有权和来源身份匹配继续作为输入。
本包不证明任意回调或外部 I/O 的真实性，也不证明调度公平、最终清理、全局终止或合流。
