# R3：删除原生执行中的中间 Episode 区间

[English](r3-native-deletion.md) · [宿主所有权](r3-host-recovery.zh-CN.md) · [里程碑](paper-refinement-roadmap.zh-CN.md)

第 4 包从**真实生产快照构造合法的剩余 native 生命周期／publication／owner 历史**。
选择按历史区间进行，因此同一插件更早、更晚的 Episode 保持不变。
这完成了一类原生观察投影上的构造性删除；**R3 仍在进行中**。

## 保证

`NativeRuntime` 的认证快照已经包含真实 Journal 的完整、有序、带类型观察投影。
当所选区间满足来源条件，构造器：

- 删除选定 owner 的激活、清理步骤，以及选定 Child 的登记。
- 按原顺序保留其他全部步骤，保留真实 publication 和 Episode owner 的完整内容。
- 证明每个保留的 native 步骤合法，包括 Begin 准入和 Unload 的 consumer 守卫。
- 在闭合边界接回完全相同的源状态，保留区间外所有转换，包括同一 owner 的其他 Episode。
- 从真实分配历史推出目标身份不复用，并将每个保留标签映射回原始 native Journal 提交。

调用方**不提供目标轨迹合法性、目标 Unload 成功或预期终态表**。
结果包含论文控制执行关系。`Restart` 仍是显式宿主扩展：只有目标不含 Restart
才推出严格论文执行关系；源轨迹不含 Restart 足以保证这一点。

## 来源条件与诊断

`Window { start, end, region }` 使用状态下标，选择 `[start, end)` 中的转换。
region 指定被删除 Episode 的 owner，以及其中连登记一并删除的名字。
所有条件都检查真实源历史，包括中间状态：

| 来源条件 | 作用 |
| --- | --- |
| 两个边界处，选中 owner 均为 Inactive、承诺为空、无 publication／owner 条目 | 使中间区间能与原前缀、后缀准确接合。 |
| 被删除名字在两个边界都未登记 | Retire 和 Unload 不等于 Remove；仍登记的 Child 阻止这种准确接合。 |
| 保留声明不依赖选中 owner 的 provisions | 保留 consumer 不会失去 Begin 或已安装视图需要的 provider。 |
| 保留登记不引用被删除 parent | Child 不能在其登记父节点消失后继续保留。 |
| 所选 parent 在区间内产生的 Insert 进入删除出生集合 | 不能删除创建者 Episode，却悄悄保留它创建的 Child。 |

证明查询可诊断下标越界、region 非法、打开／闭合边界未满足、缺失 parent、
遗漏 consumer 或遗漏 Child 出生。这表示当前允许类别的条件未成立，
并不声称所有其他删除策略都不可能。

## 真实入口与组合

`NativeRuntime::deletion_snapshot` 调用已有真实快照入口并构造证书；
`Snapshot::delete_window` 查询已捕获的快照；`Snapshot::delete_since_begin`
从真实收据和保存的位置定位原始 Begin，不把稍后的收据末端当成 Begin。

受管调用的 `RecoveryCapture::with_deletion` 使用与既有值／Child census、
publication／owner／pending 恢复**相同的实际切点**，起点是该调用真实的 pre-Begin 状态。
它保留全部已有结果并附加删除结果，不增加 Journal 读取。

这些是供验证使用的接口。历史、选择与结果都是 Cargo 会擦除的 `Ghost`／`Tracked` 数据，
不增加运行时日志、历史 payload 保留、自动回滚或运行时“已证明”标志。
父插件可能已经完成自身清理，但查询仍因 Child 尚未 Remove 而拒绝删除；
独立结果保留了这一重要区别。

## 论文到代码的审查路径

| 约束 | 审查入口 |
| --- | --- |
| 定义 53–54：准入和依赖安全的 Unload | `native_episode_deletion::{retained_target, control_step, transport}` 从来源闭合推出守卫保持。 |
| 引理 79 的构造性删除，限定 native 控制／publication／owner 观察 | `Window::{construct, delete}` 构造剩余历史，不接受目标轨迹作为前提。 |
| 重复 Episode 与中间区间 | `Window::unchanged_outside` 保留所选区间外的准确源转换。 |
| 出生与准入来源 | `Window::{births_closed, fresh}` 和 `Snapshot::deletion_source` 保留来源出生约束、分配新鲜性和真实提交身份。 |
| 区分公式 (55)/(56) 与合法执行 | `RecoveryCapture::with_deletion` 在同一真实切点组合已有值结果和 native 结果，不混淆两者结论。 |

代码见[原生删除](../crates/cordis-kernel/src/lifecycle_state/native/runtime/history/deletion.rs)、
[区间构造](../crates/cordis-kernel/src/lifecycle_state/native/runtime/history/deletion/trace.rs)、
[共同捕获结果](../crates/cordis-kernel/src/managed_deletion_capture.rs)。
本包不改变原论文账本或 R3 验收标准。

## 非空证据

[证明案例](../crates/cordis-kernel/src/lifecycle_state/native/runtime/history/deletion/client.rs)首先证明源路径本身合法：
27 个 native 步骤包含 owner 更早／更晚的 Episode、consumer、一个 Child、
清理失败的 stutter 和独立 provider。构造得到 11 个合法步骤，保留前后 Episode
准确的带类型 owner／publication。遗漏 consumer、遗漏出生、在 Child Remove
或 owner Unload 前关闭区间都会被拒绝。这些数字是证明案例的规模，不是性能指标。

[原生回归](../crates/cordis-kernel/tests/native_runtime.rs)通过真实调用运行两个版本，
检查 consumer 清理失败、旧回复拒绝、父插件阻塞、Child 的独立退休／移除、
owner 再次激活及独立 publication 保持。运行断言验证该案例，不是任意回调的证明。

```sh
source scripts/toolchain-env.sh
cargo test -p cordis-kernel --test native_runtime interior_episode_deletion --locked --offline
python3 scripts/check-profile-controls.py deletion
python3 scripts/record-development.py --offline
```

两个严格语义负向控制分别错误保留应删除的动作、跳过 Child 出生闭合检查。
它们必须先通过整 crate 编译，再在指定断言失败，并具有新的正向基线；
超时、资源耗尽和无关错误都不能算通过。局部证据位于 `target/r3-deletion-controls/`，
[开发记录](development-report.json)将集中检查绑定到准确源码。
完整负向回归独立记录为 `not_run`。

## 尚存边界

目标是合法的 **native 观察历史**，不是新的完整 Journal，也不是任意 Rust／Node
回调的可执行重放。目标保留原始来源票据和 payload 引用；真正重放分配／generation
计数器、共享槽内部、逆操作队列、宿主 work 和外部 I/O 仍需要进一步转换证明。
native 终态相等不代表堆值恢复；与已有恢复证书共享切点，也不自动产生整个效果载体的合法执行。

独立的 Mixed/Fresh 构造仍使用自己的整 region 条件。组合共享效果、Episode 选择、
Mixed 固定名字代码转换和异步落地，以及 Node 协议恢复仍未完成。
本包及开发证据都不宣称整篇完成、全局终止、公平调度或发布验收。

[第 5 包](r3-effect-deletion.zh-CN.md)现补充来源读取和因果闭合条件下的完整 Journal 关系转换；物理分配／generation 重放及任意回调解释仍待完成。
