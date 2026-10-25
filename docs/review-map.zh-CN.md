# 所有权与审查地图

[English](review-map.md) · 简体中文 · [计划](verification-plan.zh-CN.md) · [生成式证据](cases/generated-lifecycle.zh-CN.md)

从操作拥有的状态开始审查。生产函数与其 Verus 合同保持放在一起。下表分类的是职责
和审查路径，不表示目录内每个函数都是生产调用者。

下一轮字段级所有权与依赖审计见[后续结构工作](verification-plan.zh-CN.md#后续结构工作)。
这里记录的布局调整不代表该后续审计已经完成。

## 五条保证的审查路径

| 保证／论文依据 | 状态所有者和修改入口 | 真实调用者与观察 | 证据／边界 |
| --- | --- | --- | --- |
| 未解决的依赖者保护 provider；定义 53–54、L-Unload | `Kernel` 拥有注册身份、phase 和 committed bindings；[`LifecycleState`](../crates/cordis-kernel/src/lifecycle_state/cleanup.rs) 拥有动作收据及 `execute_cleanup`；受管释放满足同一 `cleanup_step` | 共享 Driver 调用 dispatcher，Native `RecordedExecution::release` 调用受管释放；观察失败／重试中的 target 和 committed 身份 | [`cleanup/update.rs`](../crates/cordis-kernel/src/lifecycle_state/cleanup/update.rs) 的 `failed_child_keeps_chain`、调度负控和生成历史。父子关系本身不是服务依赖。 |
| 恢复失败保留逆操作及载荷；带见证效果及明确的 R1-DOMAIN 解释 | [`Inverse::restore_following`](../crates/cordis-kernel/src/reversible_value.rs) 在同一锁下拥有值／深度；[`CleanupQueue`](../crates/cordis-kernel/src/cleanup_queue.rs) 拥有占用槽位与恢复日志 | 实际 dispatch、共享值及可观察析构的真实载荷 | 同时审查严格逆操作定义域和载荷保留合同。普通已消费 `FnOnce` 失败不等于受管恢复。 |
| 旧／重复回复不能结束新尝试；实现机制 | [`ActionLedger`](../crates/cordis-kernel/src/action_ledger.rs)、[`CleanupJournal`](../crates/cordis-kernel/src/cleanup_journal.rs)、队列完成及重试入口 | 实际动作／恢复票据、新 attempt、拒绝前后状态、新 Episode 中的旧回复 | 既有收据测试和生成历史。不假定任意异步 callback 最终回复。 |
| Child 逆操作退休其实际 Child；定义 52、54 | [`shared_child`](../crates/cordis-kernel/src/lifecycle_state/registration/shared_child.rs) 原子创建请求／逆操作，Native 注册关联实际身份 | 原始返回句柄、真实请求 dispatch、父 Episode 及显式服务绑定 | 句柄／注册关联检查、拆分句柄变异及其合同拒绝。所有权与依赖继续分开。 |
| 原因移除后，受支持的更新可恢复；朝定理 68–70 推进的受限证据 | [`NativeRuntime`](../crates/cordis-kernel/src/lifecycle_state/native/runtime.rs) 拥有注册、publication 和实际 recorded execution；owner 保留清理状态直到合法释放 | 真实 root、Child、干扰、修复原因、重试、再次更新和完整关闭 | 原始固定案例与有效／不利生成场景。不宣称一般恢复等式、合流或全局活性。 |

一般性缺口继续以[论文清单](paper-mapping-inventory.zh-CN.md)为准。测试模型检查观察，
不向生产路径提供历史，不替代 refinement 证明。

## 源码组织及依赖方向

| 区域 | 所有权／用途 | 审查分类 |
| --- | --- | --- |
| [`lifecycle_state/`](../crates/cordis-kernel/src/lifecycle_state/)、[`lifecycle_actions/`](../crates/cordis-kernel/src/lifecycle_actions/)、动作／清理 ledger | 共享生命周期权限和旧 provider 保护 | 生产状态、附着合同及轨迹组合 |
| [`reversible_value/`](../crates/cordis-kernel/src/reversible_value/)、[`cleanup_queue/`](../crates/cordis-kernel/src/cleanup_queue/)、[`cleanup_groups/`](../crates/cordis-kernel/src/cleanup_groups/) | 受管操作、保留逆操作、实际执行来源和历史 | 生产 primitive 及解释／迁移证明，一般性边界保持明确 |
| [`lifecycle_state/native/`](../crates/cordis-kernel/src/lifecycle_state/native/)、[`node_runtime/`](../crates/cordis-kernel/src/node_runtime/) | 各自建立共享协议前提的 Native／Node 状态所有者 | 生产连接；Node 记录 publication／句柄／scope，不证明 JS 对象内部 |
| [`refinement.rs`](../crates/cordis-kernel/src/refinement.rs)、[`dependent_grammar.rs`](../crates/cordis-kernel/src/dependent_grammar.rs)、grammar／history／recovery 及 [`mixed_driver/`](../crates/cordis-kernel/src/mixed_driver/) | 论文语义、条件定理、参考执行器及实际历史连接 | 规格与证明支持，包含可执行研究 driver；被擦除或没有宿主调用者不代表冗余 |
| [`paper_counterexamples.rs`](../crates/cordis-kernel/src/paper_counterexamples.rs)、恢复／mixed 示例、定向负控和冻结报告 | 反例、修订解释、准入示例和证伪 | 保留的研究证据，导航单列，活跃验证目标不变 |
| [`cordis-driver/src/shared/`](../crates/cordis-driver/src/shared/)、[`node.rs`](../crates/cordis-driver/src/node.rs) | 共享调度策略、命令解析和宿主适配 | 普通 Rust 连接，不自动成为已证明的调度器 |
| [`runtime/setup.rs`](../crates/cordis/src/runtime/setup.rs)、[`services.rs`](../crates/cordis/src/runtime/services.rs)、[`cleanup.rs`](../crates/cordis/src/runtime/cleanup.rs)、[`poll.rs`](../crates/cordis/src/runtime/poll.rs) | Episode API、服务句柄、清理收据和协作轮询 | 普通宿主；状态结构和生命周期入口留在 [`runtime.rs`](../crates/cordis/src/runtime.rs)，模块拆分保持锁／析构顺序 |
| 可选 Node facade／N-API／进程／cdylib | 语言语义、callback、传输和外部 I/O | 通过测试检查的宿主边界；纯 Rust 不依赖 Node，Harness 保持独立应用 |

依赖方向仍为宿主 → 共享 Driver → 验证状态所有者 → 共享生命周期／资源协议。
数学支持为附着合同提供定理，不引入运行时 Node 依赖或第二份实现。
[架构文档](architecture.md)说明工具链、库、编译器、验证器和 FFI 信任前提。

## 积累内容的处置

| 重构前内容 | 处理和理由 | 检查 |
| --- | --- | --- |
| 253 个通过 `#[path]` 连接的平铺文件 | 按既有逻辑模块路径移动：先 41 个生命周期文件，再 212 个剩余文件；移除全部 255 个路径属性，其中两个本来就多余。公开模块身份不变。 | 除路径属性／引用外，函数体与合同精确相等；编译、完整 Verus、打包及规范负控锚点检查 |
| 5,195 行普通 `runtime.rs` | 先拆清理，再拆 setup、服务句柄方法和轮询；当前主文件 3,139 行。公开类型／导出不变，只调整必要的内部方法可见性。 | 方法体比对、Cargo／lint、原宿主回归和抽取包构建 |
| 同一严格负控执行器的 15 个包装入口 | 合并为 `check-profile-controls.py PROFILE` | 保留规范选择、新正向基线、完整变异编译及精确合同拒绝；独有 full／R2 检查器保留 |
| 重复入口清单 | 按任务组织文档首页、当前审查地图及单一 campaign CLI | 链接、源码绑定和中英入口 |
| 一般模型、条件恢复分支、独有失败与冻结报告 | 研究导航中保留，继续使用原有验证目标 | 移文件不关闭义务，历史通过保持原始源码绑定 |

固定归档为 `codex/archive-before-refactor-2026-10-24`（`60bdd89`）；第二批整理前的
布局也保存在 `c47d111`。不改写历史或上游锁。本轮**没有批准删除独有语义成果**。
进一步删除须比较前提／结果、调用方、证明依赖与独有反例；存在归档本身不是删除
当前对外保证所依赖定理的理由。
