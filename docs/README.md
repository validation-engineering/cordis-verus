# Documentation

Start with the [English README](../README.md) or [中文 README](../README.zh-CN.md).
The project connects useful Cordis lifecycle behavior to executable contracts,
proofs and reproducible cases. Choose a task below; detailed research is grouped
separately from the main review path.

## Use the runtime

| Goal | Guide |
| --- | --- |
| Write Rust plugins without Node | [Runtime](runtime.md) and [examples](../crates/cordis/examples) |
| Run existing Cordis JS/TS plugins | [Node compatibility](node-compatibility.md) |
| Install prebuilt runtime artifacts | [Distribution](native-distribution.md) · [中文](native-distribution.zh-CN.md) |
| Understand runtime vs Harness responsibilities | [Package boundaries](package-boundaries.md) · [中文](package-boundaries.zh-CN.md) |

## Review a guarantee

| Goal | Guide |
| --- | --- |
| Reproduce update, cleanup failure, retry and release | [Provider/consumer/Child case](cases/update-recovery.md) · [中文](cases/update-recovery.zh-CN.md) |
| Generate/reduce histories and compare test/proof detection | [Generated lifecycle evidence](cases/generated-lifecycle.md) · [中文](cases/generated-lifecycle.zh-CN.md) |
| Locate state ownership and the five review paths | [Review map](review-map.md) · [中文](review-map.zh-CN.md) |
| Follow paper → real API → contract → evidence | [Paper review](paper-review-guide.md) · [中文](paper-review-guide.zh-CN.md) |
| Understand ownership, dependencies and trust boundaries | [Architecture](architecture.md) and [semantics](semantics.md) |
| Inspect remaining whole-paper work | [Fixed inventory](paper-mapping-inventory.md) · [中文](paper-mapping-inventory.zh-CN.md) |
| Distinguish original counterexamples from revised results | [Paper audit](paper-audit.md) |

## Maintain and extend

| Goal | Guide |
| --- | --- |
| Follow the current refactoring and verification work | [Plan](verification-plan.md) · [中文](verification-plan.zh-CN.md) |
| Reproduce checks and interpret their scope | [Validation](validation.md), [evidence guide](evidence-guide.md), [recorded status](status.md) |
| Contribute a change | [Contributing](../CONTRIBUTING.md) |
| Qualify artifacts or report a vulnerability | [Releasing](releasing.md) and [security](../SECURITY.md) |
| Understand adoption goals | [Adoption plan](adoption-plan.md) · [中文](adoption-plan.zh-CN.md) |

Current work is on `main`; `codex/archive-before-refactor-2026-10-24` preserves
the pre-refactor snapshot. Reports apply only to their recorded source inputs.
Local/scoped checks do not constitute release or whole-paper acceptance.

<details>
<summary>More runtime and maintenance guides / 更多运行与维护指南</summary>

| Guide | Scope |
| --- | --- |
| [Comparison with Cordis](comparison.md) · [中文](comparison.zh-CN.md) | Lifecycle contracts, supported functionality and known differences |
| [Lifecycle cleanup case](cases/lifecycle-cleanup.md) | One fixture across two pinned upstreams and two native profiles |
| [Events](events.md) | 事件模式、owner admission 与 drain |
| [Loader](loader.md) | 配置树、原地更新、Include、热更新和持久化 |
| [Rust/JS plugins](rust-node-plugins.md) | 同图 Rust factory、JSON/流/显式对象与回调、borrowed/owned 及 action/cleanup 合同 |
| [Native Rust modules](native-rust-modules.md) | 独立 cdylib、C ABI、同进程代码换代、清理失败恢复与常驻版本预算 |
| [Typed Rust plugins](typed-rust-plugins.md) | 既有 Plugin 接入 Node、共享 typed slot、动态 publication 与子插件、清理失败合同 |
| [Official in-place HMR](official-in-place-hmr.md) | 官方模块依赖闭包、原地替换、缓存恢复和失败后继续恢复 |
| [Official configuration transactions](official-config-transactions.md) | 默认 Harness 配置 UI、Include/HMR 队列与失败恢复 |
| [Module graphs, Worker and process reloads](module-graph-reloads.md) | 观测依赖、候选更新计划与旧制品恢复 |
| [Process plugins](process-plugins.md) | 外部可执行插件、JSON-RPC、代码快照与失败恢复 |
| [Host diagnostics](host-diagnostics.md) · [中文](host-diagnostics.zh-CN.md) | Node/shared Driver 阻塞、清理动作、失败和旧 episode 身份 |
| [Diagnostics](diagnostics.md) | JSON/DOT 诊断、回收与 shutdown |
| [Upstream parity](upstream-parity.md) | Cordis／Harness 功能对应、差异及非目标 |
| [Verified programs](verified-programs.md) | ProgramDriver、MixedDriver、FreshDriver 的可运行接口及证明边界 |
| [Node compatibility architecture](node-compatibility-architecture.md) | 原版插件运行于 Rust 内核的长期架构、实施状态、兼容合同和交付门槛 |
| [Research inputs](../reference/README.md) | 锁定上游、论文来源和分发边界 |
| [Benchmarks](benchmarks.md) | 性能测量方法、源码/构建绑定、原始批次数据、显式基线与未验收预算 |
| [Toolchain archives](toolchains/README.md) | 固定 Verus 下载来源、恢复与校验 |
| [Roadmap](roadmap.md) | 后续工作顺序、交付物和验收条件 |

- [Full negative regression](full-negative-validation.md) · [中文](full-negative-validation.zh-CN.md)

</details>

<details>
<summary>Research and refinement notes / 研究与 refinement 专题</summary>

These notes retain their individual scopes and dates. An R-series title is not
a current completion claim; the fixed inventory records the remaining obligations.
Read `requires` / `ensures` before relying on a theorem. Proof counts are not
paper-theorem counts.

| Guide | Scope |
| --- | --- |
| [R01 guarded primitive replay](r01-prewrite-replay.md) · [中文](r01-prewrite-replay.zh-CN.md) | Input guards before writes, dynamic slot certificates, typed version transport and remaining whole-interval obligations |
| [Native operation contracts](native-operation-contracts.md) · [中文](native-operation-contracts.zh-CN.md) | Actual access/restore entry points, allocation identity mapping, strict scalar domains and remaining capability boundaries |
| [R3 remaining acceptance work](r3-remaining-work.md) · [中文](r3-remaining-work.zh-CN.md) | Current completion boundary, fixed remaining packages and their dependencies |
| [R3 retained target inputs](r3-target-execution.md) · [中文](r3-target-execution.zh-CN.md) | Actual source operands, fresh target execution and remaining alias/scheduling obligations |
| [R3 shared target execution](r3-shared-target-batch.md) · [中文](r3-shared-target-batch.zh-CN.md) | Allocation identity, shared target services and actual multi-call execution |
| [R3 scalar landing](r3-scalar-landing.md) · [中文](r3-scalar-landing.zh-CN.md) | Source-derived operation success, real target reads and interference evidence |
| [R3 source ordering and typed continuation](r3-source-schedule.md) · [中文](r3-source-schedule.zh-CN.md) | Actual call order, persistent typed input continuity and atomic native landing |
| [R3 effect contract boundary](r3-effect-boundary.md) · [中文](r3-effect-boundary.zh-CN.md) | A verified implementation and real root counterexample identifying the remaining effect-access obligation |
| [R3 executable control replay](r3-control-replay.md) · [中文](r3-control-replay.zh-CN.md) | Real Kernel execution, compacted registry IDs and retained-generation accounting |
| [R3 full Journal deletion](r3-effect-deletion.md) · [中文](r3-effect-deletion.zh-CN.md) | Source-read closure, full-record transport and inverse-index preservation |
| [R3 native episode deletion](r3-native-deletion.md) · [中文](r3-native-deletion.zh-CN.md) | Source-constructed interior lifecycle deletion, retained provenance and exact native endpoints |
| [R3 ordinary host ownership](r3-host-recovery.md) · [中文](r3-host-recovery.zh-CN.md) | Actual host mutation paths, retained inverse histories and controlled release |
| [R1 context interpretation](r1-semantics.md) · [中文](r1-semantics.zh-CN.md) | 完整载体组件合同、真实值和逆操作解释、明确语义修订与运行案例 |
| [R3 production recovery](r3-production-recovery.md) · [中文](r3-production-recovery.zh-CN.md) | 真实混合历史、共享别名逆序列、typed 恢复定义域与冲突来源 |
| [R3 cleanup recovery](r3-cleanup-recovery.md) · [中文](r3-cleanup-recovery.zh-CN.md) | 真实混合派发证据、失败重试、旧票据拒绝及 Begin 值的有限恢复组合 |
| [R3 interleaved recovery](r3-interleaved-recovery.md) · [中文](r3-interleaved-recovery.zh-CN.md) | 外部写入、失败重试、实际恢复日志闭合与真实 Unload 值恢复 |
| [R3 Child recovery](r3-child-recovery.md) · [中文](r3-child-recovery.zh-CN.md) | 实际出生／父 Episode、退休与 Unload 来源自动收集，以及原始 Child 义务完整性 |
| [R3 common recovery cut](r3-common-recovery-cut.md) · [中文](r3-common-recovery-cut.zh-CN.md) | 同一真实检查点上的值恢复、Child 终态及本次写入的 pending 消除 |
| [R3 observed-owner recovery](r3-observed-recovery.md) · [中文](r3-observed-recovery.zh-CN.md) | 跨所有者真实调用／派发观察、覆盖保持及从终态组推出外部恢复 |
| [R3 source continuity](r3-source-continuity.md) · [中文](r3-source-continuity.zh-CN.md) | Automatic producer intervals, pre-interval obligations and registered root/Child recovery boundaries. |
| [R3 final recovery](r3-final-recovery.md) · [中文](r3-final-recovery.zh-CN.md) | Producer-derived native Unload, foreign closure and original Child completion at one actual snapshot. |
| [R3 observation recovery](r3-observation-recovery.md) · [中文](r3-observation-recovery.zh-CN.md) | Actual intermediate publication, Episode owner and pending-registration recovery. |
| [R3 episode recovery](r3-episode-recovery.md) · [中文](r3-episode-recovery.zh-CN.md) | 任意 Episode 检查点、真实逆收据、内部 Unload 与剩余生产恢复边界 |
| [R3 script deletion](r3-script-deletion.md) · [中文](r3-script-deletion.zh-CN.md) | 真实 Mixed 来源构造合法剩余执行、严格 Xor 合同与 Child／consumer 条件 |
| [R3 closed-region deletion](r3-closed-region-deletion.md) · [中文](r3-closed-region-deletion.zh-CN.md) | Owner-created Child、实际 consumer、合法剩余执行及 Fresh 可执行名称压缩；真实七类命令、精确后继与整段同步重放完备性 |
| [Refinement](refinement.md) | 已建立的桥接、真实恢复与轨迹变换及其前提 |
| [Whole-paper milestones](paper-refinement-roadmap.md) · [中文](paper-refinement-roadmap.zh-CN.md) | R0–R5 依赖、验收与全部条目的工作映射 |
| [Typed Child domain case](cases/typed-child-domain.md) · [中文](cases/typed-child-domain.zh-CN.md) | 完整子组件输入、预留定义域与实际 Kernel 检查的对应 |
| [Paper coverage](paper-coverage.md) | 81 个编号条目的生成视图和 4 项整体连接义务 |
| [Paper ledger](paper-obligations.json) | 覆盖状态、范围和证据符号的机器可读来源 |
| [R2 production scope](r2-acceptance.md) · [中文](r2-acceptance.zh-CN.md) | Retained scoped production-refinement acceptance |
| [Automatic source association](r3-source-chain.md) · [中文](r3-source-chain.zh-CN.md) | Actual commands, Unload origins and a managed recovery cut |
| [Controlled effects](r3-controlled-effects.md) · [中文](r3-controlled-effects.zh-CN.md) | Actual effect boundary and remaining general obligations |

</details>
