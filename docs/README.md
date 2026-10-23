# 文档导航 / Documentation

[Runtime packages and application boundaries](package-boundaries.md) · [中文](package-boundaries.zh-CN.md)

从[英文 README](../README.md)或[中文 README](../README.zh-CN.md)开始。本文按用途导航；完整研究推导保留在专题文档中。

## Evidence and independent review

| Guide | What you can check |
| --- | --- |
| [Paper-to-code remaining obligations](paper-mapping-inventory.md) · [中文](paper-mapping-inventory.zh-CN.md) | 81 paper items, 4 integration obligations, 31 fixed closure units, premise sources and dependencies; no completion percentage |
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
| [Evidence guide](evidence-guide.md) | Formal-methods review, functional alignment and reproducible cases |
| [Comparison with Cordis](comparison.md) · [中文](comparison.zh-CN.md) | Lifecycle contracts, supported functionality and known differences |
| [Provider/consumer/Child update](cases/update-recovery.md) · [中文](cases/update-recovery.zh-CN.md) | Real inverse failure, explicit retry, safe release and source-bound reproduction |
| [Lifecycle cleanup case](cases/lifecycle-cleanup.md) | One fixture across two pinned upstreams and two native profiles |
| [Paper review guide](paper-review-guide.md) · [中文](paper-review-guide.zh-CN.md) | Five exact paper → contract → executable path → regression chains |

## 运行与使用

| 文档 | 内容 |
| --- | --- |
| [Runtime](runtime.md) | typed service、同步／异步插件、stage 与清理 |
| [Events](events.md) | 事件模式、owner admission 与 drain |
| [Loader](loader.md) | 配置树、原地更新、Include、热更新和持久化 |
| [Rust/JS plugins](rust-node-plugins.md) | 同图 Rust factory、JSON/流/显式对象与回调、borrowed/owned 及 action/cleanup 合同 |
| [Native Rust modules](native-rust-modules.md) | 独立 cdylib、C ABI、同进程代码换代、清理失败恢复与常驻版本预算 |
| [Typed Rust plugins](typed-rust-plugins.md) | 既有 Plugin 接入 Node、共享 typed slot、动态 publication 与子插件、清理失败合同 |
| [Official in-place HMR](official-in-place-hmr.md) | 官方模块依赖闭包、原地替换、缓存恢复和失败后继续恢复 |
| [Official configuration transactions](official-config-transactions.md) | 默认 Harness 配置 UI、Include/HMR 队列与失败恢复 |
| [Module graphs, Worker and process reloads](module-graph-reloads.md) | 观测依赖、候选更新计划与旧制品恢复 |
| [Node compatibility](node-compatibility.md) | 原版 JS/TS 插件的实验性原生运行路径、构建、加载、差分测试与范围 |
| [Native distribution](native-distribution.md) · [中文](native-distribution.zh-CN.md) | GitHub Release 免编译安装、平台选择、校验和离线合包 |
| [Process plugins](process-plugins.md) | 外部可执行插件、JSON-RPC、代码快照与失败恢复 |
| [Host diagnostics](host-diagnostics.md) · [中文](host-diagnostics.zh-CN.md) | Node/shared Driver 阻塞、清理动作、失败和旧 episode 身份 |
| [Diagnostics](diagnostics.md) | JSON/DOT 诊断、回收与 shutdown |
| [Upstream parity](upstream-parity.md) | Cordis／Harness 功能对应、差异及非目标 |
| [Verified programs](verified-programs.md) | ProgramDriver、MixedDriver、FreshDriver 的可运行接口及证明边界 |
| [Examples](../crates/cordis/examples) | 可直接用 Cargo 运行的示例 |

## 架构与证明

| 文档 | 内容 |
| --- | --- |
| [Architecture](architecture.md) | 纯 Rust 路径、可选 Node 宿主、构建／运行依赖、证明层次与信任边界 |
| [Node compatibility architecture](node-compatibility-architecture.md) | 原版插件运行于 Rust 内核的长期架构、实施状态、兼容合同和交付门槛 |
| [Semantics](semantics.md) | 实现规则、依赖与所有权、retire/remove 等关键区别 |
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
| [Paper audit](paper-audit.md) | 原文反例、编码模型障碍和修订结论的区别 |
| [Research inputs](../reference/README.md) | 锁定上游、论文来源和分发边界 |

阅读证明时先看公开 `requires`／`ensures`，再跟随实现和调用。`formalized`、`proved`、`partial`、`refuted` 是论文条目的状态；Verus verified 数不是论文定理数，也不替代这些状态。

## 项目维护

| 文档 | 内容 |
| --- | --- |
| [Status](status.md) | 冻结快照结果、尚未通过的检查和当前工作 |
| [Validation](validation.md) | 重现验证、规范负控、实验性 scoped 检查和证据判定 |
| [Benchmarks](benchmarks.md) | 性能测量方法、源码/构建绑定、原始批次数据、显式基线与未验收预算 |
| [Adoption plan](adoption-plan.md) · [中文](adoption-plan.zh-CN.md) | 用户目标、形式化主线、阶段验收与独立接入 |
| [Toolchain archives](toolchains/README.md) | 固定 Verus 下载来源、恢复与校验 |
| [Roadmap](roadmap.md) | 后续工作顺序、交付物和验收条件 |
| [Contributing](../CONTRIBUTING.md) | 开发环境、提交约定与变更检查 |
| [Releasing](releasing.md) | 完整质量门槛、打包与发布流程 |
| [Security](../SECURITY.md) | 安全问题报告 |

日常开发使用 `./scripts/check-development.sh --offline`；默认 CI 不含全量负控。
`quality.sh` 复用完整正向证明、运行与软件包检查，发布还要求所选平台的实际产物安装。全量负控独立运行，在 `verification/v4` 发布记录中明确标为 `not_run`。scoped-negative 仍是实验工具，不能冒充全库负控或发布证据。新增或调整论文范围后，编辑 ledger 并运行 `python3 scripts/check-paper-coverage.py --write`；不要直接手改生成表来提升状态。

Independent full negative regression: [English](full-negative-validation.md) · [简体中文](full-negative-validation.zh-CN.md).

- [Automatic production source association](r3-source-chain.md) ([中文](r3-source-chain.zh-CN.md)): bounded real commands, complete Unload origins and one managed recovery cut.
- [Real managed target execution](r3-target-execution.md) ([中文](r3-target-execution.zh-CN.md)): preserved invocation inputs, guaranteed interpreter admission and target-local cleanup.

- [Controlled effects in actual execution](r3-controlled-effects.md) · [中文](r3-controlled-effects.zh-CN.md)
