# 文档导航 / Documentation

从[英文 README](../README.md)或[中文 README](../README.zh-CN.md)开始。本文按用途导航；完整研究推导保留在专题文档中。

## Evidence and independent review

| Guide | What you can check |
| --- | --- |
| [Evidence guide](evidence-guide.md) | Claims, commands, evidence types and remaining publication work |
| [Comparison with Cordis](comparison.md) | Capabilities, deliberate differences and performance tradeoffs |
| [Lifecycle cleanup case](cases/lifecycle-cleanup.md) | One fixture across two pinned upstreams and two native profiles |
| [Paper review guide](paper-review-guide.md) | Five exact paper → contract → executable path → regression chains |

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
| [Native distribution](native-distribution.md) | 原生产物 manifest、平台选择、校验和离线合包 |
| [Process plugins](process-plugins.md) | 外部可执行插件、JSON-RPC、代码快照与失败恢复 |
| [Diagnostics](diagnostics.md) | JSON/DOT 诊断、回收与 shutdown |
| [Upstream parity](upstream-parity.md) | Cordis／Harness 功能对应、差异及非目标 |
| [Verified programs](verified-programs.md) | ProgramDriver、MixedDriver、FreshDriver 的可运行接口及证明边界 |
| [Examples](../crates/cordis/examples) | 可直接用 Cargo 运行的示例 |

## 架构与证明

| 文档 | 内容 |
| --- | --- |
| [Architecture](architecture.md) | Rust/Node 分层、证明层次、源码导航与信任边界 |
| [Node compatibility architecture](node-compatibility-architecture.md) | 原版插件运行于 Rust 内核的长期架构、实施状态、兼容合同和交付门槛 |
| [Semantics](semantics.md) | 实现规则、依赖与所有权、retire/remove 等关键区别 |
| [Refinement](refinement.md) | 已建立的桥接、真实恢复与轨迹变换及其前提 |
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
| [Roadmap](roadmap.md) | 后续工作顺序、交付物和验收条件 |
| [Contributing](../CONTRIBUTING.md) | 开发环境、提交约定与变更检查 |
| [Releasing](releasing.md) | 完整质量门槛、打包与发布流程 |
| [Security](../SECURITY.md) | 安全问题报告 |

日常开发使用 `./scripts/check-development.sh --offline`；默认 CI 不含全量负控。
完整 `quality.sh` 的发布门槛仍独立保留，当前尚未通过。scoped-negative 是实验工具，结果不能冒充全库负控或 v3 发布证据。新增或调整论文范围后，编辑 ledger 并运行 `python3 scripts/check-paper-coverage.py --write`；不要直接手改生成表来提升状态。
