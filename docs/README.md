# 文档导航 / Documentation

从[项目 README](../README.md)或[英文入口](../README.en.md)开始。本文按用途导航；完整研究推导保留在专题文档中。

## 运行与使用

| 文档 | 内容 |
| --- | --- |
| [Runtime](runtime.md) | typed service、同步／异步插件、stage 与清理 |
| [Events](events.md) | 事件模式、owner admission 与 drain |
| [Loader](loader.md) | 配置树、Include、热更新和持久化 |
| [Diagnostics](diagnostics.md) | JSON/DOT 诊断、回收与 shutdown |
| [Upstream parity](upstream-parity.md) | Cordis／Harness 功能对应、差异及非目标 |
| [Verified programs](verified-programs.md) | ProgramDriver、MixedDriver、FreshDriver 的可运行接口及证明边界 |
| [Examples](../crates/cordis/examples) | 可直接用 Cargo 运行的示例 |

## 架构与证明

| 文档 | 内容 |
| --- | --- |
| [Architecture](architecture.md) | 两个 crate、证明层次、源码导航与信任边界 |
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
| [Roadmap](roadmap.md) | 后续工作顺序、交付物和验收条件 |
| [Contributing](../CONTRIBUTING.md) | 开发环境、提交约定与变更检查 |
| [Releasing](releasing.md) | 完整质量门槛、打包与发布流程 |
| [Security](../SECURITY.md) | 安全问题报告 |

日常开发使用 `./scripts/check-development.sh --offline`；默认 CI 不含全量负控。
完整 `quality.sh` 的发布门槛仍独立保留，当前尚未通过。scoped-negative 是实验工具，结果不能冒充全库负控或 v3 发布证据。新增或调整论文范围后，编辑 ledger 并运行 `python3 scripts/check-paper-coverage.py --write`；不要直接手改生成表来提升状态。
