# 运行时包与 Harness 应用的边界

[English](package-boundaries.md)

`cordis-verus` 对应 Cordis；配套 Harness 应用对应 DeepSeek Harness，在我们的运行时上组合官方应用和插件。两者分别维护上游目标与验收记录。

| 包 | 职责 | 所属项目 |
| --- | --- | --- |
| `@validation-engineering/cordis` | Rust 支撑的共享 Node 运行时与普通 Cordis 接口 | cordis-verus |
| `@validation-engineering/cordis-compat-deepseek` | 兼容 `@deepseek-ai/cordis` 的生命周期接口与导入路由 | cordis-verus |
| `@validation-engineering/cordis-loader` | JSON Loader、域事务、Worker/进程隔离及 Rust 模块加载 | cordis-verus |
| `@validation-engineering/harness-verus` | 官方 CLI/Web/headless 组合，以及对应版本的 Loader、ConfigEditor、HMR 集成 | 配套 Harness 应用 |

DeepSeek 兼容包是可选的运行时接口，不包含 AgentLoop、模型、工具、会话存储或 Web UI。其类型和策略回归与共享运行时一起维护。内部策略标识仍为 `harness`，包名调整不改变原生协议和生命周期合同。

官方应用类的方法接入、Include 写入屏障、模块缓存替换与恢复，以及相应的官方工作流和类型测试，由应用仓库维护。它们调用核心的事务准入与清理 API，核心不反向依赖应用。

## 从首次 npm 发布迁移

将 `@validation-engineering/cordis-harness` 导入改为 `@validation-engineering/cordis-compat-deepseek`，包括 `/register` 预加载入口。原有 `cordis-harness@0.1.0` 仍是兼容库，不将该名称重新解释成完整应用。

从 `cordis-loader@0.2.0` 开始移除应用专用的 `/harness` 入口。`LoaderTransactions`、`installOfficialTransactions` 和 `officialTransaction` 改由应用的 `/official-loader-api` 导出，实现、类型和验收测试也一并归应用维护。需搭配明确提供该出口的应用版本，旧应用快照不能自动消费新 Loader。

本文描述源码布局和迁移方式，不代表所有列出的版本均已发布；实际可用版本以发布说明为准。此次整理不覆盖历史发布包或历史证据。

## 验证边界

Verus 证明可执行内核的指定合同。JS 兼容策略、应用类适配、Node 模块缓存、应用回调与外部 I/O 依靠行为测试，不具有整体 Verus 证明。将包放在核心仓库不扩大内核的证明范围。
