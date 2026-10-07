# cordis-verus 与 Cordis 的比较

[English](comparison.md) | 简体中文

cordis-verus 将形式化方法落实到可执行的生命周期代码，同时对齐 Cordis 功能。
同一份 Rust 内核既由 Verus 验证，也编译进入运行时。原版插件接口、上游测试和官方
Harness 工作流，为功能对齐提供了具体的检验目标。

下文重点介绍可供审查的生命周期合同，以及实际可用的插件能力。
已支持的行为和已知差异都附有相应证据。

本比较针对 [upstream.lock.json](../upstream.lock.json) 固定的版本：
Cordis `f8ea3cd50f1a5724e8e715995bcde131c9c12b2c`（`4.0.0-rc.10`），以及
DeepSeek Harness `da00f7f5358f2949383b35c14f548bc20187d80c`（内置 Cordis
`4.0.4`）。这里的结论不涵盖所有上游版本或所有 npm 插件。

## 从论文约束到可执行代码

[论文审查指南](paper-review-guide.zh-CN.md) 沿着五项论文条款，追踪其前提、Verus
合同、可执行调用路径和具名回归测试。借助这些路径，可以检查某个生命周期决策受哪项
约束控制，以及执行何时交由普通 Rust 或 JavaScript 宿主负责。内核中已经明确陈述的
合同获得了证明；任意插件回调和外部 I/O 仍在该证明边界之外。
[论文覆盖台账](paper-coverage.md) 记录了剩余的 refinement 工作。

对维护者而言，这些路径为审查 provider 身份、清理或恢复行为的变更提供了具体起点。
证明检查、宿主回归测试和应用验收分别检查变更的不同部分。让这些关联随实现保持更新，
也是维护工作的一部分。

## 功能对齐

| 方面 | 上游 Cordis / Harness | cordis-verus |
| --- | --- | --- |
| 插件语言 | 原有 JavaScript/TypeScript 生态 | 类型化 Rust 插件，以及通过独立 Cordis/Harness profile 支持的原版 JS 插件；TS 需先编译再加载 |
| 生命周期实现 | JavaScript/TypeScript 运行时 | 由 Verus 验证的可执行 Rust 内核；普通 Rust 和 JS 宿主负责值、回调和调度 |
| 清理依赖 | 行为取决于所选上游实现及插件之间的交互 | 消费者清理期间保留已提交的 provider 身份；内核合同要求 provider 等待这些消费者完成后再释放 |
| 清理失败 | 固定版本的 Cordis 测试要求逆操作抛错后，释放操作仍成功完成 | 释放操作返回拒绝，保留失败的逆操作和 provider 资源，并提供显式重试 |
| 配置与 HMR | 官方配置和模块 API | 支持的官方配置事务与 JS 原地 HMR；Worker/进程替换和独立 Rust `cdylib` 实例替换具有明确的恢复合同 |
| 原生代码更新 | 本比较中的上游没有对应的 Rust 插件 ABI | 重新构建兼容的动态库，再在 Node 宿主中替换其实例；迁移逻辑状态需要插件显式采用 checkpoint 合同 |
| 安装 | JS 依赖和受支持的上游工具链 | Rust 应用通过 Cargo 使用固定的 Rust/Verus 构建输入；可选的 Node 兼容层增加平台对应的原生扩展和产物校验 |
| 保证与证据 | 上游行为及测试作为兼容性证据 | 分别报告内核合同、反例、宿主回归测试和应用验收 |

对于 Rust 应用，Node 和 npm 都是可选的；运行与开发所需的依赖见
[架构概览](../README.zh-CN.md#架构)。

详细的 Rust API 对照见[功能对齐表](upstream-parity.md)，profile 限制见
[Node 兼容指南](node-compatibility.md)。替换 Rust `cdylib` 不会改写正在执行的机器码，
也不会使任意旧函数指针变得安全。代码仍按[原生模块指南](native-rust-modules.md)中的
模块生命周期与预算规则保留在内存中。

## 一个具体的生命周期问题

一个服务持有文件流。其消费者在清理期间等待，然后通过该服务写入最后一条记录。
如果在消费者写入之前关闭服务，最后一条记录就会丢失。

[生命周期案例](cases/lifecycle-cleanup.md) 在四个真实入口中使用同一份测试场景，
记录了两个固定版本上游及对应 native profile 的行为、准确的源码哈希和原始轨迹。
native 合同要求保留已提交的 provider，直到消费者完成清理。
在固定版本中复现缺陷，与获得上游维护者的确认，是两件不同的事；两者也都不构成
对上游当前最新版本的判断。

配套的清理失败案例说明的是另一点：保留失败的清理操作并显式报告错误，是一项规范
选择。依赖上游吞掉错误行为的应用，需要处理释放被拒绝和后续重试。
我们不将这种 JavaScript 行为称为 Rust 意义上的未定义行为。

## 如实记录兼容性差异

[2026-10-08 比较](evidence/2026-10-08-a03/README.md)包含未经修改的上游核心测试集、
严格的 profile 轨迹、较小的 API 测试场景和真实 Harness 服务场景。当前完整核心运行中，
**上游测试通过 87/87，native 测试通过 85/87**。其余三组比较通过；选定场景通过，
并不能消除核心套件中的两项失败。

[2026-10-06 基线](evidence/README.md)仍保留上游 87/87、native 83/87 及原始四项失败。
两项非故意差异现在通过：受限协调避免了以消费者旧配置额外激活一次，清理期资源注册
错误也包含了上游要求的文本。协调覆盖 Cordis profile 中满足
[约定条件](node-compatibility.md#同栈-providerconsumer-更新)的同栈直接 provider/committed-consumer
更新，其他情况继续使用 FIFO。清理期间仍禁止注册资源，保留结构化失败 code 与旧 episode 检查。

剩余的 `inertia lock 2` 场景，以及逆操作抛错后的释放行为，与我们采用的已提交
publication 和清理失败合同存在差异。两项断言均保留，完整比较仍以失败退出。
预期内的失败，仍然是不符合上游行为的失败。这些修复没有证明 JS 协调器，也不代表
兼容所有应用。

配套的 [Harness 验收](https://github.com/validation-engineering/cordis-harness/blob/main/docs/official-validation-report.json)
增加了官方 Web/standard 和 headless 执行路径，覆盖原版插件、UI、工具和会话存储。
使用脚本化的本地模型 provider，使验收可以复现。这些验收不证明所有模型、插件或外部
服务上的等价性，也没有替换浏览器端的 Cordis。

## 何时选择本项目

当你需要 Rust 原生插件组合、显式清理恢复、JS/Rust 混合生命周期，或希望审查一个将
形式化方法与运行软件关联起来的实例时，可以评估 cordis-verus。如果你的要求是精确
保持所有现有 Cordis 插件的行为，则需要先评估已知差异和原生集成工作。
可复现的入口和剩余发布工作见[证据指南](evidence-guide.md)。

## 其他测量

性能优化仍在继续。历史[应用测量](https://github.com/validation-engineering/cordis-harness/blob/main/docs/performance.md)
和[运行时基准](benchmarks.md)保留了方法、样本与适用范围，供工程参考。
