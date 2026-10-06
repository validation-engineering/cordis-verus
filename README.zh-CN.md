# cordis-verus

**以 Verus 验证生命周期内核的 Rust 插件运行时。**

[English](README.md) · [文档](docs/README.md) · [示例](crates/cordis/examples) · [路线图](docs/roadmap.md) · [参与贡献](CONTRIBUTING.md)

cordis-verus 用 Rust 实现 [Cordis](https://github.com/cordiverse/cordis) 的插件生命周期与可逆效果。插件声明服务和依赖，运行时协调激活、提供者变化和清理。内核是可执行的 Rust：同一份源码接受 [Verus](https://github.com/verus-lang/verus) 验证，并由 Cargo 编译。

你可以用它构建 Rust 插件系统，通过原生 Node 适配器运行支持范围内的 Cordis JavaScript 插件，或将 Rust 与 JavaScript 插件组合到同一个生命周期图中。

**项目状态：** 实验性、尚未达到 1.0。API 仍在演进，crate 和 npm 包尚未发布。内核证明、运行时测试与应用兼容性各自的范围见[验证范围](#验证范围)。

## 功能

- **依赖感知的生命周期。** 跟踪服务提供者的实际身份，直到消费者完成清理后才释放其依赖的服务。清理失败会明确报告，并保留恢复所需的资源。
- **类型化 Rust 插件。** 组合服务、异步初始化与清理、子插件、事件和定时器，显式管理资源所有权。
- **在 Node 中运行 Cordis。** 由 Rust 决定生命周期动作，运行支持范围内的原版 JS 插件。JavaScript 对象、函数和服务值保留在 Node 中，保持原有身份。Cordis 与 DeepSeek Harness 使用不同的兼容 profile。
- **组合 Rust 与 JavaScript。** 用户编译的 Rust 插件可通过显式服务、流、对象和回调适配器加入 Node 图；typed binding 保留既有 Rust 服务槽，并可显式开启动态 publication、拥有的子插件、动态值与按 consumer 检查 availability。
- **可热替换的原生插件。** 通过版本化 C ABI 加载独立构建的 Rust `cdylib`，在同一 Node 进程内替换插件实例；reload 等待真实清理，并可恢复旧代码与配置。
- **配置与重载。** 加载 JSON 插件树，并通过同一生命周期队列协调官方 Harness 配置编辑与支持范围内的原地模块重载。需要隔离替换时，使用捕获的 Worker 或进程制品，启动失败时恢复旧版本。外部可执行插件使用独立 JSON-RPC 接口。

支持行为和有意保留的差异见[上游对照](docs/upstream-parity.md)，生命周期契约见[语义说明](docs/semantics.md)。

## 快速开始

需要 Git、Rustup、Python 3.9+、curl 和本机 Rust 编译工具链。安装脚本按照 [toolchain.lock.json](toolchain.lock.json) 选择并校验固定的 Rust/Verus 工具链，不修改 Rustup 默认工具链。安装器支持 macOS ARM64/x86_64 和 Linux x86_64。

```sh
git clone https://github.com/Stool233/cordis-verus.git
cd cordis-verus
./scripts/install-verus.sh
bash -c 'source scripts/toolchain-env.sh && cargo run --locked -p cordis --example basic'
```

仓库目前需要相应访问权限才能克隆。首次准备需要下载工具链和依赖；示例本身不需要模型凭据或外部服务。

[基础示例](crates/cordis/examples/basic.rs) 先挂载消费者，再挂载提供者，最后执行清理：

```text
consumer: hello from verified Cordis
consumer cleanup still sees: hello from verified Cordis
provider cleanup follows the consumer
```

消费者在清理期间仍能使用当前生命周期已经取得的服务，提供者随后才被释放。示例自带一个小型 executor；Rust 运行时不替应用选择异步 executor。

### Node 兼容层

安装 Rust 工具链后，使用 Node **22.22.0** 和 npm：

```sh
npm ci --ignore-scripts
npm run build:native
npm run example:node
```

[Node 示例](examples/node/basic.mjs) 从 `cordis` 导入 `Context`，加载服务并清理消费者。预加载 hook 将这个包名映射到原生适配器。自己的应用应选择对应的 profile：

```sh
# 原版 Cordis 插件
node --import @cordis-verus/compat-cordis/register app.mjs

# DeepSeek Harness Cordis 插件
node --import @cordis-verus/compat-harness/register app.mjs
```

这些命令要求已安装对应的本地 runtime 包。TypeScript 插件需先编译为 JavaScript；同一 Node environment 使用一个 profile。兼容性按具体接口和应用验证，加载规则、已知差异与平台限制见 [Node 指南](docs/node-compatibility.md)。

### DeepSeek Harness

配套项目 [cordis-harness](https://github.com/Stool233/cordis-harness) 在实际应用中验证这个运行时。它运行固定官方版本的 **Web / standard** 和 **headless** 组合，保留官方 CLI、Loader、插件、前端与 JSONL 会话存储，替换其中的 **Node Cordis 宿主**。浏览器端 Cordis 仍为官方 JavaScript 实现。

按配套项目的[构建指南](https://github.com/Stool233/cordis-harness/blob/main/docs/build.md) 准备已验收的 runtime 制品，然后在该仓库运行：

```sh
npm run official:install -- --offline
npm run official
```

没有公开依赖缓存时，安装命令去掉 `--offline`。[应用验收记录](https://github.com/Stool233/cordis-harness/blob/main/docs/official-validation-report.json) 覆盖默认插件清单、真实工具调用、跨进程会话恢复和关闭。验收中的模型请求使用本机 fixture；交互使用需自行配置模型。

## 架构

| 组件 | 职责 |
| --- | --- |
| [`cordis-kernel`](crates/cordis-kernel) | 可执行 Verus 规范、生命周期转换、动作所有权与服务发布契约 |
| [`cordis-driver`](crates/cordis-driver) | Rust 与 Node 宿主共用的生命周期控制 |
| [`cordis`](crates/cordis) | 类型化服务、插件回调、异步工作、事件、定时器与配置加载 |
| [`cordis-node`](crates/cordis-node) 和 [`packages/`](packages) | Node-API 绑定、JavaScript facade、兼容 profile 与 Rust 插件适配器 |
| [`cordis-plugin-api`](crates/cordis-plugin-api) | 独立原生插件 SDK 与版本化 C ABI |

内核管理生命周期状态，各宿主维护自己的值、回调和资源日志。源码导航与信任边界见[架构指南](docs/architecture.md)。

## 验证范围

形式化保证适用于内核中明确写出的契约及其前提。任意 Rust 或 JavaScript 回调、宿主异步执行、FFI 边界以及文件和网络 I/O，仍在已完成的证明范围之外。这些层次通过行为测试和上游对照提供独立证据。

最近一次记录的本机开发检查包括：

| 检查 | 结果 |
| --- | ---: |
| Verus 全库验证，使用 `--no-cheating --compile` | 2,292 项义务通过，0 错误 |
| Rust、文档与 Node 行为测试 | 精确数量见绑定源码的[开发记录](docs/development-report.json) |
| 解包后的 crate 构建与 npm 安装检查 | 在 macOS ARM64 / Node 22.22.0 通过 |

[开发记录](docs/development-report.json) 将结果绑定到源码和制品哈希。这些数字是验证义务和测试数量，不是已证明的论文定理数量；其他平台需要各自的执行证据。

语义参考为 [arXiv:2608.25512v1](https://arxiv.org/abs/2608.25512v1)。完整宿主到论文的 refinement 和完整发布门槛仍未完成。[论文清单](docs/paper-coverage.md) 记录已完成、部分完成和已反驳的条目，[论文审计](docs/paper-audit.md) 解释具体范围。开发检查通过不能替代发布门槛中的完整负控测试。

## 开发与验证

安装工具链和 Node 依赖后：

```sh
# 证明、格式、lint、文档、测试、示例与打包检查
python3 scripts/record-development.py

# 检查已有记录是否仍与本地源码和制品匹配
python3 scripts/record-development.py --check
```

依赖已缓存时，可给第一条命令加 `--offline`。第二条命令只检查记录是否过期，不重新执行证明。上游差分测试和完整发布门槛是独立检查，使用方式见[验证说明](docs/validation.md)和 [Node 指南](docs/node-compatibility.md)。

## 文档与贡献

| 主题 | 指南 |
| --- | --- |
| Rust 服务与资源所有权 | [Runtime](docs/runtime.md) · [Events](docs/events.md) |
| 配置与外部插件 | [Loader](docs/loader.md) · [Process plugins](docs/process-plugins.md) |
| 原版 JS 插件与原生包 | [Node compatibility](docs/node-compatibility.md) · [Distribution](docs/native-distribution.md) |
| Node 应用中的 Rust 插件 | [Factory SDK](docs/rust-node-plugins.md) · [Typed bindings](docs/typed-rust-plugins.md) · [Native module reload](docs/native-rust-modules.md) |
| 证明、进度与后续工作 | [Refinement](docs/refinement.md) · [Status](docs/status.md) · [Roadmap](docs/roadmap.md) |

更多示例与设计说明见[文档导航](docs/README.md)。专题文档目前包含英文和中文两种语言。

欢迎提交缺陷报告、小范围修复、插件兼容用例和证明贡献，中英文均可。环境与评审要求见 [CONTRIBUTING.md](CONTRIBUTING.md)，安全问题报告见 [SECURITY.md](SECURITY.md)，发布要求见[发布流程](docs/releasing.md)。

## 许可

采用 [MIT](LICENSE) 许可。上游组件保留各自许可证，来源声明见 [NOTICE](NOTICE)。cordis-verus 是独立实现，不是 Cordis 或 DeepSeek 官方发行版。参考论文和提取文本不随仓库分发，详见[研究输入](reference/README.md)。
