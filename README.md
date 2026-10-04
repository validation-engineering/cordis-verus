# cordis-verus

[English](README.en.md) · [文档导航](docs/README.md) · [项目状态](docs/status.md) · [贡献指南](CONTRIBUTING.md)

用带 [Verus](https://github.com/verus-lang/verus) 契约与证明的可执行 Rust 实现 Cordis 的生命周期与可逆效果。内核的同一份源码接受 Verus 验证和 Cargo 编译；上层 Rust runtime 提供 typed services、异步插件、事件、定时器及配置加载。

这是独立于原 TLA+ 研究的新项目，以 [arXiv:2608.25512v1](https://arxiv.org/abs/2608.25512v1) 为语义来源，以 Cordis 和 DeepSeek Harness 的锁定官方快照为功能参考。项目提供 Rust 对应接口，不运行 TypeScript 插件，也不实现 Harness 的模型 API、权限系统或 UI。

**这是私有研究开发项目（实验性 0.1.0），尚未发布到 crates.io，完整发布质量门槛尚未通过。** 公共 API 和证明边界仍在演进；实现优先对齐 Cordis 行为和论文语义。

## 当前进度

| 检查对象 | 冻结快照结果 |
| --- | --- |
| Verus 全库正向验证 | 使用 `--no-cheating --compile`；结果与源码哈希见[开发记录](docs/development-report.json)的 `proof` 字段 |
| Rust 行为测试 | 同一记录的 `tests` 字段；开发检查另包含独立 crate 打包测试 |
| 论文 81 个编号条目 | **42 formalized · 17 proved · 18 partial · 4 refuted** |
| 整体连接义务 | **4 项 open** |
| 负控与发布证据 | **114 项负控待完成全量校准**；完整 `quality.sh` 尚未通过 |

这些数字对应已冻结源码，不等于整篇论文已证明。`formalized` 表示定义已编码，不表示其所有模型或宿主实现都已满足定义。实验性 scoped-negative checker 只生成所选证明的证据，**不能代替规范全库负控，也不是 v3 发布证据**。准确记录与重现方法见[项目状态](docs/status.md)及[验证说明](docs/validation.md)。

## 能做什么

- 生命周期内核：四态转换、真实 provider identity、target／committed bindings、retire／remove 分离和恢复次序守卫。
- 已验证闭合程序：实际服务值、Provision、跨 provider 操作、动态 Child、真实 LIFO inverse journal、在途准入和目标变化后的 Divert。
- Rust 宿主：同步／异步 setup、typed services、realm、动态子插件、取消和清理、事件及 owner 定时器。
- 配置与维护：JSON 配置树、Include、热更新、显式配置保存、状态诊断及 shutdown。

宿主功能由行为与集成测试支撑；任意 Rust callback、Future、锁和文件 I/O 尚未获得完整形式化 refinement。功能对应与差异见[上游对照](docs/upstream-parity.md)，使用限制见[语义边界](docs/semantics.md)。

## 快速开始

需要 Git、Rustup、Python 3 和 curl。安装脚本下载并校验锁定的 Verus／Rust 工具链，支持 macOS ARM/Intel 与 Linux x86_64，不修改 Rustup 默认工具链。首次运行需要网络和 Cargo 依赖；后续可使用本地缓存。

```bash
git clone https://github.com/Stool233/cordis-verus.git
cd cordis-verus
./scripts/install-verus.sh
source scripts/toolchain-env.sh
cargo test --workspace --locked
cargo run --locked -p cordis --example basic
```

仓库当前按私有项目管理，克隆需要相应 GitHub 访问权限。示例使用 std executor，无需模型密钥或外部服务。

| 想了解 | 从这里开始 |
| --- | --- |
| consumer 与 provider 的清理顺序 | [basic.rs](crates/cordis/examples/basic.rs) |
| 异步 stage、Child 与 LIFO | [async_lifecycle.rs](crates/cordis/examples/async_lifecycle.rs) |
| 配置加载与保存 | [config_reload.rs](crates/cordis/examples/config_reload.rs)、[config_persistence.rs](crates/cordis/examples/config_persistence.rs) |
| 已验证程序的具体 API | [固定程序指南](docs/verified-programs.md) |

## 验证与论文范围

```bash
# 日常开发检查：格式、lint、文档、全库正向证明、测试、示例及打包
./scripts/check-development.sh --offline

# 仅内核正向验证
./scripts/verify.sh --num-threads 2 --triggers-mode silent

# 完整质量流程：格式、lint、文档、证明、测试、示例、全库负控及打包
./scripts/quality.sh --offline

# 清单一致性；--require-complete 另检查整篇完成门槛，当前应失败
python3 scripts/check-paper-coverage.py
```

锁定工具与输入见 [toolchain.lock.json](toolchain.lock.json)、[Cargo.lock](Cargo.lock) 和 [upstream.lock.json](upstream.lock.json)。负控须先完整编译，再产生真实契约失败；超时、资源耗尽和编译失败不算成功。默认 CI 使用开发检查，**不包含全量负控**；规范全库负控和完整发布质量保留为独立流程。CI 配置的存在不代表远程矩阵已通过。

已完成的受限证明包括实际九规则轨迹、provider 次序、观察恢复、带守卫的交换与后缀运输，以及允许 foreign Table／Child 混合日志和动态 registry 的 episode 删除。其条件和局限保留在合同中，不能提升为任意调度汇合或完整宿主证明。详见[架构](docs/architecture.md)、[refinement](docs/refinement.md)和[逐项覆盖清单](docs/paper-coverage.md)。

论文 Lemma 62、75、77 和 Theorem 71(2) 的无条件闭合断言有 Unit 组件的原文反例。Child 的交换、删除与字面输入见证仍有原 Component 表示缺口，**不构成原文 78／79／80 的无条件反驳**。判断依据见[论文审计](docs/paper-audit.md)。

当前使用 Verus 官方滚动发布 `0.2026.10.04.1687598`，按完整提交和各平台归档 SHA-256 固定。上游锁同时记录匹配的 Verus 源码，供核对语言能力和证明实现；正式发布、滚动发布和更靠前的主分支提交分别对待。

## 参与与许可

实现和证明的后续工作见[路线图](docs/roadmap.md)。提交变更请遵循[贡献指南](CONTRIBUTING.md)，安全问题按[安全报告流程](SECURITY.md)处理，发布要求见[发布流程](docs/releasing.md)。

本项目 Rust 代码采用 [MIT](LICENSE) 许可。上游代码保留各自许可；论文及提取文本不属于项目 MIT 许可，未随源码分发，详见[研究输入说明](reference/README.md)。
