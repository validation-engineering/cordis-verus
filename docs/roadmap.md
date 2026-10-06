# 路线图与验收条件

当前正向验证和测试结果以绑定源码哈希的[开发记录](development-report.json)为准。论文清单为 42 formalized、17 proved、18 partial、4 refuted，另有 4 项整体义务 open。完整发布质量尚未通过；这些数字不是后续改动的自动证据，最新状态见[status](status.md)。

工作按下面的交付物推进，不承诺日期。每项范围变化都应同步合同、非空示例、负控和 ledger；原文反例保留原状态，修订定理另列前提。

## 1. 完成可复现的验证与仓库维护

| 工作 | 交付物 | 验收条件 |
| --- | --- | --- |
| 固定工具链制品来源 | 保留 Verus 锁定版本与原始校验值，建立长期可用的下载来源 | 原 rolling 资产已失效；恢复同字节制品并通过新机器安装与 CI，不绕过 SHA-256 校验 |
| 校准 114 项负控 | 每项精确 mutation、selector、唯一锚点、工具链和源码绑定 | 正向同 selector 先通过；mutant 完整编译；出现所指函数的真实契约失败；超时／rlimit／编译失败不计通过 |
| 完整发布质量 | 规范 `quality.sh`、测试、示例与独立 `.crate` 解包构建记录 | 在同一冻结源码上全部通过，保留完整日志及哈希；不得拼接不同快照冒充一次成功 |
| 远程 CI | 实际 Linux／macOS 开发检查矩阵及失败排查 | 默认检查包含全库正向证明、测试、示例和打包，不包含全量负控；以实际 job 结果为准，开发通过不替代发布门槛 |
| API 与维护入口 | 双语 README、文档导航、贡献／安全／发布流程 | 所有本地链接有效，最小示例可运行，版本与实际公开 API 一致 |

日常检查入口为 `./scripts/check-development.sh --offline`；严格 `quality.sh` 与规范全库负控仍独立保留，不因建立私有开发仓库而放宽验收。

`check-negative-scoped.py` 目前仅为实验工具。校准完成也只说明所选函数的负控有效，不能自动替代规范全库负控，更不能生成或冒充 v3 发布证据。采用新的发布判定方式必须是独立、可审查的流程变更。

## 2. 补齐原文 Component 与严格 Child 的表示桥

从 [paper_instantiation](../crates/cordis-kernel/src/paper_instantiation.rs) 的真实 typed primitive 出发，连接完整 Component 输入 witness、实际 O-Insert／捕获 O-Retire 和观察关系。首先构造同一 typed Child 在等表观察输入上的 Some／None 边界，把已有纯 grammar 见证升级为带真实 Component 参数的精确结论。

验收须同时给出实际 editor、所有输入的依赖值解释、完整 child Component witness 和实际执行结果。它仍不能省略 spawning parent 的原全域 witness，也不能据此无条件反驳原文 57／73／80。随后明确原 total-context 解释与 strict partial-domain 解释的桥或必要修订，更新 52／55／56／57／65／66 的逐项范围。

## 3. 从受限恢复扩展到完整生命周期

| 当前已闭合 | 下一步 | 验收条件 |
| --- | --- | --- |
| foreign Table／Child、旧／新混合 journal、动态 Insert/Remove；owner 为 Table | owner 自己创建 Child 后的删除 | 处理两侧 registry 域不同、birth identity、依赖和 retention；构造目标执行，不预设目标合法 |
| 私有 owner provision 与 foreign 声明分离 | owner provision 有真实 consumer | 从原 committed／relied guard 导出允许交错与恢复域，不把完整恢复成功当作前提 |
| 一次 owner episode，最后实际 Unload | 多 episode／窗口内部 owner Unload | 重新建立每次 Begin 的切点、真实 receipt 来源与名字重用关系；保留每个严格失败域 |
| 合法 surviving execution 的终点观察恢复 | 原 Equation (55) 的一般前缀表达式 | 连接实际恢复与原冻结 state-map 组合；不能以 catalogue provenance 代替值 replay |

每一步都需要可达的非空实例，覆盖新允许的交错，而不只是复用旧片段的实例。68／69／79 目前仍为 `partial`。

## 4. 推进 canonical form、进展和一般调度结论

已有 guarded 外部／生命周期交换、共享 provider 的真实 Iter diamond、有限后缀运输，以及同一源轨迹的局部重写正常形唯一性。继续工作须明确外部输入的完整 payload、fresh 名字／birth handle 的运输和实际历史 token 对应。

验收目标是从原实际轨迹构造合法重排和可达终点，并证明适用的唯一性或汇合；不能把反序合法、相同终态、全局交换或公平性偷放为前提。有限前缀安全与局部正常化不等于 liveness。原文 71(2) 的无条件闭合反例保留，修订进展定理必须明确调度／最大性条件。78／80 的通用结论仍开放。

## 5. 扩大可执行与宿主连接

- 扩大闭合驱动语言或验证 callback 接口，保持实际参数、raw outcome、continuation 和 returned inverse 的来源；不允许调用者提供期望结果充当执行。
- 在单个 owning admission 之外处理多个在途阶段，证明 generation、取消、落地和回执归属；先给可运行程序与精确不变量。
- 分别形式化 Runtime、事件 drain、timer、loader reconciliation 和 persistence 的关键协议，再连接内核。普通 Rust 集成测试继续保留，但不能升格为任意 Future／I/O 的证明。
- 在性能工作前建立可复现基准，特别记录闭合驱动的机器复制、历史增长和 tombstone 成本；不提前承诺生产吞吐量。

整篇完成门槛仍是[ledger](paper-obligations.json)的原条目审计加 4 项整体连接义务。`python3 scripts/check-paper-coverage.py --require-complete` 当前应拒绝。原文修订、反例审计完成与原文全部成立是三个不同结果，任何发布说明都应说明交付的是哪一个。


## 6. Node 长期架构的下一轮交付

2026-10-06 本轮已接入默认 Harness 配置 UI：ConfigEditor 的文件锁、写入、
reconcile/rollback，Include.refresh 和 HMR 队列进入同域事务；真实官方类的
测试覆盖失败恢复与旧代次拒绝。WorkerDomain 提供实际观测模块图、影响闭包与
整体替换恢复，官方 Loader 另有支持范围内的原地模块替换路径。typed Rust adapter 显式支持动态 publication、子插件及已声明服务的动态值与 availability。
这些交付没有关闭完整 M5/M6 或论文 refinement。

本轮继续补齐独立原生模块的宿主入口：Controller 的 `reconcile` 同时捕获
制品与 recipes，支持配置变更、增删和空列表停用；`createRustModulePlugin`
提供普通 Loader 插件，配置校验在旧实例退役前验证制品，setup 仅挂载已准备的
owned children。`officialTransaction` 可把官方 ConfigEditor 修改、指定消费者
就绪检查和应用恢复放在同一 FIFO revision，回调仍不能借用宿主权限。
随后接入独立 C ABI 的声明式服务注入与异步反向 JS 调用，复用已有作用域、
committed provider、重入和清理屏障。真实 cdylib 验收覆盖 provider 更新、
取消后排空、丢弃调用 Future 与有界结果。独立库进一步提供 Rust-owned 流与对象，
按需拉取、并发方法、关闭重试及代码换代复用现有资源生命周期。反向 JS 流、
对象和 callback 也已通过动态 SDK 接入，同一 action journal 管理迟到获取、
取消排空与关闭重试。跨 ABI 的 mount 与动态 factory publication 进一步接入真实
owned child、独立 owner anchor、ready/retire/join 与 cleanup retry；定义随原始库固定，
直到实际 Removed 才释放。它没有跨库共享 typed slot，也不等价于 ServiceHandle::set。
显式状态迁移现支持 factory schema、版本化 JSON checkpoint、排空后采集、setup 前恢复，
以及普通 Loader 与官方消费者验收期间固定的回滚快照；失败和重试保留同一恢复源。
这些宿主改动没有新增论文证明。

| 下一项 | 需要解决的边界 | 验收条件 |
| --- | --- | --- |
| 独立 Rust 模块扩展 | 首版 C ABI 的同进程换代、失败恢复、配置 reconcile、普通 Loader 插件与常驻映像预算已实现；反向 JSON 服务与双向流/对象及 JS callback 已接入；真实 owned child 与动态 factory publication 已接入；显式状态迁移和事务回滚快照已接入；继续处理跨平台运行保障与长期驻留成本 | 同图真实 native 场景、失败保留、跨平台执行；物理卸载需要额外资源和代码引用证明，不以逻辑清理冒充 |
| 隔离宿主扩展 | ProcessDomain 与 Harness Web/standard opt-in watcher 已接入；继续扩展 CLI 覆盖和运行保障 | 默认应用的模块更新、客户端重连、候选失败恢复；应用 addon 需真实进程隔离与验收 |
| 长期运行成本 | 已测量 1,000 次驻留生命周期并自动回收失效 binding；新增 3 次独立的 1,000 轮 checkpoint 原生换代基准，活动资源和快照凭据有界且关闭归零，固定两份代码映像；已将单调 LeaseId 与活跃记录分离，释放即回收，失败 cleanup 仍保留租约；identity/publication tombstone 仍增长，见[实测](benchmarks.md#2026-10-06-lease-record-reclamation) | 源码绑定的反复装卸数据、驻留资源与变更耗时；回收设计不能破坏旧 handle 失效保证 |
| 模块依赖图精化 | 当前图只记录已执行的 Node 解析，执行器保守替换整个 Worker | 完整安装图、未执行动态导入、可保留 identity 的模块边界；不能用观测图冒充静态完备图 |
| 剩余 typed Rust 接口 | 已接入新建/撤销 publication 与子插件；继续处理 effect group、每 Fiber 动态 injection config、更新 hook 与反向 typed JS 服务 | 同图 Rust/JS 生命周期与权限一致，真实子图及失败路径验收；保留现有槽位和 cleanup 合同 |

跨平台制品实际安装、完整发布负控及宿主到论文的整体 refinement 继续按各自门槛执行。

## 7. 可审查的开源证据与兼容缺口

首组[证据入口](evidence-guide.md)已提供四路异步清理复现、英文功能对齐说明，以及五条论文到合同、执行代码和回归的审查链；映射检查接入日常开发门槛。它们是新增审查材料，不提升论文 ledger 状态。

最新[上游差分归档](evidence/README.md)为 upstream 87/87、native 83/87。下一轮兼容工作应先处理两个新增缺口：并列 provider/consumer 更新的合并语义，以及清理期资源注册错误的兼容文本；先写明是否有意改变合同，再增加针对回归、重跑原样上游套件和 Harness 验收。另两项 committed publication 和 cleanup failure 的有意差异继续公开保留。

运营验收关注外部独立复现、实际插件接入与一次相关修改后的重新验证；当前没有声称已有外部采用。完整发布负控、跨平台实际运行和公开前安全报告渠道见[证据指南](evidence-guide.md)。
