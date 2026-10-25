# 所有权与审查地图

[English](review-map.md) · 简体中文 · [计划](verification-plan.zh-CN.md) · [生成式证据](cases/generated-lifecycle.zh-CN.md)

从操作拥有的状态开始审查。生产函数与其 Verus 合同保持放在一起。下表分类的是职责
和审查路径，不表示目录内每个函数都是生产调用者。

下述清理链路审计是[结构计划](verification-plan.zh-CN.md#后续结构工作)的首批实施。
它区分实际状态所有者、受检转换和普通宿主职责，不代表整个仓库的修改入口或证明
依赖审计已经完成。

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

## 清理所有权审计

范围为 provider／consumer／一层 Child 的更新、清理失败与显式重试，以及对应的
Node 确认／释放边界。本次沿可执行调用及其合同审查。下表列出选定状态及其修改
入口族，不穷举这些所有者内其他服务、动态接口、配置或一般重放操作。

| 权威状态 | 修改入口与实际调用者 | 必须保持的合同或边界 |
| --- | --- | --- |
| [`Kernel`](../crates/cordis-kernel/src/lib.rs)：`nodes`、`declarations`、`links` | 构造／注册及 provision／依赖修改建立身份；`begin` 捕获 committed bindings；`leave`、`retire`、`begin_cleanup`、`finish_cleanup`、`remove` 和压缩通过受检 API 修改控制／存储。[`LifecycleState`](../crates/cordis-kernel/src/lifecycle_state.rs) 拥有 kernel 并记录控制转换。 | `resource_safe`、`ordering`、`cleanup_enabled`、`bindings_except` 及附着的 refinement step。目标变化不替换运行 Episode 已承诺的 provider；压缩保持观察，退休与移除含义不同。 |
| [`LifecycleActions`](../crates/cordis-kernel/src/lifecycle_actions.rs)：`ledger`、`cleanups`；[`ActionLedger`](../crates/cordis-kernel/src/action_ledger.rs)：`domain`、`next`、`entries` | `begin`／清理请求发行票据；`complete_setup`／`complete_cleanup` 消费票据；`retry_cleanup` 替换失败尝试；finish 删除清理记录。ledger 构造后的修改入口只有 `issue` 和 `complete`。 | `wf`、`cleanup_reply_enabled`、`history_preserved`、`eligible`、`finish_enabled`。合法回复须匹配 domain／action／owner／generation／kind；错误路径保持状态。`execute_cleanup` 组合这些合同，自身不是另一份状态存储。 |
| [`CleanupJournal`](../crates/cordis-kernel/src/cleanup_journal.rs)：`stages`、`domain`、`next`、`current`、`failed` | scope／iterator 构造；register／land／admit／end／cancel；`begin_restore`、`complete`、`retry`。调用来自队列，不使用宿主自建票据计数器。 | `RestoreTicket` 标识单个逆操作的尝试。失败保留所选 token，重试增加 attempt，旧／重复回复不能消费当前尝试；它与整个 Episode 的 `ActionTicket` 职责不同。 |
| [`CleanupQueue`](../crates/cordis-kernel/src/cleanup_queue.rs)：`journal`、`payloads`、`in_flight`、`joint` | register／land 填充槽位，attachment 接入执行 journal；pop／dispatch 取出载荷；complete／restore 归还或消费载荷；retry 保留槽位。`*_following` 变体同时连接实际 journal 来源。 | `wf`、`completion_enabled`、`same`、`retry_enabled` 及完成合同将所选 token 关联到真实槽位。[`complete_future`／`complete_failure`](../crates/cordis-kernel/src/cleanup_queue/completion.rs) 返回被拒绝的载荷；宿主确认不能冒充受管逆操作。 |
| 受管值与保留的逆操作 | [`Inverse::restore_following`](../crates/cordis-kernel/src/reversible_value.rs) 在锁内检查实际 value／depth；[`payload::Inverse`](../crates/cordis-kernel/src/reversible_value/payload/restoration.rs) 检查保留的载荷版本，payload dispatcher 在失败时放回逆操作。 | 标量恢复失败返回同一个 inverse；载荷失败保留重试所需版本／inverse。共享值修改与 publication 槽位替换是不同操作，任意 `Arc<T>` 内部仍在保证之外。 |
| [`SharedChild`](../crates/cordis-kernel/src/lifecycle_state/registration/shared_child.rs)：共享 `inner` cell 与不可变 `origin` | `enqueue_native_child` 一起创建请求和逆操作；`register_shared_child` 在同一把锁下分配真实身份；`reject`／`retire_shared_child` 决定或退休同一个槽位；宿主使用实际返回的句柄 dispatch。 | 请求／逆操作身份、父代次与前后 `ChildTransition` 一致；pending 时取消后不能再分配。父子所有权不自动引入服务依赖。 |
| Native Episode、实际执行及轮询控制 | [`NativeRuntime`](../crates/cordis-kernel/src/lifecycle_state/native/runtime.rs) 拥有 `host`、`services`、`owners` 及关联历史；[`RecordedExecution`](../crates/cordis-kernel/src/reversible_value/managed/interleaving/history/lifecycle.rs) 拥有实际 work／cleanup 状态与历史见证；[`PollControl`](../crates/cordis-kernel/src/poll_control.rs) 拥有 Episode／work 身份、失败与重启状态。本路径由 controlled begin／retry／release 和失败记录修改。 | 实际 API 建立或检查 `owns_execution`、`bound`、`matches`、work idle 和队列 drained。重试通过受检转换清除失败；守卫允许卸载后才移除匹配的 owner／publication，并返回值交给宿主析构。 |
| Node 清理状态与保留的 publication | [`NodeRuntime`](../crates/cordis-kernel/src/node_runtime.rs) 拥有 `control`、`store`、`admissions`、`episodes`、`restoring` 及待释放句柄；`begin`、`cleanup_with_error`、Episode 命令和 release 修改 Episode；[`resources`](../crates/cordis-kernel/src/node_runtime/resources.rs) 导出／修改保留清单；handle drain 将已释放值移交适配器。 | `wf` 与 `history::operation` 连接观察。`cleanup_allowed` 拒绝裸 `Release`，资源专用 `release`／`release_reservation` 检查真实 admission／lease／publication。`cleanup_failed` 和诊断是受检宿主状态观察，不是另一份释放权限；JS 清理成功仍来自宿主报告。 |
| 普通 Rust callback 尝试 | [`RunningCleanup`](../crates/cordis/src/runtime/cleanup/attempt.rs) 私有持有票据、实际 Future 和重试工厂；`start`／`poll` 产生字段不公开的 `CleanupCompletion`；`Cleanups::complete_reply` 经原有验证完成 API 消费它。[`Runtime`](../crates/cordis/src/runtime/cleanup.rs) 和 [`StaticCleanupFuture`](../crates/cordis/src/runtime/static_host.rs) 保存／取走 pending 尝试。 | Pending 保留 Future 和工厂，Ready 结果携带自身工厂，不再由调用方分别配对。调用者在 Episode 锁内确认，出锁后丢弃拒绝／废弃载荷及已完成 Future。这层由 Rust 隐私约束和运行回归支撑，不构成 callback 效果或调度进展的 Verus 证明。 |

### 调用与证明依赖

| 审查路径 | 必需代码与证明支持 | 前提来源／边界 |
| --- | --- | --- |
| 宿主 callback → attempt → `RecordedExecution::complete_future`／`complete_failure` → `Execution` → queue → restore journal | [`async_completion`](../crates/cordis-kernel/src/async_completion.rs)、[`poll_result`](../crates/cordis-kernel/src/poll_result.rs)、recorded [`callbacks`](../crates/cordis-kernel/src/reversible_value/managed/interleaving/history/lifecycle/callbacks.rs)／[`host`](../crates/cordis-kernel/src/reversible_value/managed/interleaving/history/lifecycle/host.rs)、队列完成及 journal 合同 | 实际 await 结果与捕获票据配对；宿主仍负责轮询、捕获 panic 及选择失败策略。普通 Runtime 使用 `DrainConsumed`，静态宿主使用 `RetainFailure`；可重试失败在两者中均阻塞。`Drained` 不等于恢复成功。 |
| Native poll／retry／release → shared `NativeDriver` → recorded controlled API → `NativeRuntime`／`PollControl` → `NativeHost` → `LifecycleState` | Recorded [`native`](../crates/cordis-kernel/src/reversible_value/managed/interleaving/history/lifecycle/native.rs)、[`native/managed`](../crates/cordis-kernel/src/lifecycle_state/native/managed.rs)、[`services`](../crates/cordis-kernel/src/lifecycle_state/services.rs)、[`execution`](../crates/cordis-kernel/src/lifecycle_state/execution.rs)、cleanup groups 与共享 action／control 合同 | 实际 owner 身份、work idle 及队列 drained 由代码检查，释放结果来自这些队列。Native history／Child receipt 是连接真实 unload 的必要证明，不能因其为 ghost 代码就当作可删实验。 |
| Node facade／driver → `NodeRuntime::complete`／资源释放 → 共享 cleanup／control 与 publication store | [`NodeDriver`](../crates/cordis-driver/src/node.rs)、[`node_runtime::history`](../crates/cordis-kernel/src/node_runtime/history.rs)、[`Admission`](../crates/cordis-kernel/src/availability/admission.rs)、[`PublicationStore`](../crates/cordis-kernel/src/publication/values.rs)、[`资源释放`](../crates/cordis-kernel/src/lifecycle_actions/resources.rs) | 验证状态所有者检查表示出来的关联；N-API 句柄关联、JS 对象内部、外部清理真实性保留宿主边界。单独一条报告不能绕过 publication／lease 释放守卫。 |
| 共享清理执行 → 有限历史保证 → 论文转换 | [`cleanup_step`](../crates/cordis-kernel/src/lifecycle_state/cleanup.rs)、`failed_prefix_retains_dependencies`、`consumed_ticket_never_returns`、`release_has_accepted_report`；再接 `LifecycleActions`、`ActionLedger`、`Kernel::ordering`、[`refinement`](../crates/cordis-kernel/src/refinement.rs) 及其必要不变式／历史引理 | 定义 52–54 与 L-Unload 对应所有权、已承诺依赖保护及卸载；票据新鲜性属于实现机制。有限历史安全性不自动提供一般恢复、公平调度或终止。 |

以上是选定保证已审查的依赖路径，不是整个 crate 的自动生成传递符号图。结构调整
必须保留必需的历史／refinement 支持；其他一般证明分支要核对调用者与对外主张后
再分类。运行／构建依赖另行区分：Rust 库使用 `cordis-driver` 和 `cordis-kernel`，
Node／N-API 是可选适配器，被擦除的历史／引理代码不引入运行时 Node 依赖。

### 首项所有权收拢

此前 `initialize_cleanup`、`poll_cleanup_callback`、完成枚举及
`Cleanups::complete_reply` 分散在 `runtime.rs`，两个宿主分别传递回复与重试工厂。
现在统一到 [`cleanup/attempt.rs`](../crates/cordis/src/runtime/cleanup/attempt.rs)，
私有字段使其他 runtime 模块不能自行构造或拆分完成结果。两个调用者均保留 Future
直到确认／错误处理完成，再在锁外析构。公开 API 和内核合同保持不变。

两种失败策略及 action／restore ledger 因语义不同继续分开。`Episode`／`SharedEpisode`、
effect 句柄所有权和更广的 Node 接口仍需后续审查。本批完成一项受限维护改进，
不代表结构路线图或 R01 整体完成。

既有回归包括 [`retry_cleanup`](../crates/cordis/tests/retry_cleanup.rs)（多失败 group、
工厂／Future panic、pending 工作保留、工厂析构重入）、
[`static_host`](../crates/cordis/tests/static_host.rs)（不可重试的失败保留及 Child 清理）
和 [`update_recovery`](../crates/cordis/tests/update_recovery.rs)（provider／consumer／Child）。
集成结果以最终源码开发记录为准，历史 campaign／负控记录保持自身源码绑定。

## 源码组织及依赖方向

| 区域 | 所有权／用途 | 审查分类 |
| --- | --- | --- |
| [`lifecycle_state/`](../crates/cordis-kernel/src/lifecycle_state/)、[`lifecycle_actions/`](../crates/cordis-kernel/src/lifecycle_actions/)、动作／清理 ledger | 共享生命周期权限和旧 provider 保护 | 生产状态、附着合同及轨迹组合 |
| [`reversible_value/`](../crates/cordis-kernel/src/reversible_value/)、[`cleanup_queue/`](../crates/cordis-kernel/src/cleanup_queue/)、[`cleanup_groups/`](../crates/cordis-kernel/src/cleanup_groups/) | 受管操作、保留逆操作、实际执行来源和历史 | 生产 primitive 及解释／迁移证明，一般性边界保持明确 |
| [`lifecycle_state/native/`](../crates/cordis-kernel/src/lifecycle_state/native/)、[`node_runtime/`](../crates/cordis-kernel/src/node_runtime/) | 各自建立共享协议前提的 Native／Node 状态所有者 | 生产连接；Node 记录 publication／句柄／scope，不证明 JS 对象内部 |
| [`refinement.rs`](../crates/cordis-kernel/src/refinement.rs)、[`dependent_grammar.rs`](../crates/cordis-kernel/src/dependent_grammar.rs)、grammar／history／recovery 及 [`mixed_driver/`](../crates/cordis-kernel/src/mixed_driver/) | 论文语义、条件定理、参考执行器及实际历史连接 | 规格与证明支持，包含可执行研究 driver；被擦除或没有宿主调用者不代表冗余 |
| [`paper_counterexamples.rs`](../crates/cordis-kernel/src/paper_counterexamples.rs)、恢复／mixed 示例、定向负控和冻结报告 | 反例、修订解释、准入示例和证伪 | 保留的研究证据，导航单列，活跃验证目标不变 |
| [`cordis-driver/src/shared/`](../crates/cordis-driver/src/shared/)、[`node.rs`](../crates/cordis-driver/src/node.rs) | 共享调度策略、命令解析和宿主适配 | 普通 Rust 连接，不自动成为已证明的调度器 |
| [`runtime/setup.rs`](../crates/cordis/src/runtime/setup.rs)、[`services.rs`](../crates/cordis/src/runtime/services.rs)、[`cleanup.rs`](../crates/cordis/src/runtime/cleanup.rs)、[`poll.rs`](../crates/cordis/src/runtime/poll.rs) | Episode API、服务句柄、清理 dispatch 和协作轮询；callback 尝试封装在 [`cleanup/attempt.rs`](../crates/cordis/src/runtime/cleanup/attempt.rs) | 普通宿主；其他状态所有者和生命周期入口留在 [`runtime.rs`](../crates/cordis/src/runtime.rs)，保持锁／析构顺序 |
| 可选 Node facade／N-API／进程／cdylib | 语言语义、callback、传输和外部 I/O | 通过测试检查的宿主边界；纯 Rust 不依赖 Node，Harness 保持独立应用 |

依赖方向仍为宿主 → 共享 Driver → 验证状态所有者 → 共享生命周期／资源协议。
数学支持为附着合同提供定理，不引入运行时 Node 依赖或第二份实现。
[架构文档](architecture.md)说明工具链、库、编译器、验证器和 FFI 信任前提。

## 积累内容的处置

| 重构前内容 | 处理和理由 | 检查 |
| --- | --- | --- |
| 253 个通过 `#[path]` 连接的平铺文件 | 按既有逻辑模块路径移动：先 41 个生命周期文件，再 212 个剩余文件；移除全部 255 个路径属性，其中两个本来就多余。公开模块身份不变。 | 除路径属性／引用外，函数体与合同精确相等；编译、完整 Verus、打包及规范负控锚点检查 |
| 5,195 行普通 `runtime.rs` | 先拆清理，再拆 setup、服务句柄方法和轮询；该布局批次结束时主文件为 3,139 行。公开类型／导出不变，只调整必要的内部方法可见性。 | 方法体比对、Cargo／lint、原宿主回归和抽取包构建 |
| 同一严格负控执行器的 15 个包装入口 | 合并为 `check-profile-controls.py PROFILE` | 保留规范选择、新正向基线、完整变异编译及精确合同拒绝；独有 full／R2 检查器保留 |
| 两个普通宿主分别传递 callback 回复／工厂 | `runtime/cleanup/attempt.rs` 统一私有尝试所有者和完成结果，保留受检队列与两种宿主失败策略 | 全目标编译、既有 retry／static-host／update 回归及最终开发验收；不新增内核定理主张 |
| 重复入口清单 | 按任务组织文档首页、当前审查地图及单一 campaign CLI | 链接、源码绑定和中英入口 |
| 一般模型、条件恢复分支、独有失败与冻结报告 | 研究导航中保留，继续使用原有验证目标 | 移文件不关闭义务，历史通过保持原始源码绑定 |

固定归档为 `codex/archive-before-refactor-2026-10-24`（`60bdd89`）；第二批整理前的
布局也保存在 `c47d111`。不改写历史或上游锁。本轮**没有批准删除独有语义成果**。
进一步删除须比较前提／结果、调用方、证明依赖与独有反例；存在归档本身不是删除
当前对外保证所依赖定理的理由。
