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
| [`SharedChild`](../crates/cordis-kernel/src/lifecycle_state/registration/shared_child.rs)：共享 `inner` cell、不可变 `origin` 及保留的执行 Journal | `enqueue_native_child` 一起创建请求和逆操作；`register_shared_child` 在同一把锁下分配真实身份；`reject`／`retire_shared_child` 决定或退休同一个槽位；宿主使用实际返回的句柄 dispatch。 | 请求／逆操作身份、父代次与前后 `ChildTransition` 一致；pending 时取消后不能再分配。父子所有权不自动引入服务依赖。 |
| Native Episode、实际执行及轮询控制 | [`NativeRuntime`](../crates/cordis-kernel/src/lifecycle_state/native/runtime.rs) 拥有 `host`、`services`、`owners` 及关联历史；[`RecordedExecution`](../crates/cordis-kernel/src/reversible_value/managed/interleaving/history/lifecycle.rs) 拥有实际 work／cleanup 状态与历史见证；[`PollControl`](../crates/cordis-kernel/src/poll_control.rs) 拥有 Episode／work 身份、失败与重启状态。本路径由 controlled begin／retry／release 和失败记录修改。 | 实际 API 检查 `owns_execution`、`matches`、work idle 和队列 drained；工厂建立 `bound`，Driver 在使用控制对象前检查保留的 Native 分配，见下文审计；其他执行／表示前提仍单独保留。重试通过受检转换清除失败；守卫允许卸载后才移除匹配的 owner／publication，并返回值交给宿主析构。 |
| Node 清理状态与保留的 publication | [`NodeRuntime`](../crates/cordis-kernel/src/node_runtime.rs) 拥有 `control`、`store`、`admissions`、`episodes`、`restoring` 及待释放句柄；`begin`、`cleanup_with_error`、Episode 命令和 release 修改 Episode；[`resources`](../crates/cordis-kernel/src/node_runtime/resources.rs) 导出／修改保留清单；handle drain 将已释放值移交适配器。 | `wf` 与 `history::operation` 连接观察。`cleanup_allowed` 拒绝裸 `Release`，资源专用 `release`／`release_reservation` 检查真实 admission／lease／publication。`cleanup_failed` 和诊断是受检宿主状态观察，不是另一份释放权限；JS 清理成功仍来自宿主报告。 |
| 普通 Rust callback 尝试 | [`RunningCleanup`](../crates/cordis/src/runtime/cleanup/attempt.rs) 私有持有票据、实际 Future 和重试工厂；`start`／`poll` 产生字段不公开的 `CleanupCompletion`；`CleanupCompletion::acknowledge` 经原有验证完成 API 消费它。[`Runtime`](../crates/cordis/src/runtime/cleanup.rs) 和 [`StaticCleanupFuture`](../crates/cordis/src/runtime/static_host.rs) 保存／取走 pending 尝试。 | Pending 保留 Future 和工厂，Ready 结果携带自身工厂，不再由调用方分别配对。调用者在 Episode 锁内确认，出锁后丢弃拒绝／废弃载荷及已完成 Future。这层由 Rust 隐私约束和运行回归支撑，不构成 callback 效果或调度进展的 Verus 证明。 |

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

### 释放回执的单一守卫

[`lifecycle_actions/finish.rs`](../crates/cordis-kernel/src/lifecycle_actions/finish.rs)
集中回执选择、生命周期／reservation 完成及最终记录删除。公开方法仍属于
`LifecycleActions`，前提、结果及保持性合同不变。私有 `finish_index` 合并原来的三份
代次／结果／释放模式检查，返回的索引在同一次调用中使用；公开资源预检只返回代次，
不签发可转交或保留的释放权限。

这个所有者的 `cleanups` 表的完整写入清单如下：

| 入口 | 修改及所需证明支持 |
| --- | --- |
| `new` → Begin／清理请求调用 `issue` | 初始化空表；`ActionLedger::issue` 后追加 Pending 清理记录。容量预检与 `wf` 建立所有者唯一性、新动作身份及对应的 pending ledger 项；setup 动作不追加清理记录。 |
| `complete_cleanup` | 验证精确 pending 票据，消费 ledger 项，再将该记录替换为报告结果。`cleanup_reply_enabled`、ledger 完成合同和 `completion_frame` 保持其他所有者及历史边界。 |
| `retry_cleanup` | 要求当前 restoring／reservation 代次的 Failed 记录，发行新票据并把该记录替换为 Pending。`retry_enabled`、ledger 唯一性和保持性证明保留其他记录。 |
| finish 模块私有的 `remove_cleanup` | `finish_index` 接受后才删除已确认记录；普通完成还须先调用 `Kernel::finish_cleanup`。证明保持 `wf`、`history_preserved` 与 `no_new_release`，宿主没有独立的回执缓存参与决策。 |

只读选择由 `cleanup_index`、表不变式及 Kernel 实际代次／phase 观察建立
`finish_enabled` 或 `reservation_finish_enabled`。普通完成继续依赖
`Kernel::finish_cleanup` → `refinement::Rule::Unload`；reservation 完成保持 Kernel
不变。资源释放仍先经过
[`PublicationRegistry::cleanup_batch`](../crates/cordis-kernel/src/publication/cleanup.rs)
的独立校验，再释放 committed bindings；资源校验失败保留原 registry、控制及回执状态。
提交时重新检查回执资格，旧预检结果不能在状态变化后充当权限。

Pending／Failed、错误代次和错误释放模式仍返回 `InvalidState`；Succeeded 与
Drained 保留原有不同宿主含义。callback 真实性、队列恢复和依赖顺序继续各有义务，
不从一份报告推导这些性质。

普通宿主的 [`record_cleanup_report`](../crates/cordis/src/runtime/cleanup.rs) 共用同步
Child 结果和成对 callback 完成的后续处理，调用时确认已经离开 Episode 锁。它先析构
废弃工厂再记录错误，仅将 Failed 标为阻塞；两类确认入口、被拒载荷处理、Future 寿命
及静态宿主策略继续分别保留。

既有清理结果／资源、重试、静态宿主与更新恢复测试覆盖保留行为。定向负控检查接受
Failed、忽略代次、绕过回执及资源校验前提交这四类错误，仍要求新正例、完整变异编译
和指定合同拒绝，范围与完整负控套件分开。

### 执行所有权与队列修改入口

[`Episode`](../crates/cordis/src/runtime/episode.rs) 直接持有 `RecordedExecution`。
`SharedEpisode::checked_lock` 检查关联后，setup、root、Child、service 和 cleanup
都使用这一执行对象。没有独立的 `Cleanups` 所有者或宿主回执缓存。
普通宿主的 `register_cleanup` 只断言已有的活 group 准入结果，不自行决定资格或
再存储一份载荷。

以下具体写入补齐所选队列／回执清单，不代表枚举了 `RecordedExecution` 支持的全部操作。

| 权威字段 | 构造及全部后续修改入口 | 必需不变式／用途 |
| --- | --- | --- |
| `CleanupQueue.payloads`、`in_flight` | `scope`／`iterator`；`register_following`、`land`、`pop_following`、`complete_following`。`register`、`pop`、`complete` 转发到这些入口；完成、dispatch 和 landing 适配器也经这些入口修改。 | `local_wf` 关联占用槽位、等待 token 和选中且已发出的尝试；`same` 保留拒绝路径状态；`retry` 不改变载荷槽位。 |
| `CleanupQueue.journal` | 构造；`register_following`／`land`、`pop_following`、`complete_following`、`retry`、`admit`／`end`／`cancel` 调用自身 journal。 | [`CleanupJournal`](../crates/cordis-kernel/src/cleanup_journal.rs) 拥有 stage 状态和 attempt 计数。`begin_restore`／`retry` 分配尝试；`complete` 保留失败 selection。`current` 隐藏已失败回执，`receipt` 仍暴露保留的 selection，二者不可互换。 |
| `CleanupQueue.joint` | 初始为空；`attach_execution` 一次分配 member；`commit`／`commit_following` 在真实队列变化后更新该 member 的历史。 | `cleanup_step`、`traces`、`wf` 将占用观察对应到同一 Journal；`issue_receipt`、`latest_receipt`、`drained_observation` 支持生产历史，不是第二份可变权限。 |
| callback 票据、Future 与重试工厂 | [`RunningCleanup::start`／`poll`](../crates/cordis/src/runtime/cleanup/attempt.rs) 构造尝试及成对完成；`CleanupCompletion::acknowledge` 消费自身，将这一对值交给持有的执行对象。 | 宿主保留 Pending 工作，在 Episode 锁内确认，锁外析构拒绝／废弃载荷及已完成 Future。同步 Child 报告保留独立入口，不再接收无用途的重试工厂参数。 |

[`reply_pending`](../crates/cordis-kernel/src/cleanup_queue.rs) 是直接队列完成、callback
结果、Future 结果、失败报告及受管值恢复共用的可执行回执谓词。精确合同要求票据
匹配已发出、被选中且未失败的尝试；受管路径在**恢复值之前**执行检查。
`complete_following` 另行检查只有 Failed 才能保留载荷；`completion_condition`
向证明调用者展开组合条件。合并重复回执分支没有削弱公开完成合同或保留规则。

因此，修改回执规则只需审查一个谓词及其适配入口。Action／inverse 票据、
`DrainConsumed`／`RetainFailure`、受检载荷恢复／宿主 callback 仍有不同合同。
既有 `retry_cleanup`、`static_host`、`update_recovery` 回归覆盖失败重试、panic、
工厂析构重入及 provider／consumer／Child 执行；最终源码的
[验收门槛](cases/generated-lifecycle.zh-CN.md) 还将实际行为与严格证明拒绝配对。
这些结果不证明 callback 的外部效果或公平调度。

## Episode 与句柄所有权

普通宿主把 `Episode`、不可变 `SharedEpisode` 元数据和受检锁集中到
[`runtime/episode.rs`](../crates/cordis/src/runtime/episode.rs)，把句柄构造、状态访问及
全部等待／通知字段集中到
[`runtime/effect_handle.rs`](../crates/cordis/src/runtime/effect_handle.rs)。公开的
`EffectHandle`、`EffectJoin` 和 `AsyncSetup::effect` 路径保持不变。

本节审计覆盖下表的关联与句柄字段，不宣称全部可变 Episode 字段已封装完成。
下一节另行审查 Child 所有权及外部宿主报告边界。

| 状态／所有者 | 本范围修改入口 | 合同或宿主边界 |
| --- | --- | --- |
| `SharedEpisode`：association、generation、context、service 元数据、anchor 和 Episode mutex | `native` 从实际保存的 execution 导出元数据；`external` 从受检静态 values 导出 association／generation，并检查关联。字段私有，仅暴露只读元数据访问。 | `Association::native`／`matches` 和 `static_values::Values::from_definition` 提供身份合同；每次 `checked_lock` 检查最初 execution 的关联。静态 realm／anchor 仍来自嵌入宿主。 |
| `Episode`：values、记录型清理执行及宿主状态 | Native `Runtime::start` 与静态 `begin_inner` 构造；发布后 setup、poll、cleanup、静态宿主仅经受检 guard 修改。`withdraw`、`seal_external`、`provide` 保留原有受检调用。 | values 与清理派发仍使用较宽 guard；Child 保留列表及私有通知／能力状态的审计见下文，移动或封装字段不增加内核证明。 |
| `EffectStatus`：受检 owner 和 Episode 弱引用 | `AsyncSetup::effect` 在句柄逸出前分配并绑定实际 group 的 status；`EffectHandle::service` 从锁内 execution 创建服务状态。没有生产重绑定入口。 | 弱引用避免 Episode／group／handle 所有权环。`matches_episode` 在轮询或取消之前检查分配身份和内核签发的执行关联；语义权威仍是 `HostStatus`。 |
| Effect 取消、初始化和完成 | `cancel`、`mark_cancelled`、`poll_driver` 请求取消；`initialize_effect`、`retire_effect` 使用实际 group／runner 调用原有 Execution 守卫。 | 取消不代表工作结束；`initialize_effect_status` 要求工作已落地，`retire_observed_effect` 检查真实队列并先记录 group 移除再记录完成。退休条件仍取决于所选清理策略。 |
| 服务报告和状态错误载荷 | `assign_service_child`、`initialize_service`、`fail_service_cleanup`、`finish_service`；`record_error`、`record_unique_error` 追加实际错误。 | 使用已有 `HostStatus` 合同，包括 Child 唯一分配、保留首个 terminal error；服务报告不能结束 effect，终止失败不等于成功移除。外部清理是否真正成功仍是宿主前提。 |
| Join ID 和 waiter map | `EffectJoin::poll` 分配／登记／替换或移除等待者，`Drop` 注销；effect 初始化／退休以及服务分配／初始化／失败／移除在原有通知点取出等待者。 | 每个 join 保留独立 ID；初始化唤醒不等于 join 完成，外部 Child 等待边守卫不变。Waker clone、替换析构及调用均在 status 锁外。 |
| 句柄 driver waker 和 notify callback | 构造时保存可选 callback；`poll_driver` 替换 driver；`cancel`、`replace_service_value`、`refresh_driver` 取走 driver 并 clone callback；`finish_service` 取走两者用于释放。 | 私有 `Notification` 在调用前移出锁内状态。服务值替换与取消／完成检查仍原子进行；被拒绝／替换的载荷在锁外、通知前析构。 |

组合操作保持 Episode → status → checked cell → Journal 的锁顺序。单独的句柄操作
不会持有 status 再获取 Episode。服务 callback、waker 和返回载荷的析构在解锁后进行。
Native 服务初始化保留原有不唤醒 join 的策略，静态服务初始化继续唤醒；driver 自身
标记取消也不通知正在运行的 driver。不能因共用状态所有者就合并这些宿主策略。

证明依赖为关联处的 `host_context`／`static_values`，以及
[`host_status`](../crates/cordis-kernel/src/host_status.rs)、Execution
[`状态守卫`](../crates/cordis-kernel/src/host_status.rs)、recorded
[`宿主转换`](../crates/cordis-kernel/src/reversible_value/managed/interleaving/history/lifecycle/host.rs)
和 [`joint/host`](../crates/cordis-kernel/src/reversible_value/joint/host.rs)。它们保持
[R2 执行说明](r2-execution.zh-CN.md)中定义 58／63 的观察与清理连接。Rust 隐私约束
缩小适配器的修改面，不构成普通 mutex、任意 callback、公平调度或整篇恢复的新证明。

修改句柄唤醒所有权时，现在只需维护一个实现位置，不必跨 setup、services、poll 和
cleanup 直接修改字段；调用方继续明确选择调度和失败策略。既有身份错配检查移到
私有存储旁，没有新增生产绕过入口。
[`runtime_waiters`](../crates/cordis/tests/runtime_waiters.rs)、
[`static_host_join`](../crates/cordis/tests/static_host_join.rs) 和
[`static_host`](../crates/cordis/tests/static_host.rs) 覆盖取消、等待者替换／重新登记、
析构重入、外部等待边和通知重入；没有增加测试框架或运行依赖。

## Child 请求与完成所有权

[`runtime/child.rs`](../crates/cordis/src/runtime/child.rs) 集中 Child 准入、原始句柄、
pending 请求载荷及 Native 请求执行；
[`child/external.rs`](../crates/cordis/src/runtime/child/external.rs) 拥有外部分配报告、
退休／移除状态及完成通知。`ChildHandle` 和
`runtime::static_host::StaticChildControl` 的公开 API 保持不变。

| 状态／所有者 | 本范围修改入口 | 合同或宿主边界 |
| --- | --- | --- |
| Native pending recipe 与诊断错误 | 仅 `mount_request` 构造 `NativeChildInput` 与返回句柄；`apply_child_request` 消费受检请求，把其中实际 `SharedChild` 交给 `mount_inner`，仅在 `SharedChild::reject` 接受后记录错误。 | 实际身份仍在内核拥有的共享槽位中，普通诊断字符串不是另一份分配权威。受检分配器检查 parent／domain／generation；取消可阻止后续分配。 |
| 外部分配与不可变 owner／generation | `mount_request` 从自身 Episode 创建一个控制器，句柄、pending 请求、逆操作和保留列表均 clone 它。`complete_mount` 只写入一次 `allocation: Option<Result<PluginId, String>>`。 | 移除原先分离的身份 cell 和 `assigned` 标记；外部逆操作的类型不再允许 Native 句柄或缺少控制器。配对依赖普通 Rust 构造与隐私约束，图身份及分配报告真实性仍是宿主前提。 |
| 外部退休与移除 | `request_retirement` 和 `cleanup_failed` 请求退休；分配前拒绝置 `removed`；已成功分配的节点须在图实际移除后调用 `removed()`。重复分配报告被拒绝，首个结果保持不变。 | 请求交出后取消，仍须保存晚到的真实 ID 并等待移除；退休本身不能结束清理。被拒绝的请求没有分配过图节点。所有权不隐式建立服务依赖。 |
| 保留的 Child 清理失败与服务状态 | `cleanup_failed` 保留首个清理错误并报告服务终止失败；`record_error` 记录 setup／应用错误；`mark_initialized`、`complete_mount` 和 `removed` 调用私有服务状态方法。 | Child 逆操作失败后，`removed` 拒绝。这个 sticky 外部 Child 错误没有 reset 接口，与可重试 callback 工厂分开；服务 join 可返回错误而 `finished` 仍为 false。 |
| 外部 notify callback 与 cleanup waiter | 构造时保存 callback；退休 clone，拒绝／移除取走释放；`poll_retired` 替换 waiter；分配、清理失败和移除取走 waiter 并通知。 | Waker 在加锁前 clone，替换的 waker、捕获的 callback 及通知均在锁外析构／调用；服务通知也在 Child 锁外。完成通知可以重入读取原始 Child 句柄。 |
| Episode 的 `ExternalChildren` 保留列表 | 私有插入仅在准入成功后调用；静态取消／清理取快照，drain 和 `child_controls` 仅剪除已移除／被拒绝的控制器，Episode 成功 seal 后取走列表并在锁外析构。 | 列表保留真实控制器及失败，不是另一张图或生命周期权威。更宽的可变 Episode guard 仍须另行收拢。 |

Native 调用链为 `mount_request` → recorded
[`enqueue_native_child`](../crates/cordis-kernel/src/reversible_value/managed/interleaving/history/lifecycle/children.rs)
→ Execution／SetupWork 准入 → `SharedChild`；dispatch 消费原始 work item 并完成其收据。
`mount_inner` 使用 `register_shared_child`，清理 dispatcher 调用
`retire_shared_child` 及运行时退休处理。`terminal_agrees`、
`cancellation_precludes_assignment`、recorded 队列／历史 frame 及 Native 生命周期
合同仍是必要依赖。Native Child 退休不等于移除，实际移除仍经过生命周期和依赖守卫。

外部链路使用 `enqueue_owned_child` 将同一控制器放进请求及逆操作 →
`StaticEpisode::drain_child_requests` → 宿主分配报告 → `StaticCleanupFuture` →
`poll_retired` → 原始恢复票据。
[Node 适配器](../crates/cordis-node/src/typed_children.rs) 在交接时检查原 owner／generation，
报告分配／应用／清理观察；[`forget_typed`](../crates/cordis-node/src/typed.rs) 报告移除。
嵌入宿主必须提供真实的图观察；队列收据证明消费了哪项工作／逆操作，不证明任意外部
报告的真实性。两条路径都没有给纯 Rust 引入 Node 依赖。

维护改进是调用方无需再配对身份／控制器，并移除类型上已不可表达的“外部逆操作缺少
控制器”回退分支。内核合同、公开 API 及调度／失败策略保留。既有 Native Child、
静态宿主及 Node 动态 Child 回归继续运行；静态宿主分配回归还检查晚到／重复报告、
原始句柄及通知重入。本次重构不关闭任何论文义务。

## Episode 通知与 root 进度

[`runtime/episode.rs`](../crates/cordis/src/runtime/episode.rs) 现在私有管理能力及通知字段；
[`runtime/root.rs`](../crates/cordis/src/runtime/root.rs) 将真实 root Future 与工作票据
放在同一所有者中；[`static_host/progress.rs`](../crates/cordis/src/runtime/static_host/progress.rs)
管理外部 setup／cleanup 交接。这些普通 Rust 所有者调用已有受检执行，不另建生命周期权限。

| 状态／所有者 | 本范围修改入口 | 合同或宿主边界 |
| --- | --- | --- |
| Episode 宿主能力与保留的不支持请求 | `for_native`／`for_external` 设置宿主模式与可选 callback；`require_feature` 接受类型化 `Feature`，保留首个不支持请求；`reject_child_batch` 保持原有批次错误优先级。`seal_external` 成功后取走 callback 用于释放。 | 各宿主仍支持原有操作；`check_service_update` 保留服务更新的阶段检查。不可变元数据不代表撤回后仍有写权限。 |
| Episode driver 与选定通知 | 除成功外部 seal 外，构造后的修改仅经 `replace_driver`、`take_driver`、`service_notification`、`child_notification`；setup、service、Child、poll 和 cleanup 调用这些方法。 | 调用方在加锁前 clone waker，解锁后析构被替换者。共享 `Notification` 在锁外先 callback 后 driver，Drop 不调用 callback。共用通知载体不合并 effect／service／宿主策略。 |
| 外部关闭资源 | `seal_external` 先调用受检执行守卫，成功后把 values、driver、callback 和保留的 Child 列表移入 `ClosedEpisode`，解锁后调用 `release_notifications`。Native `poll_settle` 仅在 `release_controlled` 成功后取走 driver。 | 外部释放顺序仍是 driver、callback／Child、完成记录、values。seal 失败不移出资源；Native 释放仍须满足受检工作／清理／依赖守卫。 |
| Root Future 与原始工作票据 | 私有 `RootState` 由 `initialize_callback`／`initialize_reply` 构造，`RootSetup::poll` 拥有全部 queued／running 转换；Native 和静态调用方不能自行拼接或拆开 pending 配对。 | `issue_root`、`start_root`、`cancel_queued_root`、`complete_root`、`fail_root` 仍操作真实工作／收据。撤回可丢弃尚未轮询的 root；已开始的 root 继续保留至落地。 |
| 静态 setup 完成与放弃 | `setup_landed` 记录结果落地；未完成 setup 析构时先取消，再调用受检 `abandon_root`，最后由 `abandon_setup` 记录 sticky 错误。 | `start_cleanup` 要求 setup 已落地并拒绝放弃状态。丢弃 Future 不能证明恢复完成；没有新增调度或终止定理。 |
| 静态 cleanup 运行状态与保留错误 | `start_cleanup` 保持守卫／错误优先级，先完成受检 retry 再取走旧错误；`cleanup_succeeded` 清除运行标记；`cleanup_failed` 保留新错误并返回被替换者。 | 组合锁顺序为 Episode → progress，没有反向获取；不透明错误返回到两层锁外析构。已消费失败、可重试工厂与 sticky Child 失败仍各用原有策略。 |

证明路径仍为 [`Execution`](../crates/cordis-kernel/src/execution.rs) 的实际工作／关闭
守卫、recorded 生命周期／工作历史和已有 Native 释放合同。Future 轮询、callback
真实性及析构行为仍属宿主边界。较宽 guard 仍向 runtime 模块开放 values、清理
派发和 Child 列表接口，本批不是 Episode 的完整封装或新的论文证明。

审查同时发现并修复两处实际所有权问题：

- 关闭的 Native Episode 可能通过逃逸的 setup context 保留 driver。
  [`runtime_waiters`](../crates/cordis/tests/runtime_waiters.rs) 中的
  `closed_native_episode_releases_driver_even_when_context_escapes` 检查真实 pending
  清理在受检关闭后释放该引用。
- 静态 setup 的 sticky 不支持功能错误可能在 Episode 锁内替换并析构不透明插件错误。
  现在被替换结果先移出锁再析构；私有 Episode 旁的
  `setup_override_drops_application_error_outside_episode_lock` 检查真实错误析构时的
  锁访问，同时保留诊断与后续清理行为。

临时恢复旧行为时，两项回归均拒绝。这是运行回归，不是 Verus 负控；最终源码的
集成结果见[开发记录](development-report.json)。Root 取消、pending 工作、清理重试
和放弃状态仍由既有回归覆盖。

## Native 决策与控制所有权

生产审查路径为 [`Runtime::poll_settle`](../crates/cordis/src/runtime/poll.rs) →
[`runtime/control.rs`](../crates/cordis/src/runtime/control.rs) →
[`NativeDriver`](../crates/cordis-driver/src/shared/native.rs) → 已有
[`NativeRuntime`](../crates/cordis-kernel/src/lifecycle_state/native/runtime.rs)、
[`PollControl`](../crates/cordis-kernel/src/poll_control.rs) 及记录型执行合同。
`Decision` 是根据观察得到的候选动作，不是状态修改权限。

| 状态或观察 | 所有者、修改入口与实际用途 | 必须区分的含义 |
| --- | --- | --- |
| 阶段、退休、target、committed bindings 与清理准入 | Kernel／LifecycleState 仍是权威，`NativeRuntime` 记录实际转换；共享 `decision`／`coherent` 读取它们，受检 begin／withdraw／cleanup／release／remove 入口实施表示出来的守卫。 | target 与 committed 不同可以是合法过渡；调度撤回不等于不变量被破坏。Child 所有权不能授权释放 provider。 |
| 轮询 owner、Episode／work 身份、setup 错误、cleanup 错误与 restart | `PollControl` 拥有状态；`poll_control` 构造，失败记录保留首个载荷，`request_restart` 及 controlled Begin／retry／release 执行重置或绑定。`poll_flags` 从 setup **或** cleanup 错误派生失败。 | Restart 清除 setup 失败，不清除保留的 cleanup 失败；retry 需要真实失败执行／收据。拒绝路径保留原合同，不把复制的 bool 变成第二份权威。 |
| 生产宿主持有的原始控制对象 | `runtime/control.rs` 的私有 `Control` 只允许只读访问及记录失败，不暴露可变控制对象；实际注册后，`bind_control` 从本 Runtime 的 Driver 获取它；`with_control` 统一 Begin、重试、释放和重启的借出／归还。 | 派发前检查 owner ID；成功／错误处理与载荷析构之前，把同一个对象归还原槽位。这是普通 Rust 所有权，不新增受检 owner 内部 panic 的恢复保证。 |
| Native 可用性与决策 | `NativeDriver::observe_decision` 在原有 Native 观察时机调用谓词，再经过 `decision_with_control` 和共享 `decision`；`Runtime::services_available` 解析实际 target 槽位、anchor 身份、context 与注入配置。 | Loading／Active 仅在 coherent 时检查；Inactive 仅在未退休且无 setup 失败时检查；其他阶段不调用。没有缓存结果，用户谓词的真实性和副作用仍是宿主前提。 |
| Node 与独立 Driver 观察 | Node 提供 sealed／ready／failure／restart 观察；独立 `LifecycleDriver` 也接受 `HostStatus`，并从受检账本派生当前票据。 | Node 就绪状态不同于同步 Native 用户谓词，不合并这些策略或 action／restore ledger。票据视图仍是观察，完成权限由受检 ledger 判断；更广的公开 API／缓存审计仍开放。 |

`poll_control` 现在直接保留 Native 成员的真实 `Arc<AllocationIdentity>`，替换原先
单独的 ghost Native key；增强的 `wf`、`binding_identity` 与
`binding_correspondence` 将它连接到 `bound(native)` 要求的精确 Journal／key 对。
`NativeRuntime::poll_control_identity` 借用原始成员分配，并给出对应合同。

`NativeDriver::owns_poll_control` 用 `Arc::ptr_eq` 比较这两个借用的分配；所有接收
控制对象的 Driver 入口都会先检查：两种决策、重启、Begin、原始／记录型重试与
释放，以及受控／带作用域的服务和载荷快照。拒绝在谓词执行、失败载荷提取或生命
周期修改之前返回 `None`／`InvalidState`；`rejected_release` 不产生 Unload 收据或
终止队列证据。工厂只克隆一次既有分配，反复检查不增加 Journal 锁、编号分配或
Arc 克隆；比较也不依赖数字名称，因此编号发行器耗尽时仍可检查。旧控制对象保留
Arc 期间，该分配不能被复用。

**身份含义由 Verus 验证；`Arc::ptr_eq` 及普通 Driver 调用者仍是 Rust／标准库边界。**
这里增加的是控制来源的可执行检查，并非整个适配器的 Verus 证明；原始
`NativeRuntime` API 仍保留 `bound` 前提。身份相同不代表仍注册、属于当前 Episode、
清理就绪，也不证明另行传入的 execution／configuration／scope 的来源；对应合同
与守卫仍须成立。其他公开 API 前提继续保留；当前票据观察见下文独立审计。

此前四个 Runtime 入口分别借出／归还原始可选控制对象，Native 观察条件与宿主值
查找放在一起；现在控制模块拥有这些修改入口，Driver 拥有观察策略。失败载荷仍在
Episode／Journal 锁外析构；重试先归还控制对象，再取出旧错误与 waker。既有转换
守卫、错误／结果合同、公开 Runtime API 及 Node 策略保留；控制表示新增上述受验证
Native 身份，Driver 入口由真实 Runtime 使用。

[服务行为回归](../crates/cordis/tests/service_parity.rs)
`failed_and_retired_consumers_do_not_recheck_user_predicates` 使用真实失败 consumer，
检查重复 settle／诊断、显式重启和移除，并能拒绝把新入口改为提前调用谓词的变异。
既有 [`retry_cleanup`](../crates/cordis/tests/retry_cleanup.rs)、
[`update_recovery`](../crates/cordis/tests/update_recovery.rs) 和
[`shared_lifecycle`](../crates/cordis-driver/tests/shared_lifecycle.rs) 继续覆盖失败保留、
绑定替换、consumer 保护和旧票据。运行回归不证明任意谓词或调度推进；最终集成结果
见[开发记录](development-report.json)。

[控制所有权回归](../crates/cordis-driver/src/shared/native/control_tests.rs) 刻意让两个
真实 Native owner 使用完全相同的 domain、插件、generation 和 work 数字，检查
回调前拒绝观察、原失败载荷保留、原始／记录型失败清理与本地成功重试／释放、
三种含控制对象的快照，以及原 owner 销毁后创建替代 Runtime。移除身份守卫会让
三项测试全部失败。另一项可编译变异把工厂身份改为 control 成员而非 Native 成员，
由 Verus 工厂后置条件拒绝。这些是定向证伪检查，不替代独立的完整负控套件。

## 执行、配置与作用域来源

Native Driver 在进入内核前检查另行传入的所有者。这些是实际生产入口的检查，
通过受验证的身份 getter 和工厂连接到现有合同，不改变论文生命周期转换的含义。

| 对象 | 实际权威与检查 | 拒绝行为及剩余边界 |
| --- | --- | --- |
| 原始／记录型执行 | `Execution::execution_domain` 借用清理所有者的真实 Journal；`NativeRuntime::execution_domain` 借用 Native 成员的 Journal。`owns_execution` 比较实际分配，并检查已有的当前 Episode 选择条件。 | 所有接收 execution／recorded owner 的 Driver 入口，都在 root 准入／派发、publication、撤回、settle／失败／重试、释放及联合观察前检查。消费型 API 在拒绝时归还原参数／owner，不生成成功释放收据；阶段与就绪守卫继续生效。 |
| 记录型配置 | `Recorded::execution_domain` 通过 `domain_ref` 到达实际历史 ledger；`owns_configuration` 与 Native Journal 比较。 | `NativeDriver::configuration_snapshot` 在联合读取前对外来 Journal 返回 `None`；通过同一 Journal 的 clone 直接构造也可接受。Loader 私有持有两个所有者，保留上层不可失败快照 API，并在受检返回处断言该私有关联。配置 target 与 adoption 使用下文说明的额外 Native 分配检查。 |
| root／effect 作用域 | `scope_for_group` 保留真实活队列的 `Arc<AllocationIdentity>`，工厂合同为已接入执行证明 `linked_to(execution)`；精确 clone 合同保持同一绑定。`owns_setup_scope` 同时检查执行来源、数字选择条件和原队列分配。 | 两种带作用域的服务／载荷快照拒绝外来或已移除的队列。`SetupScope` 改为显式 clone 的句柄，不保留队列载荷或 Journal。`belongs` 与原始 `EffectRun::call_scoped` 仍描述数字选择；独立／静态 scope 没有 Journal 分配，不能据此宣称一般来源真实性。 |

[`Journal::runtime_identity`](../crates/cordis-kernel/src/reversible_value/joint.rs)
借用既有锁分配外的不可展开句柄，不暴露锁或修改权限；`identity_correspondence`
把该身份连接到精确 Journal 相等。每个 Journal 没有新增独立分配或计数器，反复
检查不加锁或克隆 Journal；已接入的 scope 在签发或显式 clone 时克隆队列身份。

**Verus 验证身份的含义和 Scope 工厂；`Arc::ptr_eq` 与普通 Driver 仍属于
Rust／标准库边界。** 原始 `NativeRuntime` 快照 API 保留 Journal 前提。调用票据、
配置 target／adoption 见下文；Child 票据及早期恢复快照仍有各自合同和审查工作。本批不证明任意 callback、全部宿主输入、调度推进或新的一般论文义务。

[五项来源回归](../crates/cordis-driver/src/shared/native/provenance_tests.rs)刻意复用
domain／Episode／work 编号、相同配置内容，以及真实失败／清理就绪 owner；检查
root 参数未被消费、失败保留、两边都可释放时仍拒绝错误 owner、各类作用域快照、
typed root、本地成功、Journal clone，以及原运行时销毁后的替代实例。Journal 的
弱引用还检查了逃逸 scope 不会保留原域。[共享测试辅助模块](../crates/cordis-driver/src/shared/native/test_support.rs)
复用前一批控制回归的编号碰撞 fixture。

定向证伪将 `scope_for_group` 的绑定替换为 `None`：代码能编译，但 Verus 拒绝工厂
后置条件；令 `same_journal` 恒真会使五项回归全部失败；单独绕过队列指针比较会使
scope 回归失败。这些不等于全量负控；最终源码与开发验收见[开发记录](development-report.json)。

## 当前动作票据观察

动作账本是未完成票据的唯一所有者。`LifecycleDriver` 现在和 Native、Node Driver
一样，从 `LifecycleState::pending` 按需生成 `pending_action`。删除了独立的
`pending_views` 表以及八处插入、八处移除；以后新增生命周期入口，无需再同步
第二份当前票据状态。

| 状态／观察 | 权威所有者与实际入口族 | 审查结论 |
| --- | --- | --- |
| 当前动作 | `ActionLedger` 拥有 domain、单调 action 计数器及精确 pending 记录；普通 Begin、受检准入、原始／Native Begin、清理请求和重试通过受检协议签发。 | `pending` 返回当前唯一票据或其缺失。在 `wf` 下，`out == Some(ticket)` 与该 owner 的记录成员关系等价；合同贯通 `LifecycleActions` 和 `LifecycleState`。 |
| 完成与失败 | setup 结清、`complete_action`、`complete_cleanup`、原始／Native Finish、失败和释放继续调用原所有者；`pending_matches` 使用加强后的读取合同。 | 撤回／退休保留在途票据；合法确认消费票据，旧／外来回复被拒绝后保留当前票据。失败的 Finish 可能先结清 setup 再拒绝激活，不能把返回错误一概解释成票据仍存在。 |
| 清理收据与资源释放 | `LifecycleActions` 独立保留失败／成功／已排空收据；Release 和 Remove 保留原有守卫。 | pending 为空**不等于允许释放**：失败清理虽已收到回复，仍阻塞释放，必须成功完成新一轮重试。 |
| 宿主线格式值 | `pending_action` 返回自有 `ActionTicket`；`host_ticket`／`kernel_ticket` 转换五个字段，serde 编解码传输表示。 | 保留或修改旧值不会修改账本，回复仍经受检协议重新验证。转换、序列化和普通 Driver 接线继续属于 Rust 边界，由运行回归检查。 |

低层 `LifecycleDriver::pending_action` 从 `Option<&ActionTicket>` 改为
`Option<ActionTicket>`，与另外两个 Driver 一致。移除表分配及写入同步后，独立
Driver 的查询从树查找变成现有账本的线性扫描；Native／Node 原本已使用该扫描。
这是维护成本改进，不是吞吐量测量结论；没有新增缓存、索引、crate 或运行依赖。

[四项实际路径回归](../crates/cordis-driver/tests/pending_actions.rs)覆盖原始执行的
失败／重试／释放／新代次、setup 结清后失败的 Finish、Native 发布／释放，以及
受检准入后的资源释放；核对实际 owner／admission 票据、精确线格式字段、保留的
旧视图、被拒绝调用和不相关 owner 的在途票据。既有清理结果、资源和共享生命周期
测试保留原断言。定向负控要求省略当前票据的内核仍能编译，但被 `pending` 的精确
后置条件拒绝；适配层隐藏全部当前票据时，四项新回归均拒绝该实现。这不等于全量负控。

本批把旧回复保证连接到当前观察，不改变论文生命周期规则或关闭一般论文义务。
调用、配置／adoption 和 Child 来源在下文审查；历史恢复输入仍单独审查。最终验收绑定
[开发记录](development-report.json)。

## 源码组织及依赖方向

| 区域 | 所有权／用途 | 审查分类 |
| --- | --- | --- |
| [`lifecycle_state/`](../crates/cordis-kernel/src/lifecycle_state/)、[`lifecycle_actions/`](../crates/cordis-kernel/src/lifecycle_actions/)、动作／清理 ledger | 共享生命周期权限和旧 provider 保护 | 生产状态、附着合同及轨迹组合 |
| [`reversible_value/`](../crates/cordis-kernel/src/reversible_value/)、[`cleanup_queue/`](../crates/cordis-kernel/src/cleanup_queue/)、[`cleanup_groups/`](../crates/cordis-kernel/src/cleanup_groups/) | 受管操作、保留逆操作、实际执行来源和历史 | 生产 primitive 及解释／迁移证明，一般性边界保持明确 |
| [`lifecycle_state/native/`](../crates/cordis-kernel/src/lifecycle_state/native/)、[`node_runtime/`](../crates/cordis-kernel/src/node_runtime/) | 各自建立共享协议前提的 Native／Node 状态所有者 | 生产连接；Node 记录 publication／句柄／scope，不证明 JS 对象内部 |
| [`refinement.rs`](../crates/cordis-kernel/src/refinement.rs)、[`dependent_grammar.rs`](../crates/cordis-kernel/src/dependent_grammar.rs)、grammar／history／recovery 及 [`mixed_driver/`](../crates/cordis-kernel/src/mixed_driver/) | 论文语义、条件定理、参考执行器及实际历史连接 | 规格与证明支持，包含可执行研究 driver；被擦除或没有宿主调用者不代表冗余 |
| [`paper_counterexamples.rs`](../crates/cordis-kernel/src/paper_counterexamples.rs)、恢复／mixed 示例、定向负控和冻结报告 | 反例、修订解释、准入示例和证伪 | 保留的研究证据，导航单列，活跃验证目标不变 |
| [`cordis-driver/src/shared/`](../crates/cordis-driver/src/shared/)、[`node.rs`](../crates/cordis-driver/src/node.rs) | 共享调度策略、命令解析和宿主适配 | 普通 Rust 连接，不自动成为已证明的调度器 |
| [`runtime/setup.rs`](../crates/cordis/src/runtime/setup.rs)、[`services.rs`](../crates/cordis/src/runtime/services.rs)、[`cleanup.rs`](../crates/cordis/src/runtime/cleanup.rs)、[`poll.rs`](../crates/cordis/src/runtime/poll.rs) | Episode API、服务句柄、清理 dispatch 和协作轮询；callback 尝试封装在 [`cleanup/attempt.rs`](../crates/cordis/src/runtime/cleanup/attempt.rs) | 普通宿主；Episode 关联及句柄现位于 `runtime/episode.rs` 和 `runtime/effect_handle.rs`，Child 准入及外部控制器位于 `runtime/child.rs` 和 `runtime/child/external.rs`；root Future／票据位于 `runtime/root.rs`，静态交接状态位于 `runtime/static_host/progress.rs`；Native 控制绑定／借出及重置入口位于 `runtime/control.rs`；其他生命周期入口仍在 [`runtime.rs`](../crates/cordis/src/runtime.rs) |
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
| 分散在 setup／静态宿主的身份与控制器配对 | Child 准入拥有请求／句柄／逆操作构造，一个私有外部分配状态替换重复身份 cell 和 assigned 标记 | 原句柄／重复回复／通知重入回归、既有 Child 案例及最终开发验收；外部图真实性仍是宿主前提 |
| 分散的 Episode 能力／通知字段及 root／进度修改 | Episode 私有方法、root 票据／Future 配对与静态进度所有者；比较 callback 顺序和 Drop 行为后共用通知载体 | 既有取消／重试／放弃回归，加两项能拒绝旧引用保留及锁内错误析构的回归；公开 API 和受检合同保留 |
| 四份 Native 控制借出／归还及宿主内观察条件 | 私有控制所有者和统一转换辅助方法；Native 惰性观察策略归 Driver，接入实际 Runtime | 保留受检调用／错误处理；真实失败／重启／退休 consumer 回归拒绝提前观察变异；低层工厂关联前提仍明确保留 |
| 重复入口清单 | 按任务组织文档首页、当前审查地图及单一 campaign CLI | 链接、源码绑定和中英入口 |
| 一般模型、条件恢复分支、独有失败与冻结报告 | 研究导航中保留，继续使用原有验证目标 | 移文件不关闭义务，历史通过保持原始源码绑定 |

固定归档为 `codex/archive-before-refactor-2026-10-24`（`60bdd89`）；第二批整理前的
布局也保存在 `c47d111`。不改写历史或上游锁。本轮**没有批准删除独有语义成果**。
进一步删除须比较前提／结果、调用方、证明依赖与独有反例；存在归档本身不是删除
当前对外保证所依赖定理的理由。

## 调用与配置目标的来源

实际调用路径是 `Runtime::start`／recorded root admission →
[NativeDriver](../crates/cordis-driver/src/shared/native.rs) →
[NativeRuntime::admit_managed_root](../crates/cordis-kernel/src/lifecycle_state/native/runtime.rs)。
Loader 从同一个 Driver 获取配置目标，再交给预检和批量接纳。
两条路径都不能仅凭 domain、插件、代次及 revision 数字相等认定 Native 所有权。

| 状态／所有者 | 构造与实际检查 | 保留的边界 |
| --- | --- | --- |
| `RegisteredInvocation` | 私有 `bind_native` 保留真实 Native 分配，同时保持参数、work／生命周期票据、所有者及 recipe 版本。Native 和 recorded admission 证明 `bound_to(control_address())`；`owns_invocation` 在 `call_root` 和 `call_opaque_root` 执行回调前检查。 | 通用 `LifecycleState` 签发的票据不绑定 Native，仍可走原有独立路径。内核继续检查所有者、当前 Episode、Loading 状态及版本；来源真实不代表票据仍有效。 |
| 配置 `Target` | 实际工厂证明数字有效性与精确 Native 绑定；经过验证的 `Clone` 同时保留两者。Driver 在查询及替换前检查分配。两种操作都借用目标，不刷新版本或复制 Arc。 | 原始内核 freshness 有意保留数字谓词；Driver 的分配比较是额外的普通 Rust 守卫。历史 `Allocation` 证据不因此成为当前目标权限。 |
| 拥有载荷的配置批次 | Driver 复用完整的已验证预检，在其首个失败之前或同一位置合入最早的外来目标。同一位置的外来目标优先于重复／容量错误。任何拒绝都在替换和 metadata 回调前返回完整输入。 | 成功后进入已有已验证 adoption 循环，并再次预检；增加一次只读遍历，不复制策略实现。任意 metadata 回调仍保留原有合同／panic 边界；预检原子性不代表回调异常可自动回滚。 |

身份复用已有 `Arc<AllocationIdentity>`，不增加身份表、逐票据堆分配或计数器。
票据不保留 Journal、Native 宿主或 recipe 载荷；调用参数仍遵循其拥有关系。
配置目标需要额外句柄时显式克隆，不再实现 `Copy`、`Debug` 或相等比较 trait。

Verus 检查精确的工厂／克隆含义，以及已有版本、生命周期、整批预检合同。
`Arc::ptr_eq`、适配层守卫执行和不透明回调仍属于普通 Rust／标准库边界。
这是一项支持生命周期模型的实现身份机制，不是新增论文定理，也不关闭一般义务。

[七项回归](../crates/cordis-driver/src/shared/native/authority_tests.rs) 刻意复用全部数字选择器，
覆盖两种回调、独立路径、参数／recipe／metadata 保留、批次错误顺序与成功接纳，
并用弱引用确认宿主销毁后的 Journal 释放。原有内核测试保留激活、版本、撤销和重启检查。
局部负控把真实工厂绑定到错误 recipe 分配，或删除数字有效性比较；要求新鲜正例通过、
变异代码可编译、且只在指定合同失败。适配层另做守卫变异。
最终集成证据见[开发记录](development-report.json)，不代表完整负控套件或整篇论文验收。

## Child 请求与清理来源

动态 `Setup::mount` 沿真实 recorded
[`enqueue_native_child`](../crates/cordis-kernel/src/reversible_value/managed/interleaving/history/lifecycle/children.rs)
→ Execution → SetupWork → `SharedChild::from_work` 创建对象。请求、返回句柄和
逆操作共享同一个决策槽位。工厂现在保留创建 work 的实际 Journal，精确合同经两层
包装传播；原有请求／逆操作原子创建和父插件／Episode 合同继续成立。

直接 `Runtime::mount(..., Some(parent), ...)` 经 Driver 调用
[`NativeRuntime::registered_child`](../crates/cordis-kernel/src/lifecycle_state/registration/shared_child.rs)。
工厂读取实际注册，绑定 Native Journal 并产生经过证明的分配快照。Begin 前由
`Mounted::owned` 保留同一个 `SharedChild`；父插件已启动时直接放入其清理队列。
`Runtime::start` 转交保留对象，不再根据数字身份重新构造清理权限。

| 检查／所有者 | 保证及保留前提 |
| --- | --- |
| `SetupWork::execution_domain`、Child 工厂及 `Clone` | 精确合同确认保留的 Journal 和共享决策；原始未关联 work 与 `SharedChild::from_identity` 仍不绑定来源。 |
| `NativeDriver::owns_shared_child` | 注册／退休前比较保留的 Journal 与当前 Native 所有者的分配。外来或未绑定请求不能修改槽位或接收方；拒绝注册返回原定义和宿主载荷。指针比较及包装逻辑属于普通 Rust 边界。 |
| 内核共享槽位转换 | 仍检查数字 domain、父插件、Episode、阶段和终态。已取消请求不能再分配；Journal 相同不代表任意同 Journal 重构安全，也不赋予新 Episode 权限。 |
| Runtime 清理 → 退休 → 受守卫 Unload／移除 | 实际逆操作将保留的 Child 交给 Driver。局部分配见证不证明生命周期完成；退休项仍须通过清理与依赖守卫才能移除。所有权不是服务依赖。 |

该绑定保留 Journal 元数据直到最后一个 Child 克隆被销毁，不通过这一关联保留
Native recipe 或宿主载荷。创建及克隆各增加一次 Journal Arc 克隆，不增加身份表、
计数器或逐句柄 Journal 分配。原始 `ChildIdentity` 仍为 `Copy`；直接使用
`NativeHost` 的调用者继续承担既有来源前提。传给 `NativeDriver` 的 Child 应来自
Native 工厂或真实 enqueue 返回值。

[七项 Driver 回归](../crates/cordis-driver/src/shared/native/child_tests.rs) 覆盖数字选择器碰撞、
原始载荷、取消／重启、recorded 请求／逆操作共享、本地成功／幂等及元数据寿命。
[真实 Runtime 回归](../crates/cordis/tests/runtime.rs) 覆盖激活前后挂载和最终注册表移除。
局部证明负控分别移除两个工厂的 Journal，要求新鲜匹配正例、完整变异编译及精确
合同失败；运行负控分别绕过 Driver 守卫、恢复按数字身份重构清理，均被行为回归拒绝。
全量负控套件单独运行。

这是支持定义 52／54 的实现来源机制，不是一般 Child 恢复定理。Native 历史快照来源
在下文审查；一般恢复、任意回调及全局推进仍保留各自义务。最终集成结果绑定[开发记录](development-report.json)。

## Native 历史快照

[`shared/native/snapshots.rs`](../crates/cordis-driver/src/shared/native/snapshots.rs)
集中 Driver 原有的 13 个观察入口及来源检查，保留转发守卫和服务／payload 的单次
读取观察；生命周期修改和回调派发继续由 Native Driver 所有者负责。

| 所有者／路径 | 合同与保留边界 |
| --- | --- |
| Native [`history::Snapshot`](../crates/cordis-kernel/src/lifecycle_state/native/runtime/history.rs) | 私有构造器同时保留实际 Native 分配和 Journal。`certified` 把分配连接到 Journal 及 Native key；`native_identity` 返回精确借用来源。publication、Episode、slot、payload、配置工厂均传入真实所有者的分配，typed 历史仍被擦除。 |
| 配置观察 | `native_snapshot` 借用同一配置／来源截面中的 Native 部分，不复制历史或刷新旧观察。 |
| Driver `recovery_snapshot(&native_cut)` | `owns_snapshot` 在进入内核前比较保留的 Native 分配。外来快照返回 `None`；本地旧快照可跨后续发布、失败清理、重试、Unload 及新 Episode 使用。指针比较属于普通 Rust／标准库边界。 |
| 内核 `recovery_snapshot_from` → 原始 `recovery_snapshot` | typed 快照不变式提供 Native 记录前提。共享的 `Capture::describes` 保留精确早期截面、有序扩展、标准化区间和条件恢复／阻断结论。原始 API 为使用内部截面的证明调用者保留同 Journal／Native 记录前提。 |
| 观察与修改 | `Some(Capture)` 表示来源被接纳，内部 `Ghost` issue 不是运行时清理成功标志。快照不能代替当前调用、执行、重试票据或释放守卫；捕获不会恢复数据或消费清理。 |

普通 Driver API 改为接收 `&history::Snapshot<V>` 并返回 `Option`，适用于一般 Native
值，不再限定受管槽位。输入来自真实 `publication_snapshot()` 或配置快照的 Native
借用。原始 `joint::Snapshot` 不建立该入口所需的 Native 记录前提。`into_joint` 有意
丢弃 Native 关联；`joint().refresh()` 只刷新原始 Journal 观察，不刷新 typed Native 历史。

每个 Native 快照增加一次已有 Native 分配 Arc 的克隆，不增加身份表、计数器、
Journal 锁或运行时历史。快照保留 Journal／身份元数据，擦除的历史不保留 recipe、
宿主或发布载荷。投影成 `joint::Snapshot` 时释放额外身份引用，留下的 Journal
仍遵循其原有元数据寿命。

[五项回归](../crates/cordis-driver/src/shared/native/snapshot_tests.rs) 覆盖相同数字选择器、
真实失败／重试／重启、借用配置截面、八条实际工厂路径，以及载荷／元数据销毁。
局部证明负控替换为 recipe 分配或丢弃早期截面；要求匹配正例、完整变异编译和精确
合同拒绝。普通守卫绕过／全部拒绝负控同时检查拒绝与有效准入，不等于全量负控。

本批关闭所选 Native 观察输入的来源关联，不关闭一般源／目标堆恢复、语义独立性、
Node 历史或宿主活性。当前集成结果见[开发记录](development-report.json)。

## Node publication 命令的所有权

[`Driver::set`、`revoke`、`reclaim`](../crates/cordis-driver/src/services.rs)
现调用已验证的 [`NodeRuntime` 服务操作](../crates/cordis-kernel/src/node_runtime/services.rs)。
原普通 Rust `owned_publication` 判断和 `NodeDriver::replace_value` 转发层已移除。
service 模块仍是同一状态所有者的实现，不新增 publication 表、权限缓存或运行时历史。
`publish`、`resolve` 及服务错误转换也集中到 Driver 的 service 模块；公开方法名、
协议结果和错误优先级保持不变。

| 权威状态／实际入口 | 检查、修改与证明依赖 |
| --- | --- |
| publication owner／generation 与当前 Kernel generation | 私有 `owned_publication` 读取实际 registry 和控制状态。精确的 `ownership` 合同拒绝未知 ID、外来 owner 和旧 episode；即使旧槽位自身的 owner／generation 仍匹配，也必须检查当前代次。拒绝保留原观察与历史。 |
| 载荷、revision 与被替换的句柄 | `replace_service` 经 `check_replacement`、`replace_admitted` 调用原有 `replace`／`PublicationStore::replace_checked`。先检查准入，再检查归属和可见性。`service_replaced` 对应真实 Replace 事件及结果；原有句柄交付合同保留被替换的引用。 |
| 可见性与清理查询选择 | `revoke_service` → `revoke`／`revoke_with_restoring`／`forget_restoring`。要求当前归属，但退休／恢复阶段本身不禁止清理；撤销保持幂等，不释放 consumer lease。`service_revoked` 对应精确的实际调用记录。 |
| 保留载荷、checked 标记与动态声明 | `reclaim_service` 检查当前归属；已回收槽位返回 true，保留槽位调用实际 `reclaim`。活 lease 返回 false；只有真实回收成功才清除 checked 标记并执行完整 `reconcile_declarations` 遍历。`service_reclaimed`／`reclaim_tail` 通过 `batch_result` 组合真实历史；后续协调错误保留已执行前缀，不宣称事务回滚。 |
| 实际对象表与 Node 状态 | [`Bridge::replace_service`](../crates/cordis-kernel/src/node_runtime/bridge.rs) 在同一次 Node 独占借用内共用 `check_replacement`／`replace_admitted`，在两者之间检查自身 domain 和真实对象 key。Node 对象路径使用的 [`Driver::set_host_object`](../crates/cordis-driver/src/objects.rs) 不再提供独立的归属断言。Bridge 错误保持 Node 状态，成功写入使用真实发行的 key。 |

`interfaces` 保存初始 setup 要求与当前依赖，`dynamic` 保存后续声明的归属。
publication 可见性、被保留的旧槽位、consumer 已承诺的 lease、当前动态声明是不同事实。
服务命令复用这些已有所有者及历史合同。内部 withdrawal、adoption 与清理释放原语
仍有各自用途，不用面向宿主命令的准入规则替换它们。

[内核回归](../crates/cordis-kernel/tests/node_services.rs) 覆盖外来／旧 owner、真实 lease
保留、退休阶段清理及向 prepared successor 转交声明。
[Driver 回归](../crates/cordis-driver/tests/service_ownership.rs) 比较数字句柄与对象表写入、
错误优先级及实际保留的对象。`python3 -B scripts/check-profile-controls.py node-services`
检查两项 canonical 变异：省略 owner 相等检查、省略当前 Kernel generation 检查。
要求新正例、变异完整编译及精确归属后置条件拒绝；`--check` 仅检查锚点。

这些合同覆盖显式表示的 publication 协议。任意 JS 对象内部、callback 效果、FFI 转换、
首次激活编排与整个宿主的恢复仍有独立边界。Rust 应用仍可不使用 Node；本批没有新增
依赖或另一套验收框架。
