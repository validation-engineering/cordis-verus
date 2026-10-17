# R2 生产状态清单

当前 R2 状态以[第 5 包统一验收](r2-acceptance.zh-CN.md)为准：managed-production/v1 范围已完成。下文保留各批次历史记录及其当时的验证范围。

## 历史实施与验证记录

当前生产组合与准确解释边界见[第 4 包](r2-production-composition.zh-CN.md)。下文历史检查点保留原有范围。

[配置解释](r2-configuration-semantics.zh-CN.md)现已将实际模块选择、作用域键归属、schema／默认值规范化、保存合并与回读判断接入验证代码；生产步骤组合见第 4 包，综合验收仍待完成。

[English](r2-state-inventory.md) · [执行合同](r2-execution.zh-CN.md)

[宿主组合包](r2-host-composition.zh-CN.md) 新增真实外部引用所有者、派发 claim、
静态强类型槽组装与共享 Episode 归属检查。下表记录其当前范围；第 3 包已补齐配置值
解释，受验证载体的轨迹组合见第 4 包；普通宿主边界与最终验收仍单独保留。

这是 R2-C/E 的工作清单，沿实际原生 Runtime 盘点共享状态、逃逸的 setup 句柄和清理路径。
**它还不是完整共享状态解释，也不是整个宿主联合生产轨迹的证明。** Node 与 loader 行标出后续
集成面，仍需逐字段进行同样的审查。没有语义解释的字段是开放义务，不能自动视为
“不改变观察的实现细节”。

新增多服务有限函数体在第一次写入前检查全部 Begin 声明，逐条解析实际槽位，并把成功前缀 inverse 保留在真实接收组。`Report::production`、`source_trace`、`failed_trace`、`frame` 连接实际对象状态、有序本地历史和推导出的别名影响范围。计算拒绝另有捕获与收据证据。有别名时的固定端口独立性、任意回调、跨 Journal 全序及静态／Node／配置组合仍是明确边界。

原生可扩展计算现在经过 `native_effect::{Capture, Computation}`：真实声明／owner
捕获、实际输入检查点、锁外计算与验证落地。`value_alias` 提供完整本地标量别名
投影及其带条件的单键特例；任意回调、静态宿主和其他值载体的语义仍未关闭。

## 声明服务调用边界

`value_access::{Read, Write}` 连接真实 Begin 声明、所选槽位、保留的对象分配与标量
读写凭据。原生宿主调用 `observe_reversible`、`apply_native_value` 和
`run_native_value_program`；最后一个入口同时用于已登记有限 root／Child 程序体。
槽位选择凭据先于同域读写，每条程序写入都具有生产对象语义及真实 owned／imported
服务上的帧条件，清理登记指向同一对象和真实 root／effect 组。

声明端口集合与对象读写范围是两层含义。端口层不干扰还需别名闭包，不能由名字不同
推出，也没有被宿主直接假设。原生计算效果现已接入这一声明边界；一般多服务程序体、
不透明载荷与静态宿主关联仍开放。见[合同](r2-execution.zh-CN.md#声明访问与生产函数步骤)。

## 所有者、修改入口与剩余解释

| 实际所有者与字段 | 修改／调用入口 | 已建立合同与剩余工作 |
| --- | --- | --- |
| `NativeRuntime::{host, services, owners, history, positions, joint, recipes}`；`NativeHost::{lifecycle, entries}` | 注册／Child 注册、Begin、根准入／调用、Finish、撤销、重试、Unload、Remove、回调更新 | 已验证成员关系、分配的 episode 身份、publication 与连续控制／槽／owner 联合历史。回调体及不透明 `Mounted` 内部状态尚未进入该历史解释。 |
| `NativeEpisode` 的共享不可变 `NativeContext`（origin／work 域／登记 realm／anchor／声明／绑定）、imports、自有值、关闭状态、擦除的 `Capture`；`NativePublication` 的 origin、槽和相同 capture | `begin_managed_execution`、`Execution::provide`、`finish_managed_execution`、`release_managed_execution` | imports 来自真实 Begin 绑定与已发布槽；Finish／Unload 保持来源。槽内部修改需要自己的语义。 |
| `Execution::{work, groups, values, initialized, effects, checked_out, attempts}` | 根／请求准入与完成、组准入、runner 取出／归还／退休、取消、清理、重试、seal | 一个受验证 owner 绑定未完成工作、全部清理队列、原生值和阶段。不透明 iterator／Future 的函数含义仍待解释，包含被取出执行期间。 |
| `AsyncSetup::{state, scope}`；`SharedEpisode::{generation, context, services, anchor, episode}`；`Episode::{cleanups, values}` | Setup 读取／提供值、克隆／逃逸、嵌套效果／Child、服务替换与轮询 | 同一分配共享不可变元数据和可变 Episode。原生 `services` 与真实 Begin 所有者共享受验证 `NativeContext`，原生效果由内核读取其绑定。realm／anchor 来自同一登记 Begin；受验证 scope 准入／调用与实际检查点连接存活队列。五个生产身份分配器已使用受验证 CAS 分配；每次共享 Episode 锁访问现检查签发的 execution 关联；静态元数据与准确 Arc 槽由 `static_values::from_definition` 共同组装。标准 Arc／Mutex 语义、其余命名空间和外部静态租约真实性仍是边界。 |
| `Episode::{driver, static_only, dynamic_host, external_children, service_updates, unsupported}` | Setup／效果注册、Child 提交、服务通知、静态宿主轮询 | 唤醒属于调度记账，外部 Child 结果与不支持操作标志则影响结果。控制投影中没有这些字段，不等于它们在完整观察中保持不变。 |
| `ServiceSlot::{payload, metadata}`、标量槽位或 `SharedPayload<dyn Any + Send + Sync>`；保留槽的 `ServiceHandle` | `ServiceSlot::{get, accepts, replace}`、`AsyncSetup::{provide, publish, set, refresh}` 及句柄操作 | 受验证共享 owner 绑定真实载荷／版本历史、私有锁与 Journal。真实 Runtime 检查点收集完整已发布／自有／imported 载荷观察，替换保持无关标量／载荷别名。predicate、任意内部状态、一般 inverse 定律及外层 Episode mutex 关联仍待解释。 |
| `ReversibleValue` 私有锁内的真实值／深度及擦除的连续历史；`Inverse` 的真实目标／前态／后态 | 既有 `apply`／`run_value_program`、新增 `prepare_effect`／受管提交、队列 inverse 派发 | 已验证标量写入与严格恢复定义域；后续不匹配状态阻止恢复并保留 inverse。该历史只解释这个值，不覆盖所有服务对象内部状态。 |
| `effect::Prepared::{target, expected, decision, code}` | `ReversibleValue::prepare_effect` → `Execution::apply_prepared_effect` | 释放快照锁后执行真实计算；私有字段将结果／模型绑定到该输入。提交检查当前值／深度及准入，再写入并保留真实 inverse。丢弃准备结果没有受管写入；用户计算内部的任意副作用不在此合同内。 |
| `SharedChild` 的受锁槽、origin、持久终态凭据；请求和 inverse 共享它 | `enqueue_native_child`、`register_shared_child`、`retire_shared_child`、拒绝／快照 | 已验证真实分配身份、请求／inverse 配对和终态一致性。有限登记 Child 已连接其程序体解释；任意 Child 函数与完整 context 仍待组合。 |
| 已登记根回调／版本；`Mounted::{episode, root_setup, root_running}`；`GroupState::{iterator, running, handle}` | `Runtime::{start, drain_requests, poll_groups, poll_cleanup}`、`RootSetup::poll`、完成结果落地 | 已有保存的回调、实际参数、返回 Future 和 poll 结果的来源合同。传递真实载荷不等于证明任意根、iterator、continuation 或外部清理的含义。 |
| `Mounted::{next_config_update, config_update, injection_config, declared_dependencies, declared_injection_config, context, owned, service, name}` | 注册、更新、Begin、Child 归属转移、失败／重试、restart、移除 | 声明／回调身份进入受验证注册；配置回调与其余设置仍控制普通宿主行为。名称用于诊断，真实失败／restart 由下一行受验证所有者持有。 |
| `Mounted::control` 中的 `poll_control::PollControl::{owner, episode, work_domain, failed, cleanup_failure, restart}` | 受守卫 Begin、restart、失败报告、真实 retry／Unload；`poll_flags` 与共同快照 | 保留真实错误载荷与轮询输入；成功 native 操作控制重置入口。同域／成员关联前提及 availability 真实性仍明确保留。 |
| `Execution::statuses` 与受验证 `host_status::Cell`；`HostStatus` 以擦除的线性权限持有错误／终止／Child 载荷；适配层持有 waiter／driver／notify | 唯一状态工厂、所有者选择的初始化／退休、载荷报告及带凭据的观察 | 实际保存的 link 决定 Journal、Begin／work 和 group 归属；普通与观察退休共用先移除后完成协议，拒绝保留归属。这些入口不再需要条件式状态 Journal 前提；整个 Episode 的 Arc／Weak／mutex 关联、调度和回调真实性仍待完成。 |
| 受验证 driver 旁的 `Runtime::{cleanup_errors, maintenance_changes, shutdown_failures}` | 维护、清理报告、shutdown 聚合 | 这些字段报告真实宿主决策。错误聚合可被用户观察，不能假定它与完整 refinement 无关。 |
| Node `Domain`／Fiber、JavaScript 对象／publication 表、lease 与 invocation 句柄；原生 `Driver` 与 addon backend | 发布／替换／读取、异步回调、原生命令结果、清理／重试、动态接口、HMR | 受验证 Node 所有者现已将实际生命周期／publication／版本／lease／检查变化组合到同一历史；受验证 Bridge 现拥有真实 Node-API 弱引用、Fiber 绑定和待处理票据的配方 claim；封闭选择接入 typed 导入。任意 JS 对象／函数内部状态、HMR 模块效果、完整派发／诊断观察及整个步骤解释仍开放。 |
| `Loader::{runtime, root, parent, registry, configuration}`；`Snapshot`、`Transaction`、`UpdateKey`、`SourceTracking` | Apply／recover、include／group、回调更新、文件加载／重载、prepare／commit save | 私有字段与 RuntimeAccess 操作视图保持实际宿主身份；受验证原生构造入口与单次读取快照关联真实原生 member、配置和源。Configuration 拥有实际 Batch 与计划，Reversible 拥有真实正向／逆向 Future。原生 Target 检查域／ID／代次／配方；提交要求更新全部完成，恢复要求 inverse 排空。原生 allocation 快照及结构性正向／恢复阶段已连接；第 3 包已补齐真实模块／作用域绑定、schema／默认值规范化、递归保存合并和完整源回读检查。整棵树到组件及联合生产步骤的组合仍开放（R2-I）。 |
| `Recorded::{inner, ledger, sources, source_ledger}`；实际配置的候选／恢复载荷／Batch 及带类型历史位置 | begin、更新／逆向／结构轮询、commit、恢复、refresh | 与真实 Runtime 共用 Journal；完整投影、原始提交候选与接受来源有证明。回调在锁外执行；源加载／清空／保存历史已在同一 Journal 写入点核对归属配置。第 3 包补上配置值解释，完整生产序列的组合仍待完成。 |

源码入口：[`runtime.rs`](../crates/cordis/src/runtime.rs)、
[`static_host.rs`](../crates/cordis/src/runtime/static_host.rs)、
[`native_runtime.rs`](../crates/cordis-kernel/src/native_runtime.rs)、
[`execution.rs`](../crates/cordis-kernel/src/execution.rs)、
[`scalar_effect.rs`](../crates/cordis-kernel/src/scalar_effect.rs)、
[`Node runtime`](../packages/compat-cordis/runtime.js)、
[`loader.rs`](../crates/cordis/src/loader.rs)。

共享句柄状态的连接详见[执行合同](r2-execution.zh-CN.md#真实共享句柄状态接入执行轨迹)。
真实失败／restart 字段现由 `poll_control::PollControl` 持有，通过受验证 native
Begin／retry／Unload 入口重置并进入共同快照。原生句柄携带 Begin／work 来源，宿主
在轮询副作用之前核对准确 Weak Episode 分配。剩余关联边界是普通 `Arc`／`Weak`
比较、其余身份命名空间及静态嵌入输入，不能声称数字域足以认证任意共享对象。
参见[上下文／scope 合同](r2-execution.zh-CN.md#注册-realm-与回调作用域)及
[Episode／控制合同](r2-execution.zh-CN.md#episode-归属与真实轮询控制)。

## 新接入受验证所有者的 Node 与配置状态

| 实际字段 | 修改入口 | 合同／剩余边界 |
| --- | --- | --- |
| `PublicationStore::{registry, payloads, revisions}` | 发布／替换／撤销、租用／释放／回收、清理 | 实际载荷和替换版本与 publication 及保留的 lease 对应。 |
| `availability::Availability::{domain, records, pending, next_action, notification}` | request／current／complete／notify／remove_consumer | 实际生命周期／域／依赖／provider／publication／版本检查，完整票据匹配和一次确认；predicate 真实性为外部输入。 |
| `NodeRuntime::checked` 与适配层 `availability.errors` | checked 登记／撤销、诊断回复 | 选择检查与报告错误；没有另一份版本计数，诊断不授权准入。 |
| `NodeRuntime::{admissions, episodes}`；实际 `Admission`、`Episode` 标志与错误载荷 | Begin、prepare／seal／fail／restart、实际完成、清理／重试／释放／移除 | 同一连续协议历史证明真实 Begin 来源与成功释放前保留；旧回复保持状态及资源。待处理票据直接读取 action ledger。 |
| `NodeRuntime::{scopes, restoring}` 及从 registry 构造的 publication 清单 | BeginScope／FinishScope／ScopesLive／CheckScopeWait、捕获／revoke／reclaim 与受管释放 | 同一历史约束真实回调 receipt、当前等待图和撤回回读选择；释放清单来自真实 registry，publication／scope 来源及 scope 身份不复用具有有限历史证明。 |
| `NodeRuntime::released` | 成功替换／reclaim／释放，Drive 回复前的 `drain_released` | 真实载荷候选及有序筛选进入同一历史；检查写入／释放来源、完整入队与排除保留槽位。Bridge 移除现先检查真实 publication／Fiber／claim 的保留条件；JSON 交付与垃圾回收仍是外部操作。 |
| 实际 Node 读取参数、选定 publication／来源、句柄与版本 | `Driver::resolve`、typed import／调用授权 → `NodeRuntime::resolve` | 保持状态的历史事件；真实 Begin 租约／捕获／写入来源、精确选择和按调用方解释的只读 lift。对象方法及线协议翻译仍为外部边界。 |
| `NodeRuntime::{interfaces, dynamic}`；真实 parent、初始 provisions、当前依赖与动态所有者 | insert／configure、declare／release／remove、`publish_service`、`reconcile_declarations` | 同一历史中的接口对应与 mount／声明来源；精确发布分支及包含失败前缀的完整协调。动态接口保留扩展分类，Driver 不再另存这些表。 |
| `NodeRuntime::policy`：实际 `profile`／`configured` | configure、成功分配、mount／seal gate、通知重试选择 | 同一历史证明 profile 永久冻结、准确调用／失败前缀与完整受影响集合；保留清理失败和无关 episode。 |
| `NativeInvocation` 持有私有 `paths::Path`；`NodeRuntime::scopes` 持有存活 receipt | `begin_invocation`、`finish_invocation`、`invocation_live`、`invocation_own_live`、`check_invocation_wait` | 准确所选父前缀、完整路径查询和真实签发来源；逃逸上下文持有非活动路径条目，账本只保留存活 receipt。ALS 父选择及任意 JS 行为仍为外部边界。 |
| `Bridge<WeakReference<NativeObject>>::{objects, fibers, claims}`；私有 JS box／root map | 对象签发／读取／发布／替换／移除；Fiber 绑定／解绑；回调开始／完成；显式快照 | 准确原始引用与待处理票据关联；publication／Fiber／配方保留时禁止释放；检查完整快照覆盖。JS 解引用、box 适配层与载荷内部状态仍是审查边界。 |
| `static_values::Values<ServiceSlot>` 及共享 `Context` | 静态定义组装、读取和提供值 | 组合真实 realm／声明／继承端口与准确 Arc 输入；拒绝重复／缺失／额外导入和其他 owner 写入。外部静态租约权限仍单独保留。 |
| `SharedEpisode::association` 与实际 Episode mutex | native／static 创建及每次共享锁访问 | checked 关联与真实上下文共同签发；访问前和锁内 execution 比较。标准 Arc／Mutex 语义仍是信任边界。 |
| JS 回调派发及剩余 Driver 派发／诊断 | 回调调度、ALS 父选择、回复编码 | 原生捕获路径保持所选父级；完整 JS 因果祖先、调度及对象／效果解释仍需组合。 |
| `Configuration::{current, revision, pending, updates, structure}`；待办的 candidate／recovery | begin／work／commit／recover／refresh | 修改待办保持已接受快照／版本，不能修改批次；真实回调驱动顺序成功前缀与逆序重试栈。提交要求更新完成，恢复要求 inverse 义务为空。见[配置执行](r2-configuration-execution.zh-CN.md)。 |
| `Transaction::{before, created}`；受验证的真实 Tree 节点及原生 Allocation 记录 | apply_prepared／recover、mount、update／rollback await | 父级局部身份准备、完整移除派发和保存配方重建已在受验证树中执行，保证 allocation 唯一和准确失败前缀；取消保留旧 factory 和 inverse。工厂的 Component 含义及共同 Journal 仍开放。 |
| 持有的配置采用批次、实际登记配方版本与退回的旧值 | `Runtime::adopt_config_recipes` → `NativeRuntime::adopt_configurations` | 完整受验证预检和实际有序配方／元数据交换；错误退回完整输入并保持原生 owner，成功保留活跃状态／发布值。配方注册／替换／调用现已记录在共同 Journal；元数据效果／析构、Plugin 转换及完整语义仍是边界。 |
| `Snapshot::{tree, nodes}`、registry 的 factory／service／revision | prepare、load／reload | 实际展开／规划保持载荷、顺序、读取来源及真实父上下文；解析／转换、分组 Component 和源投影／合并含义仍需解释。 |
| `Save::{origin, documents, phases, cursor, halted}`；不可变文档载荷／文本 | `SaveStamp::start`、`step`、`Configuration::accept_saved_sources` | 原始票据在执行前进入保存对象且不会中途改变。真实返回驱动阶段；替换与持久化不同。接受检查原始修订／域及无待恢复状态；无票据和旧保存保持源状态。 |
| `Loader::configuration.sources` → `sources::Source::{root, contents, checkpoints, resolutions}`；`Checkpoint::{value, pending_sync}` | `load`、`clear`、接受实际保存 | 单一擦除历史已索引到共同 Journal；checkpoint 来自实际加载／已处理文档，并关联更早的具体已接受配置状态；未处理键不变，Sync 保留重试。源报告不能修改状态，加载文本保持不变。详见[源 checkpoint 合同](r2-configuration-execution.zh-CN.md#从真实保存推导源-checkpoint)。 |

剩余 Driver 派发／诊断、回调祖先列表、句柄批次序列化／JS 删除、压缩计数，
以及 JS Domain／Fiber／对象状态仍需联合解释。本表不将 R2-C/D/E/F 标为完成。

## 标量调用：已连接的执行片段

| 实际步骤 | 受检查结果 | 分类范围 |
| --- | --- | --- |
| 取快照，再于值／episode 锁外调用 `ScalarEffect::compute` | 经过验证的实现，其实际输出等于模型结果 | 局部准备；回调的额外任意副作用没有在这里解释。 |
| 获取 episode owner，重新检查票据／work／队列身份、阶段与组准入 | 已关闭／取消的准入不能进入受管写入 | 拒绝保持 execution owner；共享锁访问现检查签发的归属。标准 mutex 语义仍是信任边界。 |
| 比较当前值／深度与私有捕获状态 | 不匹配记录 `StaleComputation` 并拒绝；容量耗尽／计算拒绝也不改变标量状态 | 实际拒绝保持 Journal 记录状态与待登记义务。完整恢复到捕获状态允许提交。 |
| 写入实际结果，将真实 inverse 追加到所属清理队列 | 真实目标／前后态／分支／inverse；保留原有队列前缀及无关组／runner | 对应 dependent grammar 标量操作和受管登记，尚不是完整 R1 context 步骤。 |
| 派发该队列 inverse | 仅在捕获后态恢复成功；干扰时保留 inverse 供重试 | 既有标量历史和清理合同同样适用于新原语。 |

`ThenScalar`、`ChooseScalar` 组合的是局部计算：一次受管写入、一个 inverse，中间结果
不会分别发布。终端 Component 定理覆盖标量操作的完整声明载体；外层插件 continuation
或 Child 程序体仍需自己的函数解释。

实际别名投影和槽替换现有 `value_alias` 中的独立合同，通过
`Write::general_semantics`、`Replacement::production_aliases` 接入真实结果。
用户计算的额外效果仍需自己的合同；局部标量结果不证明整个回调。

## 延后集成的证据

接口／publication 批次仍待集中运行与严格负例验收：

- 两个动态 provider 和已提交 consumer：撤回、清理失败、旧回复、新票据重试及最终交接；
  拒绝绕过 `Relied` 或替换后继 owner 的实现。
- 初始与动态要求、依赖重配置拒绝，以及保留外来声明的单 owner 移除；拒绝写入错误依赖
  向量、错误跟踪静态端口或跨 owner 删除。
- 真实 JSON 发布路径的 generation-zero 准备、已退休／卸载中的后继，以及静态冲突与
  已跟踪动态冲突；拒绝绕过后继准入或冲突守卫。
- 实际多端口协调循环中的受阻端口与后续成功转移，注入错误保留部分进度；拒绝提前成功
  返回或派发另一个端口。


别名／效果批次现已运行原生 Child 的 `ScaleAdd`／`ThenScalar`／`ChooseScalar` 双分支、
计算中换槽、同 owner 重入、干扰、计算拒绝、panic、撤销与真实 inverse 清理。
[执行合同](r2-execution.zh-CN.md#原生可扩展效果与别名感知的论文映射)中的源码绑定记录
还检查 owner／因果／别名突变。下表保留更完整的 R2-G/H 清单：静态计算、准备与提交
之间的完整恢复、组取消及其余载荷／分支突变仍需验收。

| 调用者／边界 | 要检验的保证 | 预期回归或突变 |
| --- | --- | --- |
| 原生／静态 `update_reversible_with` | 新原语、溢出检查、真实分支选择、一次受管写入 | `ScaleAdd`、`ThenScalar`、`ChooseScalar` 两个分支及中间计算拒绝；突变返回值／分支使其不符合模型。 |
| 受管提交前的计算 | 用户代码不在宿主／值锁内执行，panic 保留错误种类 | 重入 setup、通过其他句柄修改、panic、捕获值析构；被拒绝的外层调用不写入受管值、不登记 inverse。 |
| 逃逸句柄／并发操作 | 提交使用捕获值／深度且准入仍开放 | 不匹配、同值更深写入、完整恢复、准备后组取消／owner 撤销；突变状态／准入守卫。 |
| 受管登记与清理 | 真实 inverse、原有队列前缀、无关组与状态保持 | 错误目标 inverse、丢弃之前记录或修改无关 runner 必须违反合同；运行恢复失败、消除干扰、重试成功场景。 |
| 实际标量历史 | 接受计算有源语义，拒绝保持标量观察 | 漏记／篡改历史事件或前后态；指定历史／解释合同必须拒绝可编译突变。 |

新增待验场景：同值替换、predicate／析构重入；通知／值／publication 交错与外域控制；
候选修改前后取消、容量拒绝、恢复不递增版本。负向控制应删除 freshness 守卫或替换
提交快照。既有宿主回归单独检查；这些新场景和负向控制没有宣称完成。

实现批次采用编译与定向 Verus 验证。集成运行／负向证据，以及绑定最终源码的完整验收
仍是独立待办。本清单不改变里程碑状态。

真实 `Admission` 现在保留在 `NodeRuntime::admissions`；preparation、seal、失败／重启、
清理标志和错误载荷存于 `NodeRuntime::episodes`。同一历史证明 Begin 来源、成功释放前保留
以及旧回复不改变状态。适配层只读资源，并直接观察账本票据；JS 对象及其余适配层缓存语义
仍开放。见 [Node 合同](r2-node-execution.zh-CN.md)。

新增待验收场景：外来域 store／check ledger；publication 缺失、检查拒绝或 provider
代次过期时不分配租约；前提齐备必须准入；多依赖容量耗尽；零依赖旧 admission 不能释放后续代次。
保留 owner／失败／重试与过期错误场景已加入 Node 集成批次；后续负向突变应覆盖遗漏选中 provider、
绕过 availability、一律拒绝合法准入、错误标记租约和删除 domain／generation
释放守卫。集成时运行既有 Driver 回归，不代表这些新负向控制已完成。

## 优先验证的共享历史连接

`ReversibleValue::Cell` 新增擦除的权威历史资源，`Snapshot` 持有对应前缀的持久
证据。`Cursor` 保留真实程序、目标、owner、continuation、检查点及擦除的调用位置。
受验证的 owner 推进程序并在返回前登记实际逆操作；`observe` 延续检查点但不授予
工作许可。标量轨迹现在包含插入的写入及失败/成功清理。真实 Child 案例贯通这条
路径，也展示两个端口别名到同一对象。完整 frame 证明仍需端口/版本到对象的绑定
及保留的旧对象；root/Child 函数体与生命周期/对象堆共同历史尚未闭合。
参见 [高风险贯通探测](r2-execution.zh-CN.md)。

后续待补案例：溢出后在其他恢复完成时重试、内容相同但分配不同的对象、值相同但
深度增加的写入、group 取消、slot 替换后游标保留旧对象、多层 Child 共享同一个值。
这些项目没有计为已完成验收。

## 强类型槽位、捕获与别名

原生服务表把 `ServiceSlot<T,M>` 的非标量存储实例化为受验证的 `SharedPayload`，
与标量 `slot::Slot` 并列。`Slot::Cell` 持有实际 `VersionedValue<Arc<ReversibleValue>>`
和擦除的权威历史。`Capture` 保留槽位、版本、真实对象及前缀证据，`Cursor`
可以保留实际 `ServiceBinding`。修改入口是槽位替换、对象操作／恢复以及
经过身份检查的游标推进。`begin_native_value_program` 在受验证 Execution
内部解析真实已提交 provider，不接受宿主提供的预期绑定。

`heap::Observation` 区分端口选择与对象状态，写入范围包含被修改对象的所有
别名。槽位替换更新指向该槽位的所有当前选择，旧版本捕获保持不变。这仍是
保留视图解释。共同 Journal 现已从实时替换／控制交错中推出本域槽位／对象的引用
完整性及实际服务观察；完整宿主／函数解释仍待完成。参见[当前范围](r2-execution.zh-CN.md)。

之前暂缓的槽位替换案例已接入：真实 Child 案例在游标运行中替换槽位，然后
在旧对象上经历清理失败与重试；动态 publication 也有对应回归。换回相同
对象仍使旧 predicate 捕获失效，泛型及静态读取保留真实 Arc。完整 R2 验收、
考虑别名的声明读写范围、多对象交错与嵌套 Child 函数体解释仍待完成。

## 共同检查点中的 publication 与 import 槽

专用服务表路径在 Journal 读取前，从每个真实可逆槽收集提交凭据。检查点将保留的
publication、owned 值及 Begin imports 关联到同域槽记录；捕获携带准确的版本／对象
提交。收集不创建可执行影子表或载荷所有者。每次真实槽创建／替换都要求准确目标的
对象凭据；共享历史证明每个前缀的本域引用闭包，因此收集后发生替换的槽仍能在读取
时刻解析。生产投影覆盖全部 publication／imports／owned 键，明确区分不透明载荷、
外域槽／对象及本域值，并具有别名写入／恢复及旧对象保留的定理。历史记录不表示
退休分配仍存活。宿主两个执行快照入口已使用这些生产者。参见[合同与本轮证据](r2-execution.zh-CN.md)。

## 已连接的原生执行域

`joint_execution::Journal` 拥有共同锁及擦除的权威映射／历史；真实对象、强类型槽位
和 NativeRuntime 分别拥有私有 `Member`。`Cell::record`、`Slot::replace` 及
可执行的 `NativeRuntime::transition` 在返回前更新对应成员。共同状态映射到
对象 value/depth、槽位版本／对象选择，以及原生控制、episode owner 和 publication 投影。
完整泛型 publication 与 Begin capture 保留在类型化历史中，并完整索引到真实共同提交。快照保留真实 Journal
实例，值快照证明与其联合条目相等。日志锁内不会运行插件回调。

`RegisteredPlugin<Body<C>>` 直接保存单服务 `Body::Value` 和多服务 `Body::Services`，
并区分普通回调。`run_value_root`／`run_service_root` 读取实际当前配方和已分配 owner，
解析登记声明，再依据计算结果结算同一 root。多服务绑定在签发 root 前检查全部分支；
每条操作随后捕获当前 Begin 服务槽。`service_composition` 连接完整有限控制流、真实拒绝
和带 Journal 的对象身份；`service_stack` 将语义 inverse 栈与实际清理队列后缀对应，
覆盖失败前缀。见[存储函数合同](r2-function-semantics.zh-CN.md)。

`Function::{key, program}` 是有限 root/Child 的存储函数体；`Function::run`
检查实际 root 状态和 Begin 捕获的槽位，把实际前缀逆操作放入 group 0。
宿主构造器为 `Plugin::native_value_program`，对象通过 `Runtime::reversible_value`
创建。`Member::latest` 保留权威联合前缀，标量 `positions` 映射局部事件。程序报告和
游标推出实际步骤的有序位置，注册报告将有限 root/Child 与其函数体和结果关联。
真实 work／清理队列投影已拥有同域私有成员，CleanupGroups 现加入真实存活成员关系、受守卫约束的移除／封闭及已消费失败标记。完整宿主／资源解释、其余 Node 观察及 loader 状态仍未完成；宿主状态与控制成员已经贡献各自的检查观察。跨域槽位目标保留独立历史，有限函数的对象地址包含实际 Journal，不会混淆域内编号。
详见[共同执行域的范围](r2-execution.zh-CN.md#同一原生执行域的统一轨迹)。

`SetupWork::joint`、`CleanupQueue::joint` 是由原生 Begin 绑定的可选私有成员；
`CleanupGroups::execution` 把同一个 Journal 传给每个新 iterator 队列。观察包含
真实票据、root 失败、排队／派发工作、槽位占用、清理失败保留和新 attempt。
`Execution::observe_execution` 在同一次读锁内核对 work 与全部存活队列；
`observe_execution_after` 保留此前联合历史前缀。opaque payload 含义和宿主标志仍是独立义务。
group 移除与封闭现已在同一写锁内核对真实队列，再提交所有者记录，将历史队列与存活成员
区分开来。参见[成员合同](r2-execution.zh-CN.md#存活清理组与受守卫约束的移除)。

`NativeRuntime::publication_snapshot` 导出完整类型化历史投影；`History::interval` 排除
漏记的 native 转换，`Snapshot::complete_projection` 覆盖该成员的每个共同事件。
擦除的 revision／位置不会保留运行时 Arc 值。`episode_snapshot` 在同一次读取区间中
核对当前 native 成员、work 和清理组，`Runtime::plugin_execution_snapshot` 在 mounted
episode 的既有 mutex 下调用。同域前提来自 Begin 与受管 frame 合同；这里没有证明任意
宿主 mutex 关联或泛型槽的内部含义。

## 真实逆操作来源与登记关联

`Inverse::origin` 是其真实成功写入的持久擦除凭证。`Execution::register_inverse`
是直接写入、准备型效果、有限程序和游标步骤共用的强类型登记入口。它从实际载荷取得
来源，保留原队列前缀，并在 `registration::Evidence` 中导出队列身份、域和真实 token。
已登记的有限 root／Child 报告也导出这些凭证。

同一 Journal 内，`RegisterInverse { write }` 是已分类的清理追加步骤，其序号必须
指向真实且更早的成功写入；异域对象与未关联队列保持明确边界，不具备该全局关联。
新增凭证字段均擦除，顺序由原有 Journal 锁验证。

受管 pending owner 现在由 `Applied::pending` 和有限解释器实际 `Batch::items`
表示。共同 Journal 持有按真实写入位置索引的擦除 `GhostMapAuth`；每个待登记载荷
持有唯一 points-to 凭据。写入提交分配条目，队列提交消费凭据；
`Evidence::pending_interval` 证明中间每个状态保留责任，`Snapshot::pending`
导出权威投影。四类受管标量路径仅对实际同域队列启用它；原始值操作、异域对象与
未关联队列保留明确边界。

`Execution::attempts` 现在保留由锁内真实生产者追加的擦除凭证。直接写入／prepared
effect 的每个已准入返回均追加恰好一条；成功关联登记，失败关联真实拒绝原因。
Cursor 的错误关联实际 checkpoint；有限程序必须先登记成功前缀再返回报告。
work、清理、root/Child 和原生生命周期合同保留历史。`Ledger::rejection_step`
证明真实拒绝提交保持整个联合状态及 pending 映射；该记录不是任意宿主操作的完整清单。

强类型标量派发现在返回 `restoration::Evidence`，关联从槽里取出的准确 inverse、真实恢复／受阻
凭证和匹配确认。同域凭证在一条连续 Journal 轨迹里按该顺序出现；失败把原 inverse 放回选中槽。
`Execution::dispatch_cleanup` 导出证据，错误／空动作保留队列及其轨迹。既有重试递增 attempt，
载荷保持不变。详见[恢复合同](r2-execution.zh-CN.md#从已派发-inverse-到实际恢复与确认)。

强类型结果现在还证明了**每个中间状态中的已派发清理责任**。生产者从真实凭证出发，使用
实际 next-attempt 计数器与共用转换规则建立区间：票据持续有效／已派发，选中槽持续为空，
直到首次确认；此后任意真实历史扩展都不能重新激活旧 attempt。准确 inverse 身份和失败保留
仍由强类型 owner 合同保证。恢复成功在确认前消费 inverse，继续保留的是责任而非已消费的 Rust 对象。
详见[区间合同](r2-execution.zh-CN.md#每个中间状态中的已派发清理责任)。

仍待组合：将已建立的存活清理组成员关系，与共享宿主状态、泛型槽内部语义及任意回调组成完整资源清单。
当前 pending 条目表示未登记的受管写入；已派发区间补上强类型标量责任，但不是完整论文上下文或原子论文步骤。
详见[写入／登记合同](r2-execution.zh-CN.md#从真实写入连接到真实逆操作登记)。

## Node 协议组合更新

[`NodeRuntime`](../crates/cordis-kernel/src/node_runtime.rs) 现在共同持有真实
`LifecycleState`、`PublicationStore<u64>`、`Availability` 和 checked-publication 集合。
修改入口追加同一条连续历史并保持共同域不变式。动态声明与 publication 接管仍是明确扩展；
值／检查变化不是完整观察的 stutter。适配层只保留诊断错误，序列化动作票据来自内核。
保留的 admission 和 episode 状态／错误载荷也已接入受验证修改；剩余 JS Domain／Fiber 缓存
及效果仍开放。保证、证据以及
Node 历史与 native Journal 的边界见[审查路径](r2-node-execution.zh-CN.md)。

## 登记配方历史与真实调用版本

`NativeRuntime::recipes` 拥有准确的带类型注册表历史和共同 Journal 成员；注册、SharedChild
注册、替换、移除以及 callback／Value／Service root 返回是修改入口。元数据可变借用必须
保持全部配方。快照在同一读锁区间认证配方和 native owner；调用记录在写锁内核对实际
Episode 票据与工作域。详见[配方历史审查](r2-configuration-execution.zh-CN.md#共同执行历史中的真实登记配方)。

`ProgramReport::receipts` 和多服务 `Report::receipts` 保留实际解释器收集的、会被擦除的
持久凭据。每条成功指令贡献实际写入及可选的逆操作登记凭据；失败的服务调用从
`Execution::attempts` 复制实际最后一条可信凭据。Value 报告还保留完整对象观察。
`RegisteredReport::completion` 指向真实配方 Call 提交；`record_recipes_following`
在该提交的同一写锁周期核对全部本地前驱。即使正向值属于外部域，返回区间仍包含
本地逆操作登记，但不宣称跨域全局顺序。见
[函数返回合同](r2-function-semantics.zh-CN.md#将真实效果接入实际调用返回)。

[受验证分配](r2-execution.zh-CN.md#受验证的原生身份分配)缩小了原生身份分配的边界。不复用保证限定于同一分配器，尚未消除共享 Episode／Journal 的归属前提。

[Execution 直接拥有状态的合同](r2-execution.zh-CN.md#execution-直接拥有共享效果状态)已消除效果状态的 Journal 归属前提，不依赖数字分配器不重复定理；整个共享 Episode 的解释仍待完成。

## 已接通的状态归属保持入口

下列 61 个真实方法具有 link 保持合同；`retire_effect` 只移除退休条目，其余方法保持整张表。两个程序循环也保持该关系。新增／观察退休入口另有准确插入／移除合同，见[完整历史](r2-execution.zh-CN.md#实际调用与交错中的状态连续性)。这不是全宿主语义的覆盖清单。

| 内核文件 | 实际方法 |
| --- | --- |
| [`execution.rs`](../crates/cordis-kernel/src/execution.rs) | `attach_execution`, `take_effect`, `put_effect`, `activate_effect`, `retire_effect`, `withdraw`, `activate_external`, `seal_external`, `provide`, `issue_root`, `start_root`, `cancel_queued_root`, `complete_root`, `fail_root`, `abandon_root`, `take_child`, `take_group`, `complete_request`, `register`, `cancel`, `pop`, `complete_future`, `complete_failure`, `complete_result`, `retry`, `remove`, `enqueue_owned_child`, `enqueue_effect`, `admit_effect`, `land_effect`, `enqueue_native_child`, `apply_value`, `apply_value_following`, `dispatch_cleanup` |
| [`managed_native.rs`](../crates/cordis-kernel/src/managed_native.rs) | `finish_managed_execution`, `release_managed_execution`, `withdraw_managed_execution`, `admit_managed_root`, `retry_managed_execution` |
| [`native_effect.rs`](../crates/cordis-kernel/src/native_effect.rs) | `apply_native_effect` |
| [`native_runtime.rs`](../crates/cordis-kernel/src/native_runtime.rs) | `finish_managed_execution`, `release_managed_execution`, `admit_managed_root`, `withdraw_managed_execution`, `retry_managed_execution` |
| [`poll_control.rs`](../crates/cordis-kernel/src/poll_control.rs) | `retry_controlled_execution`, `release_controlled_execution` |
| [`scalar_effect.rs`](../crates/cordis-kernel/src/scalar_effect.rs) | `apply_prepared_effect` |
| [`service_function.rs`](../crates/cordis-kernel/src/service_function.rs) | `run_service_root` |
| [`service_program.rs`](../crates/cordis-kernel/src/service_program.rs) | `run_service_program` |
| [`setup_context.rs`](../crates/cordis-kernel/src/setup_context.rs) | `admit_scoped_effect`, `enqueue_native_effect` |
| [`value_access.rs`](../crates/cordis-kernel/src/value_access.rs) | `apply_native_value`, `apply_native_value_chained` |
| [`value_cursor.rs`](../crates/cordis-kernel/src/value_cursor.rs) | `advance_value_program` |
| [`value_function.rs`](../crates/cordis-kernel/src/value_function.rs) | `run`, `run_native_value_program`, `run_value_root` |
| [`value_program.rs`](../crates/cordis-kernel/src/value_program.rs) | `run_value_program`, `run_value_program_following` |
| [`value_registration.rs`](../crates/cordis-kernel/src/value_registration.rs) | `register_inverse` |

## 完整已记录载体的分类边界

`joint::classification::Observation` 同时保留全部 13 种 Record 与 pending 义务，真实快照和函数返回导出完整轨迹分类。其他记录的存在和值均被保持；完整 stutter 必须两张表都不变。它不覆盖本清单中尚未解释的普通宿主／JS／配置函数内部。见[实际生产路径与边界](r2-execution.zh-CN.md#已记录原生观察的完整分类)。


## 共享强类型载荷 owner

`SharedPayload<T: ?Sized>` 现在持有真实 Arc、版本、私有锁、擦除的强类型历史和
共同 Journal 成员。原生 `provide`／`publish` 由真实 Execution 分配这个 owner，
读取、替换与检查均保留该归属。全部已发布、自有和 imported 槽在同一次 Journal
读取中形成完整服务投影。本域载荷替换改变全部当前别名，保持无关标量／载荷观察；
外域保持明确区分。见[合同、论文关联与待验收项](r2-execution.zh-CN.md#真实执行中的共享强类型载荷)。
受验证退休交还载荷并留下 Journal 终态，宿主最后槽引用的 guard 调用该操作，
保持锁外析构。这补齐普通载荷存储锁边界；外层 Episode 关联、任意 T 内部状态及异构函数／inverse
语义仍未关闭。

## 强类型载荷恢复状态

实际 payload cell 同时持有语义 head/depth 与版本容量预留。逆操作构造认证原始
状态历史；实际清理分支持有这个逆操作和原服务槽位 Arc。`apply_native_payload`
选择已提交的服务，`apply_payload` 登记逆操作，`dispatch_payload_cleanup` 负责
选取、恢复与确认。失败保留原队列项；历史和登记凭据会被擦除，不新增运行时旧载荷
历史。参见[论文解释与边界](r2-execution.zh-CN.md#可恢复的强类型载荷替换)。

逆操作还保留实际 Journal，使载荷退休后仍能认证读取。真实清理返回可擦除的请求／
读取／写入／确认凭据。失败只有读取位置，不伪造写入；同域内清理责任持续存在和
已完成票据不复用，都从真实完整历史推导。见
[强类型清理区间](r2-execution.zh-CN.md#强类型清理的请求读取和确认)。
