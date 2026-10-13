# R2：生产执行路径的合同

[English](r2-execution.md) · [论文里程碑](paper-refinement-roadmap.zh-CN.md)

R2 要把论文约束连接到实际的托管调用。**R2 仍在推进中。** 下列合同已经用于
Rust 和 Node 宿主，补齐了载荷、登记和结果传递的缺口；它们尚不构成整个宿主的语义
refinement，也没有证明任意插件回调满足 Component 合同。

## Begin 分配的 episode 归属与延迟根调用

生产 `NativeRuntime` 现在保存 Begin 实际分配的 setup 票据和工作域。不变式要求
Loading、Active、Unloading 插件恰有一个当前归属记录，Inactive 或已移除插件
没有记录，发布值必须属于该记录。根调用准入与执行、Finish、撤销、工作结算、
失败、重试和 Unload 都检查传入的 execution 或 invocation。修改不透明宿主字段
不能替换该记录；只有成功 Unload 才删除它，失败与重试保留它。

`RegisteredInvocation` 还保留准入时的生命周期票据。`NativeHost::call` 在真正调用
保存的回调之前，重新检查待完成 setup 动作、当前 generation、Loading 阶段与
退休标记，并保留原有 owner／domain／回调版本检查。因此，尚未开始执行的根调用
在撤销或退休后会被拒绝；即使复用工作域，它也不能在下一 episode 执行。本地工作
撤销同样关闭新的根调用准入。已经执行中的回调及其异步结果仍通过已有完成协议落地；
这里没有实现抢占回调。

原生连续历史现在同时观察实际归属记录、控制状态与发布值。`owner_has_begin`
证明保留的记录来自一次成功 Begin；`owner_retained` 证明在该插件成功 Unload 前
不能替换它。归属变更附随已有 Begin／Unload 控制步，准入检查和拒绝保持该观察。
这是生产执行投影的加强，不改变 R1 解释，也没有把它宣称为完整 context 对应。

审查入口为 [`native_owner.rs`](../crates/cordis-kernel/src/native_owner.rs)、
[`native_runtime.rs`](../crates/cordis-kernel/src/native_runtime.rs)、
[`plugin_registration.rs`](../crates/cordis-kernel/src/plugin_registration.rs)、
[`native_host.rs`](../crates/cordis-kernel/src/native_host.rs) 的实际检查，以及
[`native_history.rs`](../crates/cordis-kernel/src/native_history.rs) 的归纳证明。
`native_host` 与 `native_runtime` 集成测试覆盖延迟调用、退休、工作域复用、外来
execution 与成功释放；命名负向控制删除相应守卫或归属更新。

使用固定工具链复现这些运行案例：

```sh
cargo test -p cordis-kernel --test native_host --test native_runtime --offline
```

共享 `Arc<Mutex<Episode>>` 仍由普通 adapter 持有。这些检查将其提交的数字身份
对应到当前注册表，不证明锁的调度、不透明参数的含义，也不认证刻意复用**全部**
身份编号的独立原始宿主对象。普通宿主的唯一 domain 分配仍是边界。任意函数字段、
服务槽内部状态和 Node／native 联合 context 仍需对应到 R1，因此 R2 保持进行中。

## 从 Begin 保留至发布和释放的来源

每个原生 episode 现保存一个不可变、编译时擦除的 `Capture`：Begin 捕获依赖时
实际的控制状态、声明、committed bindings、provider 代次和发布槽。
`Capture::wf` 证明捕获的双向对应：某个 import 存在，当且仅当 committed binding
在当时的来源表中有可用槽，且其中保存的就是那个实际槽。
快照由生产构造器直接产生，不要求调用者提供“预期值”。

`Execution::capture_correspondence` 把这个 Begin 观察连接到当前工作与原生值 owner。
可执行修改保持同一份 capture，包括 Child／effect 准入、poll 落地、取消、清理、
重试和可逆值程序。episode 未关闭时，imports 始终等于最初捕获的 imports。
Finish 将同一份 capture 带入实际 publication，因而进入原生联合历史。
Unload 返还最初捕获的 imports，并清空已关闭 owner；清理不会按当前 target 重新抓取依赖。

值 owner 还保存实际 cleanup／work domain。发布和释放先检查它是否与传入的工作队列
一致，再改变状态。因此，即使原始嵌入刻意复用生命周期域、插件 ID 和代次，也不能
换用另一个工作域的队列。这补齐了工作域替换守卫，但没有把数字 domain 变成分配对象
身份凭据。普通宿主的唯一 domain 分配器、共享 episode mutex 仍是明确边界。
完整 R1 解释还需要组合这些共享 owner、函数含义与 Node 发布版本。

快照是 ghost 数据，不增加运行时表复制、历史分配或额外 `Arc` 引用。
跨线程回归保留逃逸上下文，经历 provider 撤下、清理失败和重试，再检查替换与新一轮
执行，同时核对准确的 `Arc` 引用数以及旧上下文关闭后的拒绝行为。
另一个回归分别在 Finish 和 Unload 检查工作域替换被拒绝。

审查路径：`native_capture.rs::Capture` → `LifecycleState::capture_native_values`
→ `NativeEpisode::wf` → `Execution::capture_correspondence`
→ `NativeRuntime::{begin_managed_execution,finish_managed_execution,release_managed_execution}`。
这加强了 committed dependency 与式 (46) 原生发布视图的实际对应，未缩小 R2 原有验收条件。
负向控制分别移除工作域检查、丢失 Begin 来源、把 publication 的 Begin 控制快照换成
Finish 时的状态；每项都必须编译成功，并由指定合同拒绝。定向检查不代表完整负向回归验收。

## 原生注册表与发布表的联合历史

生产 Rust `Runtime` 现通过 `NativeDriver` 持有
`NativeRuntime<R, H, V>`。注册图与 `NativeServices` 位于同一个受验证 owner
内部，Begin、Finish、查询和 Unload 的调用者不再单独传入服务表。
真实入口保持同一个联合不变量：

- 每个 Active 注册实例都有完整的用户端口发布表，对应当前 episode 代次和真实共享槽。
- 每个保留的发布表都属于仍注册的 Active 或 Unloading provider。单独退休保留发布；
  撤下时停止新查询，但为 committed consumer 和恢复保留原值。
- Finish 先检查真实 episode 的声明是否与存储的 recipe 一致，再发布。
  Release 通过实际工作与清理守卫后，只删除本实例的表。
  失败、重试、压缩、recipe 更新和共享 Child 操作都保留其他实例的发布。

`NativeEpisode::matches_provisions` 还会拒绝编号与代次碰巧相同、声明序列却不同的
值 owner。这是可执行守卫，不是加在普通 Rust 调用方上的假设。
普通宿主的全局 domain 分配器仍负责区分不同 runtime 实例。

`NativeRuntime::history_correspondence` 证明了从空状态到当前观察的连续联合历史，
包含**真实控制状态与保留的发布表**。独立关系 `native_history::step` 规定：
Finish 只增加该 provider 的表，Unload 只移除该表，其他控制步骤保留全部表。
不改变这个观察的调用保留原历史。显式 Restart 仍属于扩展；不含 Restart 的历史
具有严格论文控制投影。ghost 历史在 Cargo 编译中擦除。

这在注册表／共享槽边界连接了式 (46) 的原生发布视图与 L-Finish、L-Leave、L-Unload。
它仍未把 `Arc` 内部值、任意回调函数体、共享 episode mutex 状态、Node 发布版本
共同解释成完整 R1 context。R2 的剩余验收条件没有缩小。

审查路径：`native_runtime.rs::{linked,wf,finish_managed_execution,
release_managed_execution,history_correspondence}` → `native_history.rs::step`
→ `cordis-driver/src/native.rs` → `Runtime::poll_settle`。
聚合 owner 回归覆盖完整发布、冲突声明、provider／consumer 失败重试、
其他实例的值、旧／外部 episode、recipe／宿主记录更新、退休、压缩以及具有空发布表的共享 Child。
三个负向控制分别移除声明守卫、丢弃其他实例发布和遗漏联合历史步骤；
每项都要求突变体能编译，且指定合同确实拒绝它。


## 已用于实际运行的合同

| 用户可观察的行为 | 可执行合同 | 生产调用者 |
| --- | --- | --- |
| publication 持有 owner 实际传入的值 | `PublicationStore::publish_checked` 检查真实生命周期域、代次和准入，再保存泛型载荷 | `Driver::publish` → `LifecycleDriver::publish_value` |
| 替换保留 publication 身份并返回真实旧值 | `replace_checked` 和 `ValueCell::replace`；拒绝时原样返还新值 | `Driver::set`、Rust `ServiceSlot::replace` |
| 旧清理租约仍读取自己保留的值 | `leased_value` 从真实租约记录中取得 publication 身份与载荷 | `Driver::read` |
| 只有生命周期和完整资源清单检查通过，才能转移实际载荷 | `finish_resources` 将已有票据／租约协议与载荷转移组合；拒绝时三者均保持原状 | `LifecycleDriver::finish_cleanup_values` |
| 在轮询 Future 前，用实际参数调用工厂 | `RegisteredPlugin::call` 直接调用保存的原生 `FnMut`；`invoke_future` 保留清理工厂实际返回的 Future | Rust `Runtime::start`、`initialize_cleanup`、`Runtime::poll_groups` |
| 异步清理消费其 Future 实际返回的结果 | `Awaiting::complete`／`await_completion` 用 Verus 原生 Future 语义保存来源与实际结果；`complete_future` 据此判定成功、失败或消耗 | Rust `initialize_cleanup`、`Runtime::finish_reply`、`StaticCleanupFuture::complete_reply` |
| 先保存实际返回的 inverse，再决定是否继续 | `CleanupQueue::land_result` 自行分配 token、保存实际 inverse，并根据结果和取消状态选择后续动作 | `Runtime::poll_groups` |
| 不能因为一个组为空就关闭仍有其他工作的 episode | `CleanupGroups` 持有全部清理队列；`remove`、`seal` 检查未落地 stage、已交付凭据、保留失败和实际载荷，然后关闭注册入口 | `Runtime::poll_groups`、`Runtime::poll_settle`、`StaticCleanupFuture::poll` |
| 整体重试遇到不可重试失败时，不能先推进其他组 | `retry_execution` 先检查绑定的工作状态和全部队列，再一起推进生命周期与 inverse 的重试票据 | `Runtime::retry_cleanup` |
| 只有实际准入的原生 episode 能完成或释放其生命周期 | `begin_execution` 创建两个绑定的 owner；`finish_execution` 与 `release_execution` 检查原始票据和当前代次 | `Runtime::start`、`Runtime::poll_settle` |
| 移除一个组不能把已消耗的失败变成恢复成功 | `CleanupGroups` 保留已接受的 `Drained` 记录；`release_execution` 从它推导最终结果 | `Runtime::finish_reply`、`Runtime::poll_settle` |
| Child 在 realm 隔离后仍保留父插件的实际依赖 | `register_plugin` 解析声明的键，同时继承原始端口和子 realm 端口，并排除子插件自己提供的端口 | `Runtime::mount_inner` |
| 热更新不能让已经准入的调用误用新回调 | `admit_registered_root` 绑定真实工作与登记对象；`call` 检查域、owner、回调版本，再直接调用保存的 `FnMut` | `Runtime::start` |
| 原生 Child inverse 不能删除另一 runtime 中数字 ID 相同的插件 | `ChildIdentity` 来自真实登记；`retire_child` 验证其域和父插件 | `Runtime::poll_cleanup` → `dispose_child` |

原生 Rust 服务值还通过 `begin_native_execution`、`NativeEpisode::provide/read`、
`finish_native_execution`、`release_native_execution` 接入 `Runtime::poll_settle`、
`AsyncSetup` 和 `NativeDriver`，见下文原生服务值一节。

Node 容器保存的是实际的 `u64` JavaScript 值句柄；Rust 值单元保存的是实际的
`Arc<dyn Any + Send + Sync>`。这些合同不解释 JavaScript 对象的可变字段，也
不解释 Rust 值的内部可变状态。载荷无需实现 `Clone`、`Copy`、`Debug` 或相等比较。租约固定的是 publication
身份，而非不可变快照：替换该 publication 会改变其租约读到的值；新 publication
则使用另一个身份。

清理适配保留既有策略：可重试工厂失败后继续保留；普通 Rust 的一次性清理失败
可以报告为已消耗的 `Drained`，静态宿主采用 `RetainFailure` 并保持阻塞。
两者都不会被自动报告为成功恢复。待丢弃的工厂和被拒绝的载荷在记账互斥锁释放后
才析构，以便用户 `Drop` 安全地重新调用宿主。

## 与论文的对应

`publication_projection.rs` 把真实容器解释为键值查找表。
`publish`、`replace`、`revoke` 在自己的函数体中使用相应证明：

- 发布向当前不可见的键插入实际传入值。
- 替换只更新该键，并返回它真实的旧值。
- 撤销只移除该 publication 的可见性。重复撤销不能隐藏同键的新 publication。
- 改变租约元数据、回收已撤销的值不改变当前查找表；保留租约观察是另一个观察，可能改变。

这里解释的是注册表的可见性投影。宿主 phase、依赖和可用性检查仍会对服务查找
施加额外条件；单独这张表不是整个宿主观察。

这些是 §3.4 键局部更新的实际实例，对应 `coeffects::put`。它们不等于证明
多版本宿主注册表与 R1 的整个 reified context 相同。写回返回的旧值能够恢复单次
替换，也不能据此推导插件在干扰下的完整 inverse law。

`LifecycleState` 现在向上层传播插入时实际的 parent／dependencies／provisions，
Begin 时的 committed bindings，以及 Finish、Retire、Remove、Unload 的已有
控制步骤关系。记录压缩保持控制观察；显式重启和动态接口改变保留各自的扩展合同。

`land_result` 同时证明真实载荷更新，以及 Iter、Finish 或延迟 diversion 的
累加器投影。这一投影不解释不透明 inverse 函数的外部效果。论文没有对应守卫的
失败或显式效果组取消，仍属于宿主扩展。

## 异步证明的边界

对于传入 `await_completion` 的 Future，Verus 证明：如果完成值返回，其中保存
的就是该 Future 的真实输出，以及包装时传入的来源。这不证明它最终一定返回，
也不证明调度公平。`Completion` 的字段不能由接收者替换，但它不是外部 I/O 的
真实性凭证：调用者仍可以包装一个立即完成的 Future。

`invoke` 通过实际调用建立
`callback.ensures((actual_argument,), actual_result)`；`invoke_future` 立即调用
工厂并保留其实际返回的 Future，不会把工厂副作用或 panic 捕获推迟到第一次轮询。
原生 setup 现通过 `RegisteredPlugin::call` 直接调用保存的 `FnMut`；cleanup 工厂
使用 `invoke_future`。迭代器入口现使用下文的 `EffectRun::call` 及其私有轮询收据，
适配层不传入预期结果。
经过检查的 `witnessed_invocation` 与 `witnessed_completion` 用真实代码实例化
了这条数据传递路径。

受验证的调用者仍需建立 callback 的 `requires`，受验证的插件仍需证明自己的
效果律。普通 Rust／JavaScript 插件体仍在这个证明之外。原生登记与调用现已按
下文连接，但这仍不证明插件的 inverse law、完整宿主解释或任意外部 I/O 的真实性。

## 已由内核持有的组合状态

`CleanupGroups<T>` 替代了宿主原来持有多个独立队列的可变 map。字段是私有的，
也不向外借出可变队列。修改一个组保持其他组。移除的队列退出活跃 map，仅保留
递增的身份计数，因此存储和排空扫描随活跃组数量增长，不扫描历史空槽；移除后
也不能复用旧域冒充另一个组。
关闭时检查全部队列，因此根队列为空不能掩盖其他组的未落地 stage 或已交付清理。
已取消 stage 必须落地后才能移除其组，实际返回的 inverse 继续保留。
整体重试的预检查失败不修改任何组。关闭成功证明全部已持有队列都没有保留载荷、
已交付回调或未落地 stage，并关闭该容器后续的注册入口。

轮询 Rust Runtime 和静态适配器都使用这一组合。下面的 `SetupWork` 进一步
连接根 setup 的交付凭据和待处理请求。原生生命周期准入与释放现已接入这些
owner，见下节；原生 publication 值以及 Child 请求／inverse 的配对和同步现已有
下述合同。完整宿主观察仍需联合语义不变式，这些局部组合不能关闭整个生产状态的验收义务。

## setup 与请求也参与排空

`SetupWork<C, G>` 持有真实的 Child／效果组请求，跟踪根 setup 和已经交给宿主
执行的请求。`WorkItem`、`PendingWork`、`WorkReceipt` 的载荷与身份字段都是
私有的：实际请求经过 `run` 调用后产生结果凭据；异步工厂经过 `start` 后保留
实际 Future，只有该 Future 返回才产生其完成结果。派发队列为空而已交付请求
尚未返回时，整个 episode 仍未排空。队列采用 `VecDeque`，不会在每次派发时
搬移剩余请求；已完成票据退出活跃 map。

原生 Child 请求由 `enqueue_native_child` 同时构造申请与 inverse；通用
`enqueue_owned_child` 继续用于外部宿主提供的成对载荷。拒绝时原样返回，
由宿主在释放锁后析构。最终 `seal` 检查根 setup、排队与已派发
请求以及全部清理队列，并检查二者属于同一清理域。Rust Runtime 和静态宿主都
使用该守卫；普通 Runtime 的初始化完成也使用同一组实际状态。

尚未开始轮询的根 Future 可以在撤回后取消。已经开始的 Future 必须返回，或
保留为未确认的放弃状态；它不能走“尚未运行”的取消路径。异步完成保留实际
`Result`，失败不能使初始化成功。下文的受验证转换保留传入的真实 poll 结果，
并只能把捕获到的 panic 转为失败；执行轮询和捕获 panic 仍由普通 Rust 负责。调用关系也不能
替代插件的效果律，或 Child 请求、共享句柄与 inverse 之间的完整语义关系。

## 登记的回调与原生 Child 操作

`Runtime::mount_inner` 通过 `NativeHost::register`／`register_child` 调用
`LifecycleState::register_plugin`／`register_child_slot`，包括动态 Child 的真实分配。它消费实际的 `PluginDefinition`，读取父插件在内核中的权威声明，
根据传入的 realm map 解析键，并执行真实插入。返回的 `RegisteredPlugin` 持有
实际回调、解析后的接口和保留的 anchor；`NativeHost` 将它与真实 `Mounted`
载荷一同持有，普通宿主代码不再另行向注册 map 插入登记对象。

合同同时证明精确的成功条件与产生的接口：继承的依赖保留原始端口和子 realm 中的
端口，不引入重复端口，也不继承子插件自己提供的端口。重复声明和冲突的保留会被
拒绝。登记不要求依赖已经可用，可用性仍在 Begin 时检查。失败保持生命周期状态，
并返回原始定义和回调。更严格的父插件条件、realm 映射和合成 anchor，是围绕论文
Insert 控制规则的明确宿主约定。

`admit_registered_root` 检查实际未完成的 setup 动作、当前代次、登记域与 owner，
然后签发包含实际参数和回调版本的私有调用对象。`RegisteredPlugin::call` 检查
这些身份，直接调用保存的 `FnMut`，不接收替换回调或预期结果。Verus 原生调用
合同把登记的函数及实际参数，与返回的 `WorkReceipt` 关联起来。

`WorkReceipt::dispatch` 区分工厂实际返回的 `Ready` 结果和 `Pending` Future，
两条路径都保留签发的根任务身份。工厂仍立即运行，仅其返回的 Future 延后轮询。
同步完成和有条件的异步完成接入已有根任务／排空协议；捕获到的 panic 走只能
报告失败的入口。原生 Runtime 使用这条路径，静态适配器复用结果分派合同，但
保留自身的外部登记边界。

替换回调保留插件身份，并推进经过溢出检查的版本。替换前已准入的调用会被拒绝，
不会执行旧回调或新回调；已经开始的 Future 仍保留原来的完成身份。批量配置更新
在修改前检查每个回调所需的全部版本增量，安装结束后再析构旧捕获值。

Child 登记成功还会生成私有 `ChildIdentity`，携带实际 runtime 域、父插件和
分配出的 ID。原生清理保存它并调用 `retire_child`，合同证明对该 Child 执行
Retire 控制步骤。Child 移除后的重复调用保持状态，不会退休后续替代插件，也
不会操作另一 runtime 中数字 ID 相同的插件。退休是请求 Child 撤回，不等于
证明其资源已恢复；已有清理和移除守卫仍然必要。

原生共享句柄现在保存私有 `ChildSlot`，其来源从实际 `SetupWork` 生命周期动作
构造。`register_child_slot` 检查 runtime 域、父插件代次、存活阶段和 Pending 状态，执行
真实登记，再写入该次登记实际返回的 Child 身份；它不接受宿主另行报告的成功 ID。
重复、失败、已取消或旧 episode 的请求不会分配节点，并返回原始回调。分配失败
保持 Pending，宿主用 `reject` 记录实际错误；这个只能报告失败的入口不能覆盖
成功分配。

`retire_child_slot` 自行读取已分配的身份。若 inverse 在分配前就被消费，它将
Pending 槽改为 Cancelled，迟到的请求便不能创建失去清理者的子插件。失败和
取消的槽没有需要退休的 Child；重复退休保留原身份，移除后也不会指向替代节点。
原生 Runtime 现通过下述 `SharedChild` 调用这些操作，其配对和同步也进入证明。
拒绝后的回调捕获值析构和后续宿主退休回调均放在释放锁后。静态适配器仍使用
明确的外部分配确认协议。

这些合同已连接真实分配和登记函数调用；下述共享 Child 协议进一步减少了普通
宿主的连接假设。但 publication／context 观察、回调／panic 适配和具体插件的
效果／inverse 定律仍需完整语义组合。登记存储与生命周期成员关系已有后文的
联合不变式。域与服务键分配器的全局唯一性仍是宿主边界。

## 真实请求与 inverse 共享同一个 Child

[`shared_child.rs`](../crates/cordis-kernel/src/shared_child.rs) 补齐了原生 Child
请求／inverse 的别名对应与同步合同：

- `enqueue_native_child` 只接收真实请求载荷，从实际 setup 动作构造一个
  `SharedChild`，将同一句柄放入排队的 `NativeChildRequest` 与保留的
  `ChildCleanup::Native`，再返回观察句柄。准入有精确成功条件；拒绝时原样
  返回载荷，两个队列均保持不变。这个原生入口不接受调用方选择的 inverse 句柄。
- 私有 `vstd::rwlock::RwLock` 持有实际 `ChildSlot<()>`，锁不变式将槽绑定到
  runtime、父插件和 episode。登记、拒绝与退休使用独占访问；观察使用共享访问。
  `register_shared_child` 证明成功**当且仅当**锁内观察到的状态和真实注册表
  满足分配守卫。
- 每次终态决定生成持久的 `GhostMapAuth`／points-to 凭据，凭据对应实际槽
  修改，不是另建一份预期日志。`ChildSnapshot::terminal_agrees` 证明同一槽的
  两个终态观察不能矛盾。`cancellation_precludes_assignment` 将真实 Cancelled
  观察与之后的观察组合，后者不能为 Assigned。再结合真实登记结果合同，可以
  跨越多次锁获取，排除 Pending inverse 完成后的成功分配。
- 每个操作返回实际前后观察，返回前释放锁。Runtime 的动态 Child 使用这一
  入口；已经登记的原生子插件通过 `from_identity` 接入，保持真实身份。
  Retire 仍不同于 Remove，也不同于资源已排空。

它将论文 Child 分配／Retire inverse，以及 Definition 58／63 的控制步骤投影，
连接到真实队列载荷和共享状态；这不是新增论文规则，也不是完整 R1 Child 解释。
不能由此宣称任意插件效果、完整宿主观察或 Theorem 64 已证明。

同步证明使用固定 vstd 的锁／资源合同和标准 `Arc` 克隆合同，内核检查不重新验证
vstd 或 Rust 标准库。该锁使用自旋，不证明公平性、无饥饿或全局无死锁。临界区
不调用用户回调。锁内只有标量生命周期状态：vstd 锁要求显式释放，且不会自动
析构内部载荷，因此错误文本与回调捕获值保留在锁外。诊断文本、panic 适配和其他
Runtime 锁仍在这份共享槽证明的边界之外。本轮未新增依赖，也未改变工具链版本。

## 从生命周期准入到实际释放

`LifecycleState::begin_execution` 执行真实 Begin，并用该 setup 动作的域、owner、
代次和动作身份创建 `SetupWork` 与 `CleanupGroups`。来源字段私有且不可更改。
即使另建一个数字清理域相同的空容器，也不能代替已经准入的清理组。
全局域的唯一性仍由普通 `LifecycleDriver` 的原子分配器提供，属于宿主边界。

原生 Rust Runtime 的整个 episode 使用以下受验证入口：

- `settle_execution` 等待实际根 setup、已派发的 Child／效果组请求和未落地 stage，
  然后才能确认最初的 setup 动作。
- `finish_execution` 还检查当前真实 target 与全部清理组，再执行真实 Finish。
  Finish 被拒绝时可以确认已经结束的 setup，但不能改变内核状态或使服务 Active。
- `fail_execution` 要求存在队列中保留的失败，且没有未落地工作或仍在执行的清理，
  然后保留生命周期义务和已提交依赖。
- `retry_execution` 先检查全部队列，再一起推进生命周期与 inverse 的重试身份；
  被拒绝时二者均不改变。
- `release_execution` 检查绑定来源、当前代次、restoration 状态、未完成的生命周期
  动作、根 setup／请求及全部清理队列。它自行推导 `Succeeded` 或 `Drained`，
  消费动作、关闭两个 owner，并执行真实 Unload。拒绝时三份状态均保持原状；
  成功则证明该 owner 已释放 committed dependencies 且处于 Inactive。

宿主不再选择最终的成功标志，也不再另存 `cleanup_drained` 布尔值。受验证的组
owner 记录已经接受的消耗失败，在删除组、重试和关闭时保留它。新 episode 使用
新来源和空失败记录。同步 Child 结果通过 `complete_result` 使用与 Future 相同的
受验证结果策略。Child 分配／退休、真实配对与共享槽同步现已有上述合同；
普通回调／panic 适配和完整宿主观察仍需语义对应证明。
面向外部宿主协议的底层显式报告 API 继续存在；收到报告不等于证明外部效果。

Begin、Finish、Unload 的合同连接到已有论文**控制投影**；它们还不是完整 R1 的
值／代码／continuation 解释、完整 Child 效果或整条生产轨迹的证明。静态／Node 桥接
保留各自的外部完成边界，不能把这份原生组合证明自动推广到所有适配器。

## 原生服务值参与准入、Finish 与 Unload

`native_values.rs` 现在持有原生 Runtime 的真实发布表与 episode 服务槽。
`begin_native_execution` 执行实际 Begin，同时创建绑定的 `SetupWork`、
`CleanupGroups` 和 `NativeEpisode`。外部不能用已有工作票据再次构造值 owner。
域检查及旧 publication 检查在 Begin 之前完成，拒绝时不改变控制状态。

私有捕获函数读取内核中实际 committed 绑定，并复制每个可用绑定对应的真实
`Arc<ServiceSlot>`。合同证明双向关系：每个保留的 import 都来自当前代次的
已绑定 provider，每个可用的已绑定槽也都被保留。无关服务不会因此增加持有者。
realm 与 provider 身份仍是查找键的一部分。这里保留的是同一服务槽的 referent，
不是对内部可变服务内容做不可变快照。

`NativeEpisode::provide` 只接受已声明且尚未提供的键，保存实际实参；拒绝时
原样返还实参。其 `owned_table` 投影证明了 §3.4 的同一 `coeffects::put` 键局部
更新，并保留 import 和其他键。这是 episode 的局部表，不是完整 R1 上下文。
`read` 只能选择自己提供的值或实际捕获的绑定。全局 `visible` 还会解析当前
Active provider 并检查代次。因此，撤回后新调用看不到该 publication，正在清理
的旧 episode 仍能读取原来绑定的服务槽。

`finish_native_execution` 检查所有声明值均已提供、工作和队列来自同一次准入，
且真实 Finish 守卫成立，再在同一受验证调用中进入 Active 并发布实际持有的槽。
Runtime 不再于每轮 Active 调度复制全部已发布槽；`set` 继续原地更新共享的
`ValueCell`。这里不据此宣称已测得性能提升。

`release_native_execution` 检查值、工作及 publication 的来源一致，再执行真实
排空和 Unload 协议。拒绝时保留生命周期、工作、队列、发布表与 episode 值。
成功时只移除该 owner 的 publication，关闭 episode 的后续读写，并返回实际
持有、导入和发布的槽。宿主在释放记账锁后析构这些值；部分初始化被取消也走
这条路径。保留的清理失败不能释放，重试必须通过已有的新票据协议。已经返回
给用户的 `Arc` 仍是普通引用，不是可撤销租约。

证明采用 Verus 标准库对 `Arc` referent 及克隆的合同，不证明互斥锁同步、引用
计数实现、服务内部可变内容或任意 availability 回调。静态／Node 嵌入继续保留
明确的外部宿主合同；底层生命周期 API 本身也不会自动维护上述原生组合。
生产原生适配器现通过 `NativeRuntime` 使用内部 `NativeHost`，不再暴露可变生命周期或登记 map。共享
Child 句柄、宿主记账字段的语义与完整宿主解释仍需要全局语义不变式。

## 登记与生命周期由同一状态持有

`NativeHost<R, H>` 持有真实 `LifecycleState`，以及实际
`RegisteredPlugin<R>`／宿主载荷对的 map，替代 Runtime 原先独立的
`BTreeMap<PluginId, Mounted>`。它的 `wf` 合同对所有条目建立：

- map 的成员集合恰好等于论文控制投影中的 registered 集合；
- 保存的回调身份与 map 键相同，域与真实生命周期域相同；
- 父插件和解析后的依赖／提供端口与内核的实际声明一致，包含保留的 anchor。

`register` 执行真实 Insert，并在返回前保存传入的回调和宿主对象；
`register_child` 还在同一次操作中写入实际 Child 槽。失败时原样返回两份输入。
`remove` 先通过已有生命周期 Remove 守卫，再返回恰好对应的真实条目，方便在
记账锁外析构。Unload 保留登记的回调，Remove 是另一步骤；其他条目保持不变。

`host_mut` 只借出 `H`，证明任意通过该借用进行的修改都保持登记与控制状态不变。
容器不暴露可变登记或生命周期引用。`replace`、`admit_root` 和 `call` 按 ID 选择
实际保存的登记，保持其他条目，并检查版本与调用身份。所有公开生命周期转换、
原生值组合、Child 退休和压缩操作都保持 `wf`。原生适配器直接从该状态读取未完成
票据，不再维护第二份动作视图 map。存活 ID 枚举证明无遗漏、无重复，并只扫描
存活条目，不扫描历史身份墓碑。

这把 Definition 49–50 的登记／接口部分，以及 Definition 58／63 的控制投影
连接到真实生产存储。这是该投影的保持性结果，**不是完整 Theorem 64**，也不是
完整 R1 context 解释。`H` 仍是不透明载荷：Future 状态、共享句柄、锁同步、
availability 语义与 panic 适配，不会因为容器的成员不变式而自动获得证明。
外部／静态适配器继续保留原有登记边界。

## Effect 请求与实际轮询收据

`effect_work.rs` 把实际 effect 迭代器接到既有清理 owner。
`SetupWork::enqueue_effect` 先检查真实工作 owner、生命周期来源、发起组的取消
状态、请求容量和新清理域，再在同一受验证操作中创建清理组、排队实际迭代器，
并绑定二者身份。拒绝返回原始载荷和绑定向量，两个 owner 均不改变。派发不能
使用其他生命周期或数值 ID 相同的另一清理组激活请求。

`EffectRun` 持有实际迭代器载荷。`admit` 成功后预留递增的轮询身份；回复未完成前，
再次准入或调用不能覆盖它。`call` 把实际保存的载荷和参数交给适配函数，再从
真实返回值构造私有收据。`land` 检查生命周期／组／域和当前轮询身份，才接受结果。
Pending 保留真实 stage 的 pending 状态；Ready 把实际 inverse 或错误交给
`CleanupGroups::land_result`。取消决定是否继续迭代；取消后才产出的 inverse
仍先收集，再停止后续 stage。错误收据原样返回，不改变执行 owner 或清理组。
轮询身份耗尽会拒绝准入，不回绕复用。

真实 Runtime 的 `AsyncSetup::effect`、派发和 `poll_groups` 均使用这些方法。
普通 Rust 中的 `cancelled_groups` 集合已删除；`ensure_active`、嵌套 Child／effect
准入和取消查询直接读取决定 inverse 落地的同一 stage 状态。`EffectHandle::cancel`
仍是协作式请求，驱动把请求记录到 stage 协议后，准入守卫才据此生效。原生与外部 Child
排队也经过该守卫。取消中的在途工作仍可登记 inverse，但不能利用这一点获取
新的 Child 或 effect。

这一段把实际迭代路径接到既有 L-Iter、L-Finish、L-Divert accumulator 解释，
证明结果来源、队列归属和 continuation 选择；回调合同仍需由受验证调用方满足。
传入的 Poll／panic 结果到 `EffectOutput` 的转换现已有下文的受验证合同。
任意迭代器和 inverse 的外部效果、自定义析构、宿主锁调度及不透明可变字段的
语义仍在边界之外。这不是
完整生产轨迹解释，也不证明公平性或全局终止。

## 同一生产执行 owner

`Execution<V, C, G, I>` 现持有真实 `SetupWork`、全部清理队列、实际
`EffectRun<G>` map、借出的 runner 身份、原生服务值和初始化状态。Runtime
不再另存 work owner、phase 字段或迭代器 map。静态适配器也用它管理工作、
清理与 phase，同时保留外部生命周期与服务值的明确边界。

联合不变式连接生命周期来源、清理域与存活组身份，并要求 work、cleanup 与
原生值的关闭状态一致。`begin_managed_execution` 创建这个状态；
`finish_managed_execution` 在同一个受验证调用中发布实际值并进入 Active；
`release_managed_execution` 检查完整排空、关闭 episode 并返回实际值。
Runtime 的直接退休和 restart 撤回使用 `withdraw_managed_execution`，将
控制转换与关闭新工作准入组合，同时保留在途工作和值。Child 触发的退休仍先调用
既有共享 Child 协议，再执行宿主通知。

`take_effect` 在 owner 中留下借出记录。`put_effect` 检查原始存活队列，不能
覆盖已有 runner。`retire_effect` 只有在队列排空后才能消费实际 runner，并返回
真实载荷供锁外析构。即使迭代器 map 暂时为空，借出或放弃的 runner 仍阻止
移除和释放。这是安全守卫，放弃 runner 不代表最终能够恢复。已准入 stage 在取消
后仍可落地其真实 inverse。

这些合同约束实际生产状态与转换，但尚未给出不透明回调效果、可变值内容、
全部宿主记账字段的语义解释，也没有建立整个宿主到 R1 的对应。

## 真实 Poll 结果转换

`normalize_poll` 保留实际 Pending／Ready，捕获到的 panic 只能转成失败。
`normalize_effect_poll` 区分 Pending、迭代结束、返回错误、产出 inverse 和
捕获到的 panic；它只映射一次实际 inverse，不接受调用方提供的预期结果。
Runtime 的根 setup、迭代器和清理轮询使用这些受验证函数；静态宿主复用根 setup
和清理 helper。

标准 `Poll` 的类型规格描述真实枚举的分支，没有假设 `poll`、`catch_unwind`
或回调实现正确。证明从传入转换函数的实际结果开始，不涵盖 panic 捕获机制、
轮询实现、任意回调的外部效果或最终返回。

## 真实可逆服务值与有限程序

[`ReversibleValue`](cases/reversible-values.zh-CN.md) 为三段语义连接增加了具体生产
路径。插件使用 `Setup::update_reversible` 或 `run_value_program`，普通 Runtime
和静态宿主调用同一受验证实现。私有 inverse 保存真实共享目标和捕获的前／后态。
`Execution` 在返回前登记它；`CleanupQueue::dispatch` 直接选取、执行并确认队列
中的实际对象，宿主不传入成功标志。干扰发生后，该 inverse 保留供显式重试。

`operation`、`primitive_theory` 证明替换、检查溢出的加法、异或和比较交换的
实际部分逆操作效果律。观察包含值和嵌套层级，所以后来写入相同值也不会被误认
为状态未变。`Program::component` 证明程序根和每个结果选出的 continuation 都
属于 R1 的完整有限严格载体。插件提供的已验证指令和实际比较结果决定执行路径，
没有预期结果或 transcript 参数。

实际值锁持有 ghost 历史。`history_interpretation` 分类每次写入、成功恢复和
拒绝；`ProgramReport::source_execution` 为完整运行或失败前缀构造连续的
dependent-grammar 轨迹，并保持其他表键不变。全部成功前缀的 inverse 按执行
顺序进入既有清理 owner。Cargo 构建会擦除历史。

这条**具体原语／程序路径**完成了上述连接，并不等于完整宿主 context 已完成。
普通回调、Node 对象状态以及全局联合解释仍属于下面保留的 R2 验收内容。
[中文案例](cases/reversible-values.zh-CN.md)／[English](cases/reversible-values.md)
包含代码、约束映射、故障复现和负向对照。

## 连续的真实生产控制历史

`LifecycleState` 现在与实际 Kernel、动作协议一起持有 ghost `History`。每次基础
控制变更记录真实的前后控制观察。其不变量从空注册表开始，保留之前的前缀，并
以当前真实控制状态结束；`record_control` 不能用调用方给出的预期轨迹替换它。

`control_history_correspondence` 证明整条记录连续，每一步满足论文控制规则、
保持控制观察的内部步骤，或 `control_history.rs` 中明确的扩展。普通失配退出
对应 L-Divert／L-Leave，仍然 coherent 时的强制退出保留 Restart 分类。动态
provision 增删和首次启动前的依赖配置具有精确的接口帧；删除 provision 还要求
没有保留的 commitment 引用该端口。被拒绝的调用和存储压缩保持控制观察。
若历史没有扩展步骤，`strict_paper_trace` 从实际历史推出有限的严格论文控制
执行及其可达性结论。

原生和 Node driver 都使用这个生命周期 owner，动态 Child 插入、托管资源释放
也经过它。历史在 Cargo 构建中擦除。这是完整的**控制投影历史**，还不是整个
R1 context：服务对象内容、回调／函数字段、publication 版本以及值／清理轨迹
仍需组合为共同语义观察。仅修改协议的步骤在控制投影中属于内部步骤，其既有
收据和清理合同继续约束这些修改。

## R2 剩余验收内容

1. 在可扩展的生产插件入口，建立“实参 → 实际执行的操作 → 结果 → continuation →
   真实 inverse”的关系，并由具体原语证明效果律。原生登记与直接 `FnMut` 调用
   现已建立其中的回调／实参／结果这一段；可逆值程序还建立了具体效果／inverse
   律及结果选择的实际代码路径，但普通插件函数体仍未完成。不能改成调用方提供预期结果，或直接
   假设任意回调正确。
2. 用同一受验证的生产状态持有并组合全部并发效果组、动态子插件、publication、
   已准入工作与排空／释放决定。全部清理队列现已有共同的受验证 owner，载荷释放
   也已组合票据／租约验证；根 setup 和请求现已参与生命周期准入、失败、重试和释放。
   真实 Child 分配／退休和一次性槽状态转换现已有合同，原生 publication 与绑定值
   owner 已组合 Begin／Finish／Unload；NativeHost 现还保持实际注册表、回调和
   生命周期接口的对应。原生 Child 配对、共享槽同步和持久终态决定也已有合同。
   `Execution` 现统一持有实际工作、原生值、phase、runner 及借出记录，并组合
   发布、撤回和释放。其他共享宿主记账的语义与完整宿主观察仍需联合不变式；
   结果转换现已单独验证。
3. 证明完整生产执行轨迹的步骤分类及其与 R1 解释的关系，包括明确列出的多版本和
   动态接口扩展。实际可逆值历史及完整有限程序现已有 source 轨迹；两种适配器还共享连续且
   已分类的真实控制历史。它们整体组合后的原生／
   Node 历史仍未完成。列出一些方法的分类本身不构成这一定理。

这些就是既有的 R2 退出条件，并非为了缩小范围而新增或替换的条件。本轮没有
提升原论文条目和四项集成审查的完成状态。

## 审查与复现

八个执行 owner 测试覆盖发布与 phase 原子转换、异域撤回、释放与已关闭上下文、
失败与重试、错误 runner 归还、迟到 inverse、已派发工作，以及放弃根任务或
runner 后仍阻塞。三个 Poll 测试覆盖全部结果分支和不可复制 inverse 的实际所有权。

七个 effect-work 测试覆盖原子分配、实际载荷／绑定、Pending／Ready 收据、取消后的
inverse 收集、跨组和跨生命周期误投、拒绝后的载荷所有权、取消后不再调用迭代器。
Runtime 回归覆盖逃逸上下文、迟到 inverse 登记与落地、停止后续 stage 和保留 owner。
四个负向对照分别错配请求组、绕过取消、接受错误轮询身份或丢弃实际返回的 inverse。

```sh
cargo test -p cordis-kernel --test publication_values --test async_completion --test cleanup_queue --test cleanup_groups --test setup_work --test execution_lifecycle --test plugin_registration --test child_slot --test native_values --test native_host --test shared_child --test effect_work --test execution --test poll_result --offline
python3 scripts/record-development.py --offline
```

八个共享 Child 测试覆盖 FIFO／LIFO 配对、inverse 先于派发、失败与分配终态、
异域／过时准入、拒绝时保留载荷、并发观察／拒绝、已登记身份接入，以及拒绝后
析构重入。另两个 Runtime 回归检查克隆句柄的失败诊断和实际移除期间的身份观察。

六个原生宿主测试覆盖拒绝分配时返回两份实际输入、多 owner 间的宿主修改和回调
更新、错误／异域／旧调用、动态 Child 分配与移除、保留清理失败直到重试和
Unload，以及反复创建／删除和压缩后的存活条目枚举。

七个原生值测试覆盖精确绑定 import、真实共享槽、realm 隔离、重复／异域 Begin、
缺值 Finish、清理失败与重试、旧 publication、已关闭上下文，以及不可复制值延迟
析构。既有 Runtime 回归还覆盖共享值更新、取消 setup 和析构时重新调用上下文。

子插件槽测试覆盖重复分配、inverse 先于分配、分配失败保留、跨 runtime、旧 episode
和移除后的重复退休。四个新增负向对照分别去掉一次性分配检查、代次／父插件存活阶段检查和 Pending
取消动作，均要求指定合同拒绝该错误实现。

定向测试覆盖不可复制载荷、新旧 publication、过时代次、异域、完整清理清单、
Future 逆序完成、工厂调用时机、失败重试、析构所有权、取消后的迟到落地，
以及异域／未绑定生命周期状态、保留 provider 依赖、原子重试、删除组后保留消耗
失败，以及仍有非根组工作时尝试关闭。登记测试还覆盖 realm 隔离、父插件当前
声明、拒绝时返回不可复制载荷、错误／异域 owner、旧回调版本、直接工厂调用、
实际异步失败，以及移除后的 Child 退休。常规开发检查还会重新构建并测试实际
Rust 和 Node 宿主。

四十九个 R2 负向对照分别把真实值改为 `None`、替换租约的 publication 身份、把实际等待到
的错误改成成功、允许已取消的 continuation 继续、从排空检查遗漏非根组，以及
篡改受验证 `invoke` 调用者的实际参数、遗漏已派发请求、取消已经运行的根 Future、
替换为未绑定的清理容器，以及把消耗失败报告为恢复成功。其中五个原生值负控分别
遗漏 committed import、绕过代次检查、不完整发布、替换实际发布值表，或释放另一
episode 的 publication。另三个原生宿主负控隐藏登记、借出另一 owner 的记账
对象，或替换另一 owner 的回调。另三个共享 Child 负控给请求换用另一共享句柄、
拒绝本应合法的分配，或在未修改实际槽时报告退休完成。六个执行／Poll 负控分别
遗漏借出记录、接受异域 runner、遗漏 Active 转换、在队列存活时完成 runner、
把 Pending 变成完成，或丢弃返回的 inverse。定向实验必须先证明未修改版本、
编译错误版本，再确认指定合同确实拒绝该修改。新增五个值／程序对照改变结果分支、
忽略 depth、遗漏 inverse、伪造恢复成功或跳过 continuation；两个控制历史对照
遗漏真实步骤，或把另一个端口的声明归到传入端口。定向通过不表示完整的 184 项负向
回归已运行，详见[验证等级](validation.md)。

绑定源码的开发报告独立记录完整正向检查，不表示发布验收或整篇论文完成。本轮
没有给 Rust 用户增加 Node 依赖，也没有引入时序逻辑库。
