# R2：生产执行路径的合同

[English](r2-execution.md) · [论文里程碑](paper-refinement-roadmap.zh-CN.md)

R2 要把论文约束连接到实际的托管调用。**R2 仍在推进中。** 下列合同已经用于
Rust 和 Node 宿主，补齐了载荷、登记和结果传递的缺口；它们尚不构成整个宿主的语义
refinement，也没有证明任意插件回调满足 Component 合同。

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
原生 setup 现通过 `RegisteredPlugin::call` 直接调用保存的 `FnMut`；iterator 和
cleanup 入口使用这些泛型函数，适配层不传入预期结果。
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
owner，见下节；publication 值、Child 请求／inverse 的共享句柄和完整宿主观察仍需建立联合
语义不变式，因此这些局部组合还不能关闭整个生产状态的验收义务。

## setup 与请求也参与排空

`SetupWork<C, G>` 持有真实的 Child／效果组请求，跟踪根 setup 和已经交给宿主
执行的请求。`WorkItem`、`PendingWork`、`WorkReceipt` 的载荷与身份字段都是
私有的：实际请求经过 `run` 调用后产生结果凭据；异步工厂经过 `start` 后保留
实际 Future，只有该 Future 返回才产生其完成结果。派发队列为空而已交付请求
尚未返回时，整个 episode 仍未排空。队列采用 `VecDeque`，不会在每次派发时
搬移剩余请求；已完成票据退出活跃 map。

Child 请求与对应的真实 inverse 通过 `enqueue_owned_child` 一起登记，拒绝时
二者原样返回，由宿主在释放锁后析构。最终 `seal` 检查根 setup、排队与已派发
请求以及全部清理队列，并检查二者属于同一清理域。Rust Runtime 和静态宿主都
使用该守卫；普通 Runtime 的初始化完成也使用同一组实际状态。

尚未开始轮询的根 Future 可以在撤回后取消。已经开始的 Future 必须返回，或
保留为未确认的放弃状态；它不能走“尚未运行”的取消路径。异步完成保留实际
`Result`，失败不能使初始化成功。异常捕获仍由普通 Rust 适配器报告到只允许
失败的入口；Verus 没有证明该适配器的 poll／panic 对应关系。调用关系也不能
替代插件的效果律，或 Child 请求、共享句柄与 inverse 之间的完整语义关系。

## 登记的回调与原生 Child 操作

`LifecycleState::register_plugin` 现用于 `Runtime::mount_inner`，包括动态 Child 的
真实分配。它消费实际的 `PluginDefinition`，读取父插件在内核中的权威声明，
根据传入的 realm map 解析键，并执行真实插入。返回的 `RegisteredPlugin` 持有
实际回调、解析后的接口和保留的 anchor；`Mounted` 不再另存这些字段的独立副本。

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
原生 Runtime 在现有互斥锁内调用这些操作，拒绝后的回调捕获值析构和后续宿主
退休回调均放在释放锁后。静态适配器仍使用明确的外部分配确认协议。

这些合同已连接真实分配和登记函数调用，但尚未证明完整的 R1 Child 效果：普通
Rust 仍负责把登记对象移入 `Mounted`、在排队请求与 inverse 间复制共享槽句柄并同步访问、适配
panic，以及维护 publication／context 观察。还需要这些操作的联合不变式和具体
插件的效果／inverse 定律。域与服务键分配器的全局唯一性也仍是明确的宿主边界。

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
受验证结果策略。Child 分配／退休与槽状态转换现已有上述合同；共享句柄别名、同步和
普通回调／panic 适配仍需语义对应证明。
面向外部宿主协议的底层显式报告 API 继续存在；收到报告不等于证明外部效果。

Begin、Finish、Unload 的合同连接到已有论文**控制投影**；它们还不是完整 R1 的
值／代码／continuation 解释、完整 Child 效果或整条生产轨迹的证明。静态／Node 桥接
保留各自的外部完成边界，不能把这份原生组合证明自动推广到所有适配器。

## R2 剩余验收内容

1. 在可扩展的生产插件入口，建立“实参 → 实际执行的操作 → 结果 → continuation →
   真实 inverse”的关系，并由具体原语证明效果律。原生登记与直接 `FnMut` 调用
   现已建立其中的回调／实参／结果这一段；不能改成调用方提供预期结果，或直接
   假设任意回调正确。
2. 用同一受验证的生产状态持有并组合全部并发效果组、动态子插件、publication、
   已准入工作与排空／释放决定。全部清理队列现已有共同的受验证 owner，载荷释放
   也已组合票据／租约验证；根 setup 和请求现已参与生命周期准入、失败、重试和释放。
   真实 Child 分配／退休和一次性槽状态转换现已有合同；共享句柄别名／同步、poll／panic
   适配、publication 值与完整宿主观察仍需语义组合。
3. 证明完整生产执行轨迹的步骤分类及其与 R1 解释的关系，包括明确列出的多版本和
   动态接口扩展。列出一些方法的分类本身不构成这一定理。

这些就是既有的 R2 退出条件，并非为了缩小范围而新增或替换的条件。本轮没有
提升原论文条目和四项集成审查的完成状态。

## 审查与复现

```sh
cargo test -p cordis-kernel --test publication_values --test async_completion --test cleanup_queue --test cleanup_groups --test setup_work --test execution_lifecycle --test plugin_registration --test child_slot --offline
python3 scripts/record-development.py --offline
```

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

十八个负向对照分别把真实值改为 `None`、替换租约的 publication 身份、把实际等待到
的错误改成成功、允许已取消的 continuation 继续、从排空检查遗漏非根组，以及
篡改受验证 `invoke` 调用者的实际参数、遗漏已派发请求、取消已经运行的根 Future、
替换为未绑定的清理容器，以及把消耗失败报告为恢复成功。定向实验必须先证明未修改版本、
编译错误版本，再确认指定合同确实拒绝该修改。定向通过不表示完整的 150 项负向
回归已运行，详见[验证等级](validation.md)。

绑定源码的开发报告独立记录完整正向检查，不表示发布验收或整篇论文完成。本轮
没有给 Rust 用户增加 Node 依赖，也没有引入时序逻辑库。
