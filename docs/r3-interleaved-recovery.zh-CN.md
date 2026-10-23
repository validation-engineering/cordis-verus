# R3：外部写入、清理阻塞与恢复

[English](r3-interleaved-recovery.md) · [清理合同](r3-cleanup-recovery.zh-CN.md) · [生产恢复](r3-production-recovery.zh-CN.md)

native 中间截面的完整 publication／owner／pending 观察与恢复现见[第 2 包](r3-observation-recovery.zh-CN.md)。下文相关边界说明限定于本页较早的入口；普通宿主迁移与一般合法删除仍未完成。

生产恢复证明现在覆盖包含外部受管写入、失败清理尝试、外部恢复及后续成功清理的有限
历史。它保留真实的严格逆操作定义域，并允许独立对象的恢复交错执行。**R3 仍在进行**：
结论在明确来源条件下，覆盖本次调用触及的对象在真实 native Unload 时的值。
[共同切点定理](r3-common-recovery-cut.zh-CN.md)现将这些值与已完成的 native Child
端点、已消除的正向注册义务组合起来。一般 publication／pending 恢复及合法生命周期
执行删去仍待完成。

## 运行代码产生的证据

历史使用三种来源：

| 事件 | 真实证据 |
| --- | --- |
| 正向写入 | 实际捕获的 scalar／typed 逆操作，包括真实输入、输出、分配对象及正向 Journal 位置 |
| 受管清理 | `dispatch_payload_cleanup` 实际 completion，包含所选逆操作、前后队列、持锁读取或 scalar 提交及确认 |
| 直接恢复 | scalar `restore_observed` 收据或 typed `restore_observed` 尝试，包括失败 |

普通 `restore` 方法均委托到 `restore_observed`，保持既有行为。额外返回项是供已验证
调用者使用的擦除证据。typed 路径仍区分单调读取版本与可逆语义 head，不增加运行时
历史缓存或 payload 克隆。

逆操作身份包含 Journal、分配对象、捕获的输入／输出和正向位置。成功恢复必须对应
一个尚未消费的真实逆操作，证明不接受宿主另行提供替代的期望结果。

## 为什么允许交错

每次受支持的受管 scalar／typed 写入都会让语义深度增加一层。这来自真实正向合同，
覆盖可扩展 scalar effect，并非对任意回调添加公理。

`recovery_obligations` 证明：可恢复历史中，一个当前可执行的逆操作，必定是**其分配
对象上**最后一个未完成逆操作。若同一对象上还有更晚的逆操作，当前深度就必须更大。
因此可以跨过其他对象上较晚的逆操作，消费当前逆操作。它们修改不同地址，严格定义域
与结果可以交换。无需全局 LIFO，也无需调用方提供交换律。

构造出的恢复记录按以下规则演进：

1. 外部正向写入增加其真实逆操作，并更新观察值。
2. 被阻塞的恢复保留未完成记录和尝试处的值。
3. 成功恢复消费匹配的逆操作，并记录实际恢复值；其他对象仍可有未完成逆操作。

因此，typed 外部同值写入仍可阻塞旧逆操作：其语义 head／depth 已改变。真实外部恢复
之后，重试可以成功，单调 revision 则继续增长。

## 恢复 registered Begin 值

`RegisteredReport::interleaved_progress` 从真实函数保留的队列后缀及已建立的
Begin／返回合同出发。`outstanding` 根据返回证据构造剩余逆操作，`values` 构造投影
值。每个有限前缀都保持恢复到真实 Begin 值的能力。相关逆操作全部消费后，
`interleaved_recovers_begin` 证明构造出的最终值等于 Begin 值。

`linked` 来源条件检查：

- 真实正向操作、恢复尝试及 completion 的合同；
- 同一 Journal 中有序的真实收据前缀和读取位置，从实际 registered 返回开始；
- 跟踪对象上的每次实际输入观察，与此前值轨迹衔接；
- 每次成功恢复对应此前保留的逆操作。

它**不要求**所有尝试成功、每一步之后的逆序列都有定义，或调用方提供最终值。有定义性
来自真实初始队列及保持证明。失败和重复 raw 尝试可以出现，而不会消费另一个逆操作；
队列重试身份与旧回复拒绝继续由既有生产合同约束。

投影覆盖本次 registered 调用触及的对象。其他对象上的外部效果仍存在于真实收据历史
中，但不修改该投影。这里选取的事件证据不宣称枚举了所有生命周期事件；实际读取约束
其解释，无约束的 raw replace、退休或 opaque 回调不会被默认为可逆受管写入。

## 接到真实 native Unload

`release_managed_execution_observed` 只在实际释放成功时返回擦除的 `Unload` 证据，
普通释放入口委托到该方法。构造器从 native 宿主的索引历史取得最后一次真实 Unload
提交及其之前的 owner，包括动作票据和工作域。提交后的 native 记录中，该 episode
owner 及其 publication 均已不存在。释放被拒绝时不会产生证据。

`RegisteredReport::unload_recovers_begin` 将有限轨迹对应到**该真实 Unload 的同一
Journal 检查点**。它核对与保留 Begin 相同的 native 宿主及 episode、收据前缀，以及
每个对象从最后观察事件到 Unload 之间没有新的修改。没有后续事件的对象使用实际函数
返回观察。typed 值通过最后一次真实写入／尝试的来源历史解码；revision 增长不需要
虚构的值或过期历史。

`settled` 历史条件检查：每个初始捕获的逆操作，以及每次相关外部正向写入，都有后续
匹配的真实成功恢复。`drained` 由此证明没有逆操作残留。它利用真实深度规律，证明
消费一个可执行逆操作后，可恢复序列中不可能还残留该逆操作的重复项。整个过程允许
失败尝试，调用方无需直接断言构造的逆操作序列已经为空。

在这些来源条件下，真实 Unload 时解码出的值等于真实 Begin 值。下面的释放组合版本
进一步推出有限历史闭合条件中的本地部分。
如果最后一次恢复后又发生外部写入，尾部无修改条件就不成立。复用插件 id 的其他代际／
工作域，或其他 native 宿主的检查点，也不能替代本次端点。

## 从真实释放守卫推出成功恢复

真实释放路径现在将清理组成员收据保留在 `Unload` 中。native 提交通过既有写锁，
在同一 Journal 中建立它位于该收据之后的因果关系。证据对应实际已封闭的成员表和
episode；清理组成员记录身份沿完整释放调用链保持。收据和因果参数会被擦除，不增加运行时
缓存、克隆或锁。未接入 Journal 或跨 Journal 的执行不会被赋予虚构的共同检查点。

来源证明对应三段实际变化：

| 来源事实 | 推出的结论 |
| --- | --- |
| 真实逆操作注册时该组存在，而封闭成员表中已不存在 | 真实 `Remove` 或 `Seal` 检查过该队列已排空；覆盖在最终 Unload 前提前移除的动态组 |
| 注册槽位曾被占用，而该队列通过排空检查 | Unload 前必有真实非失败 `Complete` 结束该 token；仅 `Pop` 移出或保持失败不足以排空 |
| 该完成事件有真实受管派发确认覆盖 | 实际 scalar／typed 恢复成功；普通回调的 `Drained` 不能替代 |

`RegisteredReport::unload_recovers_from_cleanup` 对每个保留函数步骤的实际插入收据
和逆操作应用这些结果。`covered` 检查真实注册成员关系、收据前缀，以及相关队列／
token 每个消费确认所匹配的实际派发结果。它检查捕获的逆操作身份，但不要求恢复成功。
成功、本地历史闭合及共同 Unload 检查点的值恢复都由证明推出。

这个入口仍将完整确认覆盖作为来源条件。下面的记录历史入口能够从连续维护的真实队列
路径推出该覆盖；跨完整生产生命周期的集成仍待完成。
原始 `pop`／`complete` 接口支持普通回调，不能仅凭队列清空就认证受管恢复。
独立的 `foreign_settled` 条件检查相关外部写入已有真实后续恢复，本地释放不会促成
或调度那些恢复。publication、Child 效果、pending registration 语义和合法执行删去
仍需继续组合。

## 从运行中的解释器取得注册归属

`CleanupGroups::register_following` 现在把自身真实成员记录的所有权凭据，借入队列
已有的 Journal 写入区间。逆操作入队收据因此包含入队当时的存活组 ID、准确队列
key 和工作域。这项观察会被擦除，不增加运行时历史缓存、克隆或锁；未接入 Journal
的队列仍保留明确边界。

scalar 与 typed 生产入口将这些事实传到 `Step::registered` 和 `Report::registered`。
typed 合同还明确将公开 token 与真实入队收据的 token 绑定。已注册 root／Child
派发器为每个实际保留的效果输出这些事实，包括失败前的成功前缀及空调用。

`before_seal` 证明真实存活成员表中的入队，必然早于实际 Unload 使用的封闭成员收据：
成员表封闭后不能重新开放。`unload_recovers_registered` 据此将生产报告给出的成员
归属后置条件用于值恢复定理。调用方提供的数字组 ID 或无关的后续成员快照都不能
替代这项证据。

解释器还输出 `queued_sources`：每次插入都指向实际保留队列的 Journal 和 key。
它将注册证据与下面的真实清理历史相连。

## 从真实派发构造确认覆盖

`History::new` 从实际队列的保留槽位开始。可执行的 `Execution::dispatch_recorded`
调用现有生产混合派发器，并将其输出记录到擦除的证明状态。受管清理失败仍留在日志中，
原始逆操作也继续保留。`retry_recorded` 调用真实重试入口，保持槽位并取得实际产生的
更新尝试票据。被拒绝的重试、空派发和被拒绝的派发都保持记录路径。

对每个最初占用的受管槽位，记录器维护明确的二选一：准确的原始动作仍在槽位中，或有
真实成功受管派发消费了同一队列／token／逆操作。普通回调不能提供这项证据。
`History::frame` 仅在原始受管槽位保持时跟随后续注册等变化；`foreign` 可以记录真实
外部写入或恢复，但不会默默消费本地槽位。`History::extend` 将实际新注册槽位追加到
同一义务记录中，保留已有 token 及消费证据。字段 `initial` 表示各 token 的原始动作，
序列可以增长。恢复证明使用保留的函数返回前缀，不再要求此后没有注册；序列和收据表
均在运行时擦除。

`unique_consumption` 证明已经消费的 token 不能再次被消费，覆盖重试与后续注册。
`Receipt::compare` 使用持久的 tracked 凭据比较同一 Journal 中的真实前缀，不另取锁。
结合释放守卫，证明将记录器中的确认定位为真实 Unload 前必须发生的完成事件。旧回复、
重复回复或普通回调的 `Drained` 都不能补足缺失的受管恢复证据。

`RegisteredReport::unload_recovers_from_history` 因而可以从真实注册报告、连续维护的
记录器及其匹配的已排空终态队列，推出本地确认覆盖。调用方不再需要提供
`cleanup_emitted` 或本地恢复成功前提。在既有值来源、读取顺序、外部恢复闭合与尾部
无修改条件下，真实 Unload 处的值等于本次调用的 Begin 值。

普通移除入口现在委托到 `remove_observed`，仅在成功时返回准确的被移除队列，
并建立其排空守卫。普通 native 释放入口已经委托到 `release_managed_execution_observed`；
其 `ReleaseObservation` 现在将实际结果、真实 Unload 和擦除的释放前清理组放在同一返回中。
被拒绝的释放不会提供端点或终态组。`unload_recovers_from_release` 直接使用这一成功返回，
调用方无需拼装终态队列或另行断言它已排空。提前移除的组则使用其 `remove_observed`
边界，与后续真实 Unload 组合。

## 在生命周期所有者中持续保存历史

`RecordedExecution` 持有真实 `Execution`、函数返回时的基准状态、每个已捕获清理组的
tracked 历史及实际终态队列。后续分配的组也保存其实际来源队列，新增组不会替换
原始函数返回基准。`NativeRuntime::run_recorded_root` 通过既有
`run_managed_root` 执行已注册 root／Child 函数，随后把所有者接到真实返回队列上。
封装只提供只读检查，不提供可变内核借用。

| 可执行操作 | 维护的证据 |
| --- | --- |
| `enqueue_effect`／`enqueue_native_effect`／`register` | 实际新组分配保存来源队列；后续注册追加 token 义务，不重置既有消费证据。 |
| `take_group`／`take_child`／`complete_request` | 实际请求经 `WorkItem` 和同步／等待完成的 receipt 流转；只能完成匹配的未完成 work 身份，队列历史保持不变。 |
| `take_effect`／`put_effect`／`admit_scoped_effect` | 保留借出的执行器身份与真实组 scope；遗弃执行器仍会阻止移除／释放。 |
| `land_effect`／`cancel` | 实际回调回复须匹配组身份与 poll 序号；取消后返回的逆操作仍追加义务，`Pending`、错误或被拒绝的回复不会凭空产生逆操作。 |
| `enqueue_owned_child`／`enqueue_native_child` | 请求与逆操作原子入队；native 准入为请求、逆操作和返回句柄构造同一个共享分配。尚不推出 Child 终止或其效果已恢复。 |
| `run_function` | 实际解释器的完整成功前缀（包括失败前缀）追加逆操作义务，每个真实正向值事件进入所有保留组的历史。同 Journal 写入遵循保留的调用或清理边界，真实返回检查点包含本次写入、登记和失败收据。 |
| `dispatch` | 真实混合派发结果进入本组历史，受管结果也进入其他保留组历史。实际 Pop 晚于保留恢复边界，实际成功或失败确认成为下一边界。 |
| `retry`／`retry_native` | 单队列或真实 native 动作重试保留逆操作、队列身份和已有观察；native 重试生成新的生命周期动作票据，并为每个失败队列生成更大的 attempt。 |
| `complete_result`／`complete_future` | 只有已发出的宿主动作能接受宿主确认；重试载荷的类型不包含受管逆操作。旧／重复回复或回调 `Drained` 不能消费受管义务，Future 入口保留实际等待结果与 ticket 的绑定。 |
| `finish`／`withdraw` | 既有 native 发布或撤回操作直接使用持有的 Execution，历史继续对应实际队列。 |
| `remove`／`retire_effect` | 成功提前移除或退休已借出的执行器时保留准确的排空队列；拒绝时所有者保持不变。 |
| `release` | 实际 native Unload 将释放前已排空队列与提前移除的队列一起保留；拒绝时不产生终态队列或 Unload 证据。 |

共享不变式将每个已记录组对应到存活队列或保留的终态观察。
`unload_recovers_from_owner` 直接借用所有者中保存的历史与终态队列，使用这条路径的
调用方不再单独携带记录器，也无需向恢复定理提交排空快照。这些历史、遍历与快照都会
擦除；运行时操作仍调用既有生产实现。

普通 Rust 宿主尚未全面迁移。work 派发、执行器借出／准入／落地、取消、Child 准入及
执行器退休现已有显式维护不变式的接口；没有通过 `DerefMut` 或未经检查的修改绕过
历史。[Child 端点桥](r3-child-recovery.zh-CN.md)现已将保留的 native 逆操作关联到真实
退休和它自己的 Unload。原生运行时现自动收集实际共享槽出生、退休及 managed
Unload，完整性按创建者执行的每个原始 native 逆操作检查。[共同切点定理](r3-common-recovery-cut.zh-CN.md)
现将这些端点与调用值及已完成注册组合。
宿主确认本身不等于 Child 已释放，也不等于回调的外部 I/O 成功。

后续受管 `run_function` 调用现在会自动收集真实正向值观察、保留逆操作，并保持原始
函数返回基准。报告提供实际参数、续体选择、失败前缀及注册来源。通用注册或不透明
迭代器输出本身不建立外部效果的正向语义合同。外部观察完整性、外部恢复闭合与尾部
无修改仍是定理条件；`observe_foreign` 仍是显式外部观察入口。通过 `finish` 发布值
不等于已证明 publication 或动态 Child 效果的恢复；一般 pending registration 组合仍待完成。

### 受管调用与清理之间的真实边界

对于 `NativeRuntime::begin_managed_execution` 返回的执行，`run_recorded_root` 将真实
已注册返回凭据保留为首个 `recovery_boundary`。证明使用 native Begin 给出的同 Journal
等式；未接入或来自其他 Journal 的执行不会被赋予虚构边界。后续 `run_function` 将
该 tracked 凭据的副本交给既有 `run_function_following`，实际同 Journal 写入因此晚于
上一调用或受管清理边界。

返回时，`Execution::observe_execution_following` 取得一次真实 Journal 读锁，在同一
读取周期确认实际 work、cleanup 状态，并包含报告中属于该 Journal 的收据。此检查点
成为下一边界，包含成功写入、逆操作登记及已记录的失败收据；空调用也继续传递前驱。
准入拒绝保持整个所有者。生命周期／work／effect 操作保持边界；受管清理使用下述实际
确认推进边界。

`Report::covered_by`、`after_call_receipts`、`after_call` 和 `extend_boundary` 组合这些
真实返回，推出后续同 Journal 写入晚于此前写入、登记和已记录失败。正向事件的读取切点
不早于前一边界长度。该结论不要求前次调用成功或非空，覆盖关系可以沿有限个调用继续
传递。收据与保留字段会擦除；返回观察增加一次真实 Journal 读取，不新增 Journal 事件
或运行时历史缓冲区。

记录派发入口通过 `dispatch_recorded_following` 将同一前驱传给真实队列 Pop 提交。
scalar／typed 恢复遵循该实际派发凭据，包括持锁读取和失败尝试。实际清理确认成为下一
`recovery_boundary`；重试保持该边界，下一次派发或受管调用继续这条链。未接入队列、
其他 Journal 中的恢复仍保留明确的域边界。

`Dispatch::follows_boundary` 给出确认顺序，以及同 Journal 恢复的读取切点和检查点
前缀。`Report::before_cleanup` 进一步推出它们晚于上次返回所覆盖的全部本地收据。
结合 `extend_boundary` 和既有调用合同，可组合有限的受管调用／清理序列，包含失败、
空调用和重试。清理复用现有 Pop 写锁周期，前驱与保留确认会擦除，不增加清理锁或
运行时历史缓冲区。

这些合同建立了受管操作之间的顺序，但不会收集所有外部修改、证明读取值必然符合预期，
或为不同 Journal 构造共同时间轴。完整外部观察、值衔接、外部恢复闭合及尾部无修改，
仍是 `linked` 和 Unload 定理的前提。

### Native Child 退休与实际释放

真实 `NativeRuntime::retire_shared_child` 入口现已导出共享槽决策和生命周期转换：
Pending 分配被取消；已分配且仍注册的 Child 执行 `Retire`；失败保持状态。注册配方、
publication 与 Episode 所有者都保留。该合同不会把成功退休请求视作清理完成。

`retire_shared_child_observed` 现保留持久槽位决策和真实 native 收据。
`retire_and_release_child` 检查实际 Episode，组合退休与带守卫的释放，使 Unload
同时晚于退休和清理封闭。产生的 Child 专属端点证明 owner／publication 已移除及
consumer 守卫成立；取消则排除后续分配。[Child 恢复说明](r3-child-recovery.zh-CN.md)
记录可执行用法、来源合同及出生／退休／Unload 自动收集。出生保留实际父动作与 work
domain；完成查询使用全部记录组的原始逆操作来源，父插件排空不等于 Child 完成。
[共同切点组合](r3-common-recovery-cut.zh-CN.md)现将被覆盖的 Child 端点跨越任意 native
活动，接到同一实际检查点上的值恢复及本次正向注册完成。跨中间切点的一般
publication／pending 恢复仍待完成。

[native 运行回归](../crates/cordis-kernel/tests/native_runtime.rs)中的
`child_retirement_acknowledgement_does_not_release_a_consumers_provider` 执行了真实路径：

1. 父插件创建 Child，Child 发布服务，consumer 捕获该服务。
2. 父插件的 native Child 逆操作请求退休并获得确认。Child 没有依赖父插件的服务时，
   父插件可以卸载，而 Child 仍处于 Active 并保留 publication。
3. Child 退休并撤回后，新查询看不到服务；consumer 的已提交依赖和值仍保留，Child 的实际
   清理与释放被拒绝。
4. consumer 清理失败时仍保留这些资源；真实新票据重试及 consumer 释放成功后，Child
   才能清理并产生自己的实际 Unload。注册表 Remove 另外检查。

此场景检查了恢复组合所需的区别：父插件的确认或 Unload 不能替代 Child 自己的
`release_managed_execution_observed` 证据。合法剩余执行构造在删除创建者 Episode 时，
必须处理 Child 的出生和 consumer 的准入。该构造及完整 Child／publication 恢复仍待完成；
这里没有假设 Child 最终终止，也没有宣称一般合法删除已证明。

## 从真实执行所有者推出外部恢复闭合

[被观察所有者恢复路径](r3-observed-recovery.zh-CN.md)将每个返回步骤绑定到原始注册队列／
token。可执行 `run_function_observed` 和 `dispatch_observed` 将实际正向写入及受管尝试
追加到双方历史，保持已有观察覆盖与同 Journal 边界。随后从外部所有者保留的终态组和
槽位保留合同推出成功恢复，无需调用方提供成功列表。组合入口
`unload_recovers_from_observed_owners` 在共同 native 切点使用这些来源。完整相关来源
覆盖及既有值轨迹／Child 条件仍然明确。

## 审查与验证

Child 场景覆盖父插件先卸载、Child 被 consumer 阻塞、consumer 清理失败／重试，
以及通过新入口执行的 Child Unload 和单独 Remove。另检查替换为父插件执行、重复释放、
已退休端点上的 Begin，以及 Pending 取消后的迟到派发（不分配 Child、不产生 Unload）。
清理顺序负向控制还需拒绝丢弃 Pop 前驱、替换确认、忽略失败边界和虚构跨 Journal 顺序。
Child 控制需拒绝用退休、父插件 Unload 或其他 Episode 替代真实端点，替换共享来源／
native member／父插件，遗漏退休或清理封闭前驱，拒绝后伪造完成，以及取消后分配。
这些新增控制尚待验收；运行拒绝案例不能替代证明变异检查。

- [managed_interleaving.rs](../crates/cordis-kernel/src/managed_interleaving.rs)：来源
  载体、实际收据／读取条件、初始保留队列及 registered 有限历史恢复。
- [managed_interleaving_completion.rs](../crates/cordis-kernel/src/managed_interleaving_completion.rs)：
  真实后续恢复覆盖，以及逆操作记录已全部消费的推导。
- [managed_release_path.rs](../crates/cordis-kernel/src/managed_release_path.rs)：
  来源覆盖、本地成功推导及 `unload_recovers_from_cleanup`。
- [managed_release_membership.rs](../crates/cordis-kernel/src/managed_release_membership.rs)：
  实际入队成员归属、早于封闭的顺序及 `unload_recovers_registered`。
- [managed_cleanup_history.rs](../crates/cordis-kernel/src/managed_cleanup_history.rs)：
  实际派发／重试的记录入口，以及保留槽位的守恒。
- [managed_lifecycle_history.rs](../crates/cordis-kernel/src/managed_lifecycle_history.rs)：
  真实 Execution 所有权、连续派发／重试历史、跨组观察、动态组来源、后续注册及提前移除边界。
- [managed_lifecycle_callbacks.rs](../crates/cordis-kernel/src/managed_lifecycle_callbacks.rs)：
  限定宿主重试载荷、同步／实际等待结果确认，以及与受管逆操作消费的隔离。
- [managed_lifecycle_work.rs](../crates/cordis-kernel/src/managed_lifecycle_work.rs)：
  实际 work receipt、执行器借出／scope／落地及排空后的退休。
- [managed_lifecycle_children.rs](../crates/cordis-kernel/src/managed_lifecycle_children.rs)：
  Child 原子准入、保留的逆操作义务，以及创建者 Episode 与实际取消／Child 释放的关联。
- [lifecycle_state/native/runtime/child_recovery.rs](../crates/cordis-kernel/src/lifecycle_state/native/runtime/child_recovery.rs) 与
  [lifecycle_state/registration/shared_child.rs](../crates/cordis-kernel/src/lifecycle_state/registration/shared_child.rs)：持久槽位决策、真实
  退休／Unload 组合及普通 Rust 入口。
- [lifecycle_state/native/runtime/child_history.rs](../crates/cordis-kernel/src/lifecycle_state/native/runtime/child_history.rs)、
  [lifecycle_state/native/runtime/child_history/completion.rs](../crates/cordis-kernel/src/lifecycle_state/native/runtime/child_history/completion.rs)
  和 [managed_child_completion.rs](../crates/cordis-kernel/src/managed_child_completion.rs)：
  自动出生／退休／Unload 来源、已提交前缀覆盖及创建者原始 native 逆操作的完整性。
- [managed_lifecycle_function.rs](../crates/cordis-kernel/src/managed_lifecycle_function.rs)：
  后续实际受管调用、返回检查点及调用／清理收据组合。
- [cleanup_recovery.rs](../crates/cordis-kernel/src/cleanup_recovery.rs) 与
  [payload_cleanup.rs](../crates/cordis-kernel/src/payload_cleanup.rs)：真实
  Pop／恢复／确认的因果关系及同 Journal 读取边界。
- [execution.rs](../crates/cordis-kernel/src/execution.rs)：
  `observe_execution_following` 在同一读取周期确认实际所有者状态与收据包含关系。
- [managed_lifecycle_native.rs](../crates/cordis-kernel/src/managed_lifecycle_native.rs)：
  已注册 root 接入、Finish、撤回、native 重试及 Unload。
- [managed_owned_release.rs](../crates/cordis-kernel/src/managed_owned_release.rs)：
  直接使用生命周期所有者所存证据的恢复定理。
- [managed_history_release.rs](../crates/cordis-kernel/src/managed_history_release.rs)：
  推导确认覆盖、`unload_recovers_from_history` 及直接消费成功 `ReleaseObservation`
  的组合定理。
- [group_release_history.rs](../crates/cordis-kernel/src/group_release_history.rs) 与
  [cleanup_release_history.rs](../crates/cordis-kernel/src/cleanup_release_history.rs)：
  真实移除／封闭守卫，以及由此定位的先前 token 完成事件。
- [managed_interleaving_endpoint.rs](../crates/cordis-kernel/src/managed_interleaving_endpoint.rs)：
  真实终点解码、尾部无修改条件及 `unload_recovers_begin`。
- [lifecycle_state/native/runtime/episode.rs](../crates/cordis-kernel/src/lifecycle_state/native/runtime/episode.rs) 与
  [lifecycle_state/native/runtime.rs](../crates/cordis-kernel/src/lifecycle_state/native/runtime.rs)：真实成功释放、索引
  owner 来源和擦除的 Unload 证据。
- [recovery_obligations.rs](../crates/cordis-kernel/src/recovery_obligations.rs)：深度
  约束、从历史推出的单对象顺序及逆操作消费。
- [reversible_value.rs](../crates/cordis-kernel/src/reversible_value.rs) 与
  [payload_inverse.rs](../crates/cordis-kernel/src/payload_inverse.rs)：真实
  `restore_observed` 入口及正向来源规律。

值存储、清理、Execution、work／effect／Child、宿主状态、生命周期动作及 native 恢复路径的
组合定向 Verus 验证通过，范围包含分配身份新鲜性、共同切点组合及跨所有者观察恢复：
**1,455 verified，0 errors**（`is-verifying-entire-crate: false`）。
`cordis-kernel` 与 `cordis-verus` 宿主的全部目标、全部功能 Clippy 通过。
既有 `managed_function`、`native_runtime`、`cleanup_groups`、`cleanup_queue`、
`execution`、`async_completion`、`effect_work`、`setup_work`、`shared_child`
九个套件共 **84 项测试通过**。混合别名回归覆盖真实 root 返回、Finish／Restart、
动态效果组、等待中的 work、后续受管调用（包含失败前缀及其后的空调用）、Child 原子登记、取消后逆操作落地、
拒绝未排空执行器退休、成功提前退休、同步／等待的宿主确认、失败保留、拒绝释放、
生成新动作／attempt 票据的 native 重试、成功 Unload 及拒绝重复释放。
新增双所有者案例覆盖失败调用前缀、typed 同值干扰、原执行释放被拒绝、外部所有者实际
恢复与释放，以及原执行的新票据重试。这些运行检查不等于建立组合证明的完整来源覆盖和值轨迹前提。格式、论文清单／
refinement／审查索引一致性及文档本地链接检查通过。这些是定向开发检查，不是全内核、发布或整篇论文验收。

复现该范围：

```sh
source scripts/toolchain-env.sh
./scripts/verify.sh --verify-module reversible_value \
  --verify-module cleanup_groups --verify-module cleanup_queue \
  --verify-module execution --verify-module lifecycle_state \
  --verify-module lifecycle_actions \
  --verify-module setup_work --verify-module effect_work \
  --verify-module setup_context --verify-module host_status \
  --num-threads 2 --triggers-mode silent --output-json --time
CARGO_INCREMENTAL=0 cargo clippy -p cordis-kernel -p cordis-verus \
  --all-targets --all-features --locked --offline -- -D warnings
CARGO_INCREMENTAL=0 cargo test -p cordis-kernel \
  --test managed_function --test native_runtime --test cleanup_groups \
  --test cleanup_queue --test execution --test async_completion \
  --test effect_work --test setup_work --test shared_child --locked --offline
```

集成验收时，扩展既有外部写入／重试回归，保留 raw 尝试证据；补充丢弃外部逆操作、
消费失败尝试、替换正向身份或绕过实际输入观察的负向控制。覆盖多个外部写入者、typed
同值写入、别名、独立对象及重复失败。补充真实 Begin／返回／失败／外部恢复／重试／
Unload 的贯通证明调用者，以及替换 episode 或 native 宿主、恢复后再写入、遗漏未完成
逆操作、替换 typed 来源历史的负向控制。覆盖提前退休的动态组、实际成员表之外的
注册、遗漏消费确认、改变逆操作身份、普通回调 `Drained`，以及未接入／跨 Journal 的
释放来源。还需拒绝保留入队收据却替换 typed token，以及注册时观察其他组所有权凭据的
变体。记录器还需覆盖遗漏受管消费、替换队列／key／token／逆操作、重复确认、失败后
重试、后续注册及独立外部事件；普通回调的 `Drained` 不能解除原始受管槽位的义务。
被拒绝的移除／释放必须不产生终态证据；提前移除和最终释放应保留各自准确的调用前队列边界。
还需覆盖所有者中动态新增组、消费前缀后追加注册、向其他组记录失败派发、提前移除后最终 Unload、
被拒绝的 native 重试，以及绕过所有者历史或替换基准状态的变体。分别检查生命周期
动作票据和各队列 attempt 的新鲜性。拒绝追加时重置原始前缀、复用已移除组身份、
遗漏后续受管逆操作、绕过宿主 issued 不变式，以及接受旧 Future 结果或将受管逆操作
作为宿主重试载荷。还需拒绝伪造 effect 回复／组／poll 序号、丢弃取消后返回的逆操作、
完成外部或重复 work、退休未排空或遗弃的执行器、替换 Child 请求共享槽，以及遗漏
后续受管调用的成功前缀或正向事件。调用边界控制还应拒绝丢弃前驱、替换为无关返回收据、
跳过实际读锁中的收据确认、遗漏失败前缀收据，以及假设跨 Journal 顺序；覆盖夹杂空调用
和准入拒绝的调用序列。清理顺序控制还应拒绝在 Pop 丢弃前驱、替换确认、忽略失败
尝试边界或假设跨 Journal 读取顺序。Child 控制应拒绝用退休、父插件 Unload 或其他
Episode 替代真实 Child Unload，替换共享槽／native member／父插件，遗漏退休或清理
封闭来源，以及在拒绝后伪造完成或取消后继续分配。[Child 来源收集清单](r3-child-recovery.zh-CN.md#验证与剩余工作)
另补充遗漏来源、父身份、前缀及完整性变异。运行拒绝案例不能替代证明变异控制。
新控制与完整开发验收仍待进行；全量负向回归／校准保持 `not_run`。

## 剩余边界

共同切点组合之外的一般 publication／pending 恢复及合法生命周期执行删去仍待完成。
注册成员关系已由真实受管执行给出；受管所有者已在支持的生命周期操作中维护记录器，
并构造本地确认覆盖。普通宿主全面接入及完整外部效果观察仍待完成。Child 出生／退休／
Unload 来源现已自动保留，并按创建者执行的原始 native 逆操作检查完整性；共同生产
恢复切点已由[限定范围定理](r3-common-recovery-cut.zh-CN.md)组合 Child 的 native 终态、
调用值和已完成正向注册；跨中间切点的完整 publication／pending 语义仍待完成。受管调用与清理的边界来自实际返回、Pop 派发及确认，限定为
同 Journal。Child 端点桥已组合真实退休决策和该 Episode 自己的成功 Unload；单独退休
仍保留 publication 与 Episode 所有者。外部恢复闭合现可从被覆盖的记录所有者及其真实终态组推出；任意外部历史仍需独立的
闭合证据。本地释放不会迫使另一个所有者排空。合法保留执行的构造也是一般恢复的独立部分。这里不推出调度公平、外部
最终恢复或最终重试。原论文审查结果和 R3 退出条件保持不变。
