# R2：Node 协议执行历史

当前 R2 状态以[第 5 包统一验收](r2-acceptance.zh-CN.md)为准：managed-production/v1 范围已完成。下文保留各批次历史记录及其当时的验证范围。

## 历史实施与验证记录

[English](r2-node-execution.md) · [执行合同](r2-execution.zh-CN.md)

[宿主组合包](r2-host-composition.zh-CN.md) 现由受验证 `Bridge` 拥有真实 Node-API
弱引用、Fiber 绑定和保留回调配方；强类型导入携带真实查询签发的封闭结果。这补齐了
先前检查点中的引用关联缺口；JS 对象内部状态与完整生产步骤 refinement 仍是明确边界。

生产 Node Driver 现在使用一个受验证的 `NodeRuntime`，持有真实生命周期、publication
句柄与版本、lease、availability 检查、需要检查的 publication 集合，以及保留的 admission 和
episode 状态、实际存活的 callback scope、撤回后的 publication 回读选择，以及待交付的
句柄回收候选、实际接口描述、动态声明归属和冻结的 profile 策略。操作入口把
实际参数、结果和前后观察追加到同一条擦除历史；Driver 不能可变借用其中的独立所有者。
证明不在运行时保留旧 JS 对象，也不增加运行时事件日志。

## 保证与审查路径

| 行为 | 实际路径 | 检查的关系 |
| --- | --- | --- |
| 替换服务槽 | `Driver::set` → `NodeRuntime::replace` → `PublicationStore::replace_checked` | 实际句柄与版本一起变化；生命周期、publication 身份、owner 与租约保持。 |
| 接受或判废检查回复 | `check_actions`／`CompleteCheck` → `request_check`／`complete_check` | 请求捕获真实值／版本，回复检查同一所有者的当前生命周期、publication 与检查状态；已消费或失效回复不能授权新的结果。 |
| 开始 consumer episode | `drive` → `NodeRuntime::begin` → `Availability::begin_setup` | 同一次调用检查可用性、捕获准确 provider／publication、记录 Begin 并获取对应租约；实际 `Admission` 按同一个 consumer ID 保留在内核中，只返回 setup 票据；新的 Begin 不能覆盖尚未释放的 admission。 |
| 清理失败、重试与释放 | `complete`／`retry_cleanup` → `cleanup`／`release` | 失败保留资源；成功释放使用保留的 admission 租约及从真实 registry 构造的完整 publication 清单；此所有者拒绝直接控制释放，防止绕过资源协议。 |
| 准备、失败、重启与封闭声明 | `prepare`／`fail_episode`／`restart`／`seal` → `episode_command`；`complete` → `complete` | 真实标志和错误文本进入同一历史；旧回复保持它们不变，失败与重启阻止 Finish，重试只有在协议签发新票据后才清除清理失败门槛。 |
| 回调开始、结束与等待 | `NativeInvocation` → `begin_invocation`／`finish_invocation`／`invocation_live`／`check_invocation_wait` | 实际 receipt、查询参数／结果和当前已提交依赖图进入同一历史；结束只核销自己的 receipt，旧代次的存活 scope 不能授权等待。 |
| 捕获、撤回与释放 publication | `withdraw_publications`／`release_owned`／`release_owned_reservation` | 捕获来自实际可见的自有槽位；批量撤回隐藏全部保留槽位，保持载荷和租约；释放清单包括不可见旧版本，排除已 reclaim 和其他 owner 的槽位。 |
| 交付回收的 JS 句柄 | `Driver::command(Drive)` → `NodeRuntime::drain_released` → JS `Domain._pump` | 成功替换／reclaim／释放将真实旧载荷入队；交付检查所有当前槽位，包括不可见槽，消费候选并保持顺序与重复次数。 |
| 读取实际服务 | `Resolve`、typed import 与调用授权 → `NodeRuntime::resolve` | 精确的已提交／自有／清理／root 选择及真实载荷／版本进入历史；拒绝旧代次，保持全部状态。 |
| 修改动态声明、接管初始 publication | `publish`、`configure`、`reconcile_publications`、`drive` | 声明变化与 generation-zero 接管显式记录；接管保持载荷／版本、publication 身份和既有租约。 |

可执行所有者见 [`node_runtime.rs`](../crates/cordis-kernel/src/node_runtime.rs)，
转换关系与区间证明见 [`node_history.rs`](../crates/cordis-kernel/src/node_history.rs)。
普通 [Node 适配层](../crates/cordis-driver/src/node.rs) 翻译错误和序列化票据，
[`availability.rs`](../crates/cordis-driver/src/availability.rs) 只保留 availability 诊断文本。内核私有 map 保存真实 `Admission` 和
[`Episode`](../crates/cordis-kernel/src/node_episode.rs) 载荷，适配层只读访问；
待处理票据直接来自 action ledger，不再另存 Node 票据缓存。

`History::replacement_rejects_old_check` 沿真实请求、成功替换和最终回复证明，任意其他
已记录调用交错其中，版本单调性仍使旧回复失效。即使句柄经历 A→B→A，回到相同句柄也
不等于回到旧版本。已缓存的可用性接受仍遵守 Cordis 的显式通知策略：替换值本身不会
安排新的 predicate 求值。

四条有限历史合同把所有权接到执行：

- `admission_origin`：每个保留的 admission 都来自同一历史中的真实成功 Begin，捕获其实际来源观察。
- `admission_retained`：在自己的受管释放成功前，其他操作保持同一 admission，包括失败、重启与重试。
- `rejected_reply_preserves_episode`：被拒绝的清理／setup 回复不改变 admission、状态或错误载荷。
- `release_has_origin`：成功释放消费真实 Begin 产生的 owner，并检查其原代次及实际清理／资源守卫。

实际 [scope 所有者](../crates/cordis-kernel/src/node_scopes.rs) 还证明
`scope_origin`、`scope_retained`、`scope_block_has_origin` 和
`finished_scope_stays_inactive`。存活 receipt 必须来自同一历史中、当时代次下的真实签发。
清理与释放不会隐式结束回调；迟到的结束仍可核销原 receipt，但等待必须检查当前代次及
已提交依赖／ownership 关系。准备和清理回调也可签发 scope；这不声称每个回调都持有
活动 admission 或服务租约。

[资源路径](../crates/cordis-kernel/src/node_resources.rs) 证明 `publication_origin`、
`restoring_origin`、`released_publication_has_origin`。释放清单直接按分配顺序扫描真实
registry 构造，不再使用每个 Node 的重复缓存；清单包含保留的不可见旧版本，实际释放
仍先检查代次、清理成功和全部存活租约。清理回读选择必须来自真实可见槽位，显式 revoke
或 reclaim 会移除相应选择；清理失败保留其余选择和资源，释放成功才移除它们。
批量撤回还证明原历史前缀保留，全部选定槽位被隐藏，而载荷、版本和租约保持。
扫描只分配临时 ID 向量，不增加运行时证明日志或历史载荷副本。

实际[句柄交付路径](../crates/cordis-kernel/src/node_handles.rs) 现持有原先 Driver 的
`released` 队列。替换、reclaim 或释放槽位的同一次转换将实际旧载荷入队；被拒绝操作和
相同值替换不产生候选。`removed_is_queued` 证明反向义务：槽位丢失旧载荷时，不能漏掉
对应回收候选。`payload_origin`、`queued_handle_origin`、`delivered_handle_origin`
把交付的每个数字追溯到同一真实执行中的成功写入与之后的替换／释放。
`queued_until_drain` 则证明失败、重试、旧回复和无关调用不会在显式交付前丢弃候选。

交付结果是对真实队列按真实载荷表执行的精确有序筛选。**任何**槽位仍保留的句柄都不能
交付，包括撤回但未释放的版本；证明不要求数字句柄全局唯一。被筛掉的候选也被消费，
剩余引用之后被移除时重新产生候选，因此 A→B→A 会在交付时保留 A。多个候选可能产生
重复通知，延续既有行为；JS `Map.delete` 可重复调用。这不是进程故障下的恰好一次交付
保证。队列是从 Driver 移入内核的既有运行状态，不是运行时证明日志。

发布与替换检查同一个所有者的 episode 准入，generation-zero 写入要求已准备。
准备阶段与 generation-zero 清理也使用同一状态所有者。失败保留准备状态和 publication
清单义务；在 reservation 清理中，只有资源成功释放后才清除准备状态，首次成功 Begin
则把准备阶段转入新保留的 admission。这些是与论文 Begin／Unload 控制投影
并列的实现扩展合同。

`History::control_classified` 将每个完整事件的**控制投影**接到既有论文／控制历史。
Begin、Finish、Unload 使用既有论文规则；动态接口、reservation 接管和强制一致性
restart 保留明确的扩展含义。值或检查事件可以保持控制不变，同时改变完整观察。
这不等于证明它们是完整 context 的论文 stutter，也不等于任意 Component 函数证明。

## 实际读取与论文的连接

[`NodeRuntime::resolve`](../crates/cordis-kernel/src/node_reads.rs) 现在执行原先由
`Driver::resolve` 实现的选择逻辑。JSON 命令、Rust／Node typed import 和调用授权路径
都使用同一操作：检查实际注册状态和可选代次，返回真实句柄及版本，将请求／结果记入
擦除历史，保持全部受管状态不变。线协议仍返回 publication、owner 和 value；Rust 结果
还保留准确的选择来源。

| 读取上下文 | 选择规则 |
| --- | --- |
| 无所属 consumer 的查询 | 选择当前可见 publication，要求 owner 为 active 且未 retired；不获取 consumer lease |
| 已准入 consumer | 优先使用实际 Begin 资源中首个匹配项的保留租约，即使同名位置已出现另一 publication |
| 没有已提交匹配项的自有服务 | 选择当前可见自有 publication，包括准备／setup 阶段 |
| 自有清理回读 | 选择真实撤回捕获中最后一个仍保留的匹配项，不读取新出现的外部 provider |

`admission_leases_live` 从完整执行历史推出租约仍然存活并属于原 admission；其他
episode 的成功释放不能消费这些租约。`committed_read_origin` 把读取的 port／provider
接到真实 Begin 及其当时的依赖声明。`committed_selection_retained` 证明自己的释放
成功之前，任意已记录调用（包括失败清理与重试）不会让读取悄悄改绑新 publication。
保持的是槽位身份，不是旧载荷：同一槽位内的合法替换仍会被后续读取看到。

`restoring_read_origin` 将清理回读追溯到该 owner 真实捕获的可见 publication；
`read_has_origin` 将返回句柄追溯到实际 publish／replace。`read_context_lift` 将实际
结果对应到定义 29／公式 (31) 在调用方句柄表上的只读操作：正向和逆向均为恒等，
整个已记录观察不变。这个按调用方解释的表包含保留绑定，与全局当前可见表不同。
它解释句柄读取，不解释 JS 对象方法、任意回调效果或完整 Component 程序体。

回归串起 setup、同名多版本、租约下替换、撤回、清理失败、旧回复、重试、成功释放
与新代次，并检查 generation-zero 接管。三个新增可编译反例分别替换返回载荷、
忽略代次校验、绕过已提交绑定分支。它们属于开发定向控制；源码绑定开发记录与
全量负向验收仍分别记录。

## 实际接口与动态 provider 交接

[接口所有者](../crates/cordis-kernel/src/node_interfaces.rs) 现在持有
`NodeRuntime::{interfaces, dynamic}`。Driver 直接读取真实 parent、初始 provisions 和
当前 dependency 向量，不再另存 Node／接口或声明表。Insert、成功的依赖重配置、声明
释放和 Node 移除，与生命周期变化在同一个记录操作内更新这些字段；失败保持对应字段。
移除 Node 时只原地删除它自己的动态声明。

`interface_correspondence` 从实际历史推导成员关系、parent 和依赖与论文控制投影一致；
`mount_origin` 保留真实初始声明要求，`dynamic_correspondence` 与 `declaration_origin`
将每个动态所有者连接到仍存在且确实声明该端口的 fiber，以及真实成功声明。
初始 provisions 是 mount 的要求，不是当前动态接口的另一份副本。这些事实由真实空初态
及记录调用推导，不由适配层作为假设提供。

`Driver::publish` 现在调用 `publish_service`。精确轨迹涵盖准入、可见冲突、容量拒绝、
声明返回及真实 publication 结果。只有已跟踪动态 reservation 存在，才允许容忍声明
冲突。这保留了一个合法过渡：新 publication 已可见，但 consumer 仍提交于旧声明所有者；
不会把新 publication 的 owner 与旧 commitment 混为一谈。

完整协调循环现位于验证代码 `reconcile_declarations`。`ports_cover` 枚举开始时的全部
动态端口，`batch_result` 将每个真实端口调用及失败组合进同一连续历史；成功返回必须覆盖
完整列表。声明释放遇到 `Relied` 时保留归属，其他错误停在真实已执行前缀。
`reconciled_transfer` 要求实际可见且允许准入的后继，并要求先成功释放旧 reservation；
`release_requires_drained_commitments` 证明释放时没有仍指向该 owner／端口的提交依赖。
清理 dispatcher 同时导出每种命令的精确控制投影，拒绝保持该投影。

动态声明与依赖改变仍是论文固定接口生命周期的明确**扩展**。这里补齐实际 reservation
与控制语义的连接，不证明任意 JS 对象、回调效果或完整配置／Component 解释。

本实现批次使用定向 Verus 与全工作区编译／lint；新增运行场景和严格负例保留在
[集中验收清单](r2-state-inventory.zh-CN.md)。源码改变后，上一份开发
报告只属于历史证据。本批次尚未重跑完整开发、完整负例及发布／平台验收；这些局部合同
不构成 R2 完成声明。

## 准入策略与通知选择

[`node_policy.rs`](../crates/cordis-kernel/src/node_policy.rs) 持有真实的
`Policy { profile, configured }`。`Driver` 不再另存这两个字段，也不再自行选择通知重试对象；
configure、mount、seal、notify 命令均调用同一个可执行所有者，JSON profile 枚举在边界翻译。

| 入口 | 对真实执行的合同 |
| --- | --- |
| `configure_profile` | 一次配置或首次成功分配冻结 profile。`frozen_profile` 与 `registration_freezes_profile` 沿后续完整历史保持它，包括移除最后一个插件后；分配失败不触发冻结。 |
| `mount` | 检查真实父级的成员资格、退休与卸载状态，再按传入声明分配并封闭实际返回的 episode。`mount_trace` 给出准确的 gate／分配／seal 调用、返回及已完成的失败前缀。 |
| `seal_declarations` | 拒绝未知或已封闭的预约；已退休但未封闭的预约仍为无操作；否则先更新真实依赖，再执行 seal。`seal_trace` 按序记录两次实际返回。 |
| `notify` | Harness 只选择真实依赖与通知端口相交、且没有清理失败的 consumer；Cordis 保留 setup 失败。`notification_frame` 保持其他 episode 字段、无关 episode 和全部失败清理。 |

被拒绝的 gate 保持完整记录观察。Configure 与 Notify 具有显式宿主扩展含义：前者改变策略，
成功通知更新检查状态及指定失败标志；生命周期投影不变，但它们**不是整个观察的 stutter**。
父级准入与声明封闭把这些扩展接到已有论文／控制步骤。普通 JSON 转换、JS 派发及回调真实性仍是边界。

集成回归覆盖分配拒绝、重复 seal、退休、卸载、移除、两种 profile、空／重复通知、不同 realm、
失败清理的租约保留，以及重试后拒绝旧回复。真实 JS 清理案例也会在失败后发出通知，并要求显式重试清理。
三个新增可编译反例分别重新打开已冻结 profile、绕过父级准入、通过通知清除失败清理；
都必须在指定合同处失败。当时源码通过 152 项 Node 范围 Verus 检查、81 项 Rust 回归、
20 项真实 Node 回归、这三个选定反例及全工作区严格 Clippy；这些结果不代表全量负例或整个 R2 验收。

## 捕获的回调祖先路径

生产路径是 JS `beginInvocation` → Node-API `NativeInvocation` →
`Driver::begin_invocation` → 受验证的
[`NodeRuntime::begin_invocation`](../crates/cordis-kernel/src/node_scope_path.rs)。
构造器先验证所选父路径中的每个句柄，再签发新 receipt，返回私有 `Path`：
准确的父路径前缀加上本次新 receipt。它不暴露可变句柄列表。后续 Node-API 查询
直接传入该原生对象，JS 不再在每次等待时重建列表。绑定声明 `scopeProtocol: 2`，
需要匹配的原生插件。

| 合同 | 实际作用 |
| --- | --- |
| `begin_invocation`：准确父前缀、真实末尾签发及历史前缀保持 | 创建嵌套路径时不能遗漏已选择的祖先；父路径检查和签发进入同一 Node 历史。 |
| `check_invocation_wait`：允许等待当且仅当每个捕获句柄在当前控制图下都安全 | 已完成的嵌套回调不能隐藏仍存活的 setup、清理或 task 祖先；阻塞原因对应真实捕获 receipt 及保留的 provider／owner 关系。 |
| `finish_invocation`／`invocation_own_live` | 完成和 task 自等待检查只使用自己的 receipt，子回调结束不能结束父级或兄弟回调。 |
| `known_scope_origin` 配合 `finished_scope_stays_inactive` | 逃逸路径中的非活动句柄也来自此前真实签发；旧／重复完成不能核销新回调。 |

账本只保留存活 receipt。每条捕获路径保存 O(深度) 个句柄，由回调上下文持有；
逃逸上下文会在被回收前保留该向量，但不会使账本保留已完成记录。证明历史仍被擦除。
底层 JSON 列表命令仍接受调用者提供的祖先，不具有路径构造器的更强保证。

本轮补齐的是**所选原生父路径的保持**。JS 仍通过 AsyncLocalStorage 选择父路径并
派发真实回调；这不证明 JS 全部因果祖先、回调终止、任意回调效果或 HMR 模块语义。
反向 Rust 调用仍使用独立受检查的请求权限。该路径协议属于生命周期投影不变的
宿主执行扩展，既不是把不透明回调工作证明为论文 stutter，也不是添加 Cordis 论文公理。

[真实 Node 回归](../tests/node-compat/invocation-ledger.test.mjs) 覆盖已完成嵌套回调
在仍存活 setup 下等待、两种 profile、取消、准确完成，以及伪造／异域原生对象。
[Driver 回归](../crates/cordis-driver/tests/invocation_scopes.rs) 继续扩展已完成路径，
拒绝旧代次和重复完成，并检查存活记录数回到零。两个可编译负例分别截断复制的父前缀、
只查询叶子句柄；都要求新的匹配正例及指定合同的准确拒绝。

## 证据与剩余边界

上一捕获祖先路径源码切片通过 **179 项定向 Verus 检查、29 项 Rust 回归、805 项 Node／Loader
回归及两个新增严格负例**，并通过格式、全工作区严格 Clippy 和全部 297 个规范锚点
预检。此前策略批次的数字仅描述历史源码。较早并行运行的五项超时保留记录；最终 Node
复跑在构建／证明结束后进行，并发度、断言及限制不变。这是实现切片证据，
不是全内核、全量负例、完整开发、发布或整个 R2 验收。
这些数字属于绑定历史源码的证据；后续共享 driver 身份分配器的当前记录见
[受验证分配](r2-execution.zh-CN.md#受验证的原生身份分配)。

[`node_execution.rs`](../crates/cordis-kernel/tests/node_execution.rs) 通过这个真实所有者
串起版本 ABA、通知、Begin 捕获、存活租约下的替换、provider 撤销、清理失败、旧回复拒绝、
新票据重试及最终释放；另有初始 publication 接管和动态依赖声明场景。
十进制字符串 [Driver 回归](../crates/cordis-driver/tests/check_protocol.rs) 经过真实 JSON
命令边界检查 ABA。[episode 回归](../crates/cordis-driver/tests/episode_failure.rs) 还覆盖
失败／重试进入新代次，旧错误不能覆盖当前票据和状态。新增场景还串起准备阶段接管、
嵌套回调、清理失败及下一代次，并组合多版本发布、显式 revoke、reclaim、其他 provider
和从 registry 构造的重试释放清单。句柄场景还覆盖共享／撤回引用、最大数字句柄、ABA、
拒绝操作及重复交付；真实 JS [清理回归](../tests/node-compat/disposal-failure.test.mjs)
在两种兼容 profile 中检查失败清理与重试期间读取替换后的对象。此前十六个登记反例分别替换错误句柄、
反转检查结果、绕过受管释放、把 admission 存到错误 owner、失败时丢弃 admission、
隐藏清理失败标志、错误回调归属、跳过 scope 结束、遗漏不可见旧版本、提前停止批量撤回、
交付仍被引用的句柄、错误载荷入队、遗漏替换的回收候选、返回错误读取载荷、
忽略读取代次或绕过已提交绑定；
都必须先编译成功，再在指定合同处被拒绝；本轮另有上文三个策略反例。
前一份[开发记录](development-report.json) 将结果绑定到当时的源码，对当前工作区属于历史记录；
选定反例不等于全量负向验收。

```sh
source scripts/toolchain-env.sh
export CARGO_INCREMENTAL=0
./scripts/verify.sh --verify-module node_runtime --num-threads 2
cargo test -p cordis-kernel --test node_execution --offline
cargo test -p cordis-driver --test check_protocol --test episode_failure --test invocation_scopes --offline
node scripts/build-node.mjs --offline
node --test --test-concurrency=4 --test-timeout=30000 tests/node-compat/*.test.mjs tests/node-loader/*.test.mjs tests/benchmarks/*.test.mjs
```

该历史从真实空状态开始，在**一个 Node 所有者内部**连续。它没有为独立 native Journal、
Node 实例或进程虚构全序。JavaScript 对象内容、N-API／JSON 翻译、predicate 与 I/O 真实性、
JS 调度、Fiber 效果／Child 函数和 HMR 模块行为仍需各自接入。profile 选择、mount／seal
准入、通知重试选择、parent／接口状态和声明协调现已进入受验证所有者。返回的句柄批次现来自受验证所有者；引用移除还会检查 `Bridge` 中真实的
publication／Fiber／claim 表。JSON 交付、JS 保留根删除与垃圾回收仍属于适配层／运行时。实际 scope receipt 和 publication 选择
已经由受验证所有者管理；JavaScript 仍负责派发回调及选择 ALS 父上下文；原生路径保证保留所选父路径，
不等于证明完整 JS 因果祖先或回调结束。从 registry 构造完整清单，也不等于
证明 JS 对象的销毁或其中任意效果的语义。Harness 通知后清除失败时，受影响 consumer 的完整选择
现由真实受验证接口表推导。R2-D/E/F 以及整个 R2 仍为**进行中**。
