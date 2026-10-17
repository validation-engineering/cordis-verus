# 配置更新：从实际计划到已接受版本

当前 R2 状态以[第 5 包统一验收](r2-acceptance.zh-CN.md)为准：managed-production/v1 范围已完成。下文保留各批次历史记录及其当时的验证范围。

## 历史实施与验证记录

第 3 包现已补上配置数据与绑定解释，包括 schema 规范化和来源回读。下文较早检查点记录协议的逐步实现；其中的剩余边界应结合当前边界节与[第 3 包审查说明](r2-configuration-semantics.zh-CN.md)阅读。

[English](r2-configuration-execution.md)

生产 Loader 已用受验证的 owner 管理实际更新计划、正向／逆向 Future、已接受快照
和恢复输入。尚未完成的更新不能授权配置提交；尚未完成或失败的 inverse 不能授权
恢复完成。这些是实际执行代码的协议保证，并不证明任意插件的 inverse 真正撤销了 I/O。

## 论文义务与运行路径

定义 81 用父级内的 `id`、模块、上下文注解、绑定配置和管理状态描述一个配置条目。
后续 reconciliation 讨论依赖正确的实例化／撤销，以及论文恢复、终止和收敛结果的前提。
本批次连接其中一项必要条件：接受的原地更新必须属于目标登记组件，并由真实执行／恢复
结果授权。它没有关闭定理 73、80，也没有把 group／include 当作已经证明的叶子条目。

实际调用链如下：

1. `Loader::apply_transaction` 为更新捕获原生 `Target`，将实际
   `Action<UpdateKey, ConfigUpdatePlan>` 放进 `Configuration::begin_structural`。
   路径与目标身份独立于可变的回调载荷。
2. `Loader::apply_prepared` 驱动 `Configuration::poll_update`。
   `Batch::poll_apply` 选择实际保存的下一个动作，将其真实计划借给宿主。
   宿主在轮询前检查捕获的目标身份。
3. `ConfigUpdatePlan` 中的 `Reversible` 持有真实的 pinned 正向 Future、inverse 工厂
   和待完成 inverse Future。受验证 owner 缓存真实正向结果，并跨调用者取消保留 Future。
   宿主负责轮询和将捕获的 panic 转为错误。
4. 全部动作成功后，`Runtime::adopt_config_recipes` 调用受验证的
   `NativeRuntime::adopt_configurations`。内核预检整个持有的批次，并证明每项真实
   目标、函数体和元数据的采用完成，之后才返回成功。
5. `Configuration::commit` 检查自己持有的批次并消费自己持有的候选快照。
   失败或取消时，`Loader::recover` 先逆序驱动保留动作，再重建已接受配置树。

## 结构性协调与原生 allocation 证据

生产 Loader 现在通过 `Configuration::begin_structural` 开始事务。受验证的阶段所有者
要求先移除、成功排空、挂载、再次成功排空，之后才能执行原地更新；全部更新之后还必须
实际采用新配方，才能 `commit`。恢复则先排空 inverse，再移除新建／失败的实例、排空、
重建、再次排空。回调 Pending／失败保留当前阶段和实际待办数据；重新进入恢复不会重做
已经成功的重建阶段。擦除的 `forward_steps`／`recovery_steps` 序列证明这些顺序前缀，
公开轮询合同把每次推进连接到真实回调的成功返回及其真实参数、调用前后载荷。

`configuration_tree::Tree` 持有真实节点名称、不可变配方载荷、启用标志、父索引和
allocation。普通路径索引只是缓存：`Tree::get` 会核对真实节点名称。插入拒绝重名、
不存在或已禁用的父节点；挂载从树中选择父身份，父身份缺失时在调用工厂前拒绝，不能
回退到外层 root。实际调用失败保留该节点的配方和身份，供重试使用。

`Runtime::mount_configuration` 从真实 `NativeRuntime` 取得私有构造的 `Allocation`，
其中包含由经过认证的原生执行快照证明的运行域、节点和父身份。树只接受预期运行域和
父身份，内核 API 会返回被拒绝的 allocation。替换父节点时，保留子节点暂时指向旧父是
允许的协调中间态；`Tree::ready` 在子节点重新关联前拒绝完成。快照与顺序证据均被 Cargo 擦除。

生产 `recover_with` 在全部恢复阶段完成后，对实际保留的恢复载荷调用提取函数，再接受
它返回的快照，不接收调用者自行提供的替代快照。这证明结果来源；它本身不证明任意
重建回调恢复了论文的整个上下文。

审查入口为 `configuration_tree::{mount, ready}`、
`configuration_runtime::configuration_allocation`、
`configuration_transaction::{poll_structure, commit, recover_with}`，以及真实
`Loader::{apply_prepared, recover}` 调用者。案例覆盖父节点缺失／错误、不同域数值 ID
碰撞、错误路径缓存、父节点替换中间态和各结构阶段的中断。严格负例还拒绝跳过结构性
提交／恢复以及接受错误缓存条目。

完整开发证据由 `python3 scripts/record-development.py --offline` 写入
[development-report.json](development-report.json)，其状态和源码指纹必须匹配当前代码。
这份证据与整个 R2 语义验收、完整负例回归和发布／平台验收分别记录。

## 父级局部身份与完整结构派发

生产 planner 现在把真实条目 ID、父索引和管理启用标志传给 `Tree::prepare_entry`。
受验证代码从自己保存的父节点构造路径，并传播祖先禁用状态；`insert_entry` 在当前
树上再次核对准备结果。局部 ID 允许 Unicode，但不能为空，也不能包含 `/` 或 `:`。
`qualified_key_identity` 和 `local_key_correspondence` 证明实际路径对
**（父级，局部 ID）** 是单射编码：不同父级可以使用相同 ID，同级不能重名。
这把定义 81 的 reconciliation key 连接到真实 Loader 输入，没有将全部 JSON 字段
一并宣称为已解释。

树还拒绝两个不同条目共同占用同一个原生 allocation。`Tree::retirements` 比较真实
旧树和候选树，精确选出未在相同路径保留相同身份的旧 allocation；旧树非空时，运行域
或外层 root 改变会被拒绝。实际移除阶段调用 `retire_into`：擦除的 receipt 记录每次
真实 `dispose` 调用、参数、宿主状态和返回结果。成功覆盖整个选择列表；失败记录首个
失败调用，停止后续派发。

正常挂载和恢复现在都调用同一个受验证的 `Tree::reconstruct` 循环。它使用真实节点的
父先子后顺序，跳过禁用条目，将保存的配方和当前父身份交给回调。宿主保留实例前重新
读取真实原生 allocation；需要替换时调用保存的工厂。树拒绝运行域、父身份不符或身份
重复的返回结果。整次成功必须遍历所有启用条目并满足 `Tree::ready`，同时保持名称、
局部 ID 来源、管理状态、父索引和配方。失败保留已完成前缀，失败节点和后续节点不变，
也不调用后续回调。回调报错前产生的宿主变化被 receipt 保留，没有假设它们自动回滚。

`Rebuilt::visits`、`chain`、`complete_prefix` 和 `removal_prefix` 是这些真实循环的
擦除证明证据。普通 `Snapshot::order` 列表已删除。allocation 快照证明捕获时真实发生的
原生观察，不保证实例永久存活、系统必然排空或任意工厂效果语义等价。具有来源的结构展开
见下文；完整 group/include Component 含义、模块／配置含义及 native／Node／配置共同 Journal
仍需各自的解释。

审查入口为可执行的[身份代码](../crates/cordis-kernel/src/configuration_identity.rs)、
[选择与移除](../crates/cordis-kernel/src/configuration_selection.rs)、
[重建循环](../crates/cordis-kernel/src/configuration_reconstruction.rs)及其
[Loader 调用者](../crates/cordis/src/loader.rs)。

本批次待集中补齐的集成证据：

- 不同父级重复使用 Unicode ID；同级重名、非法 ID、禁用祖先和过期准备结果。
- 父节点成功后真实回调失败，再恢复重试；保留成功 allocation，并为子节点使用重建后的父身份。
- 路径移动、身份替换、跨域和重复 allocation；拒绝保留错误实例、跳过节点或失败后继续的突变。

身份／派发检查点属于历史记录。当前源码绑定的定向验证见下方规划合同；
上一份开发记录不能直接作为修改后源码的通过证据。

## 具有读取来源的 group 与 include 展开

真实文件加载和保存预检使用的 `read_tree_cached` 现在调用
[`configuration_expansion::Expander`](../crates/cordis-kernel/src/configuration_expansion.rs)。
输入是实际持有条目载荷、inline 子节点和可选 include 请求的树。适配层将这些字段移动
到 expander，再将展开结果移回；调用者不提供“预期结果树”。

受验证算法先展开 inline 子节点，再用当前文档的 base 和条目的真实 include 请求读取
文档，递归展开返回的条目，并把它们接到请求条目之下。`Forest::valid` 与
`Branch::valid_for` 描述完整递归结果：每个输入位置恰好对应一个载荷不变的输出，
子节点顺序准确，include 的根不能误接成请求条目的兄弟。擦除的读取区间连续且完整，
不能省略某次读取，也不能用另一份成功读取结果为当前子节点提供来源。

Expander 持有真实 reader 状态；擦除历史将每次请求、返回文档／错误连接到实际回调的
前后状态。`failure_from` 还要求返回的读取错误就是本次展开中最后一次真实读取的错误，
不能用旧错误或虚构错误代替。成功推导携带真实文件身份祖先链，并证明无环、有界。报告的 cycle 包含已走过
的不重复前缀，以及前缀中已存在的结尾身份。身份输入采用原生路径字节，不通过有损
Unicode 转换合并不同路径；路径规范化以及字节身份与文件系统对象的关系仍由适配层负责。

既有嵌套上限现在跨 include 文件边界检查，并在应用新修订前拒绝过深的展开树，避免
每进入一个文件就重置树深度。读取／展开失败不返回可接受的输出树；调用者保留上一份
已接受配置及源记录。源 checkpoint 保留本次展开使用的真实解析结果，`load_file` 不再
在运行时修订提交后重新解析相同文件。

JSON 解码和少量条目输入／输出转换仍是普通 Rust 适配层；证明从结构化树开始。
这不证明文件系统真实性、URL／模块／schema 解释、group 组件的完整效果函数、源文件
保存往返语义或 native／Node／配置共同 Journal，也不证明外部 reader 最终返回。

待集中补齐的集成证据：混合 inline/include 的顺序与载荷、同一 include 在不同父级下的
实例、嵌套读取失败后重试、原生路径字节身份与真实循环、跨多个文件的总深度上限。
严格突变应覆盖丢失／错接 include 根、替换读取结果和跳过循环／深度守卫。
这些是新增证据项目，与本轮实际运行的既有 Loader 回归分开记录。

## 从源条目到完整计划的实际遍历

真实 `Loader::prepare` 现在调用
[`configuration_planning::plan`](../crates/cordis-kernel/src/configuration_planning.rs)。
受验证遍历将结构化输入转换为准确的深度优先、父先子后顺序。`preorder` 包含全部条目，
包括禁用条目，并为每个子条目指定真实父条目的位置。planner 自己构建 `Tree`；
宿主不再提供已经完成的候选树，也不再驱动另一套普通 Rust 递归遍历。

每次回调接收保存的源载荷、受验证的父级局部 `PreparedEntry`，以及该父条目实际返回的
上下文；根条目使用给定的根上下文。生产上下文包含 scope、继承的 injection 配置及父级
保留决定。回调实际执行模块／服务查找、schema 规范化和实例保留判断；受验证 planner
保存其返回的配方与 allocation，再处理子条目。普通路径表从受验证的键重新构建，仍只用作缓存。

`prefix` 与 `chain` 连接完整输入顺序、真实回调、宿主状态、父上下文和已保存配方。
成功必须覆盖每个源位置恰好一次。回调失败必须返回最后一次调用的真实错误，该调用仍绑定
对应源条目和真实父上下文。此前接受的节点保留在擦除的部分计划证据中，后续回调不再执行；
结构拒绝也立即停止派发。失败计划不会暴露可被 Loader 接受的运行时 `Tree`。
输入深度／容量拒绝发生在任何规划回调之前。这些日志和部分计划证据均由 Cargo 擦除。

这将结构化输入遍历连接到了既有移除／重建和事务所有者。少量 `Entry::into_planning`
转换、schema／模块含义、上下文转换语义、回调副作用和完整 Component 成员资格仍是
明确的适配层／语义义务；实际返回结果本身不能替代回调的效果定律证明。

待集中补齐的集成证据：含多个兄弟的嵌套 group/include、禁用祖先、不同父级的 scope／
injection／保留决定、父级成功后回调失败再重新规划，以及在后续回调前拒绝重复键或
重复 allocation。严格突变应覆盖跳过输入、使用兄弟上下文、保存其他配方、失败后继续执行，
以及将失败的部分树作为成功计划返回。

上一轮规划源码检查点通过 **158 项定向 Verus 检查、0 错误**、全工作区／全部目标／
全部 feature 的严格 Clippy，以及 **59 项已有 Rust 回归**（8 项内核配置、51 项
Loader／更新／服务配置／持久化案例）。证明命令同时编译了同一份内核源码。
这是配置范围的验证，不代表整个内核、整个 R2、完整负例或发布验收；上述新增集成场景
和完整开发记录仍待完成。

## 实际登记配方的完整批量采用

`Runtime::adopt_config_recipes` 现在通过原生 driver 调用受验证的
[`NativeRuntime::adopt_configurations`](../crates/cordis-kernel/src/configuration_adoption.rs)，
传入自己持有的真实目标、setup 函数体和元数据批次。普通宿主保留插件／接口兼容性检查，
不再自行驱动目标去重和容量预检，也不再用预检后的 `expect` 来替代整批替换成功的证明。

`preflight_configurations` 在改变任何登记、调用任何元数据更新器之前，检查全部捕获的
运行域、活跃代次、配方版本、重复 owner 和版本容量。返回结果与整批 `ready` 条件等价；
拒绝指出真实无效目标、重复身份或耗尽版本，并退回完整原始载荷批次，原生 owner 保持不变。

受验证采用循环证明：替换前面的不同目标，不会使后面的目标失效。成功返回覆盖原始顺序的
每项输入：安装准确的 setup 函数体、版本恰好递增一次、返回原函数体，且 `metadata_call`
将实际宿主前后值和返回元数据连接到同一条目的真实更新器。未选中的登记不变；声明、realm、
父身份、生命周期、发布值和活跃 Episode 也不变。这是修改未来函数配方的配置扩展，
不能称为包含全部函数字段的状态 stutter。

生产更新器仅交换名称和下一次激活的更新 hook，并返回被替换的值，不在批次中途释放用户
捕获；旧函数体和 hook 在整批返回后才释放。当前活跃 Episode 继续保留原有更新 hook。
`Configuration::poll_structure` 接收实际返回结果，只有完整采用才能推进配置提交。

合同区分正常 `Err`（原生状态不变）与正常 `Ok`（完整采用），不提供任意元数据更新器
panic 后的回滚，也不证明回调副作用、析构语义或任意替换函数体的 Component 成员资格。
接口兼容、从 `Plugin` 的字段转换、宿主字段含义及完整 native／Node／配置语义仍是明确义务；带类型配方记录已接入共同 Journal，见下节。

[原生运行时案例](../crates/cordis-kernel/tests/native_runtime.rs) 覆盖第二个目标过期、
第二个 owner 重复时第一项不变，以及采用乱序批次中的不同新函数体和元数据；同时检查
准确的旧载荷、版本变化、代次不变和发布句柄保留。待补严格突变包括跳过去重或容量检查、
存入其他函数体、遗漏返回旧载荷，以及更新错误 owner 的元数据。宿主析构顺序故障案例和
整个 R2 验收单独推进。

上一轮采用源码检查点通过 **169 项配置范围 Verus 检查，以及 2 项单独选取的底层
依赖合同检查**，均为 0 错误；全工作区、全部目标和 feature 的严格 Clippy 也通过。
**81 项 Rust 回归**通过：30 项内核配置／原生运行时案例和 51 项 Loader／更新／持久化
案例，包含新增的两项批量采用案例。这些结果对应本次采用批次的源码，不代表整个内核证明、
完整 R2 验收、负例证明或发布／平台验收。

## 共同执行历史中的真实登记配方

生产原生 owner 现在保存擦除的
[`recipe_history::History<R>`](../crates/cordis-kernel/src/recipe_history.rs)，
记录准确的 `RegisteredPlugin<R>` 值。私有 ledger 与生命周期、对象写入、槽位、工作和
清理共用同一个 Journal。[`Recipes` 记录](../crates/cordis-kernel/src/recipe_execution.rs)
投影真实运行域、组件、父级、anchor、realm、声明和配方版本，不为任意回调函数体编造语义。

普通注册和 SharedChild 注册记录版本为零的真实函数体；移除记录实际移除的条目。
替换记录新函数体及恰好一次版本递增，同时保留活跃 Episode 和发布值。`call` 与
`call_opaque` 记录真实返回的调用；`run_value_root` 与 `run_service_root` 记录实际登记
程序的返回，包括返回值内部的失败。公开合同将每个事件连接到实际调用前后注册表和返回结果。
被拒绝的准入或调用不会追加成功调用记录。`FnMut` 可以改变捕获状态而不改变安装版本；
带类型历史保留这些真实前后值，没有假定函数体始终不变。

配方调用提交在持有 Journal 写锁时认证真实 native owner：生命周期票据、工作域、
Loading 阶段及未退休状态必须对应；锁内不运行用户回调。生命周期插入／移除及对应的配方
记录是有序内部步骤，不宣称两者是一个原子的论文步骤。`recipe_snapshot` 在同一读锁区间
观察配方记录和 native owner。

`Snapshot::complete_projection` 证明检查点中的每次配方记录修改都有对应的带类型状态，
没有遗漏。`History::installed_origin` 从历史推导保留版本此前真实发生的注册／替换；
`Snapshot::invocation_origin` 进一步利用准确事件位置及跨记录守卫，将调用连接到该安装
版本和真实保留的 native Episode。值写入和清理可以在配方事件之间交错，仍保留在共同历史中。

Cargo 擦除历史、旧函数体和证明索引；快照只保留共享 Journal 句柄，不保留旧插件捕获。
原生回归案例覆盖准入后替换配方、拒绝旧调用、取消、重新激活、调用新函数体、退休／Leave
及移除，并在保留多个快照时检查旧捕获能被释放。

回调返回可能只是构造了一个 Future；它的完成仍由既有 awaited-result／工作合同跟踪。
配方事件不证明 Future 必然结束、任意外部效果正确或完整函数的 Component 成员资格。
Node 对象／Fiber／HMR 解释、完整配置含义和跨宿主语义组合仍属 R2 工作。待补严格突变包括
遗漏配方记录、改变记录中的版本／owner、将调用连接到外来 native key，以及漏记 SharedChild
注册。完整开发和 R2 验收与下面的定向证据分别记录。

## 共同执行历史中的配置阶段

生产 `Loader` 现使用
[`configuration_recorded::Recorded`](../crates/cordis-kernel/src/configuration_recorded.rs)，
持有真实 `Configuration` 协议及带类型的 ledger，并直接使用 Runtime 的真实 Journal，
与原生生命周期、配方、值及清理共享历史。组合所有者不暴露可变协议引用，
现在也持有下文所述的源状态。

成功 begin、每次正向／逆向／结构轮询返回、commit、重建以及源表示 refresh 都记录真实
前后协议值。实际 Pending、错误与完成分别分类；被拒绝的 begin／commit／恢复／refresh
保持整个所有者及历史不变。refresh 可以在修订号不变时改变配置载荷，因此明确归类为
元数据转换，不能把它当作完整状态不变。

[`configuration_batch::{apply_result, rollback_result}`](../crates/cordis-kernel/src/configuration_batch.rs)
及 `configuration_transaction::{update_result, structure_result}` 将真实回调参数、
调用前后载荷和返回结果传过组合边界，包含 Pending／失败时发生的部分修改。
恢复仍从保留载荷的真实重建回调提取被接受状态。

[`configuration_history::History`](../crates/cordis-kernel/src/configuration_history.rs)
以擦除证据保存准确的候选、恢复载荷和更新计划，并将它们索引到共同 Journal 的
[`Configuration` 记录](../crates/cordis-kernel/src/configuration_execution.rs)。
`Snapshot::complete_projection` 证明捕获的共同轨迹中，该配置记录的每次修改都有对应
带类型条目，允许其他所有者交错。`History::commit_inputs` 从历史推导真实成功前缀及
提交的原始候选；`accepted_origin` 将已接受载荷追溯到实际初值或明确的提交／重建／refresh。

用户回调在 Journal 锁外执行，其生命周期／值／清理动作可以先于轮询返回记录，并与其他
所有者交错。因此配置事件是返回边界，不是包围回调的原子事务。历史、旧计划和旧 Future
均擦除，运行时持有当前协议、源状态及共享 Journal 句柄。

这建立了配置事件在原生轨迹中的真实顺序及带类型来源。加载源／checkpoint 转换已按
下文接入同一 Journal；group/include 的 Component 定律、JSON／合并含义、任意
回调／析构与完整 Node／Fiber／HMR 解释仍是 R2 义务，不能仅靠事件名称关闭。

待集中补充的证据：交错真实值写入与配置轮询，注入更新失败和逆操作失败，在恢复期间
保留快照并检查旧 Future 捕获释放；严格突变应覆盖遗漏配置记录、改变返回分类和替换
真实恢复结果。下文的源／阶段案例关闭其中一部分证据，其余场景仍待验收。

## Loader 运行时归属与联合观察

`NativeRuntime::configuration` 现在从自己的 Journal 构造真实 `Recorded` 所有者。
`Loader::with_runtime` 经 `NativeDriver`、`Runtime` 使用这个受验证构造入口，
运行时与配置字段均为私有。公开 `runtime_mut()` 返回
[`RuntimeAccess`](../crates/cordis/src/runtime/access.rs)：保留 mount、更新、restart、
清理／重试、settle 和 shutdown 等可变操作，但 `Deref` 只允许读取，不返回能替换
宿主的 `&mut Runtime`。这修复了一个真实的安全 Rust 接口缺口：此前可以通过
`mem::replace(loader.runtime_mut(), Runtime::new())` 更换宿主，使配置与源 checkpoint
仍留在旧 Journal。

异步操作消耗该操作视图，并保留其底层独占借用。例如
`let pending = loader.runtime_mut().settle();` 可以保存后再等待；丢弃 Future
仍保留原有取消／恢复行为。需要不受限制的 `&mut Runtime` 的辅助函数，应改用独立
持有的 Runtime，或接收操作视图。这是未发布 API 的有意收紧。

`Loader::execution_snapshot()` 调用受验证的
[`NativeRuntime::configuration_snapshot`](../crates/cordis-kernel/src/native_configuration.rs)。
它在**同一次 Journal 读取期间**认证真实原生 member、配置 ledger 与源 ledger。
当前原生控制／publication／Episode 归属观察，以及配置和源的完整带类型历史，绑定到
同一份捕获序列。`Snapshot::complete_projection` 证明其中每个原生、配置、源记录
修改都对应某个带类型状态，包含各所有者最后修改之间的交错；源 checkpoint 来源和
已接受配置证明也使用这份捕获。使用新 Journal 或遗漏真实原生 member 认证，会违反
对应构造／快照合同。

组合快照只保留一个实际 Journal 句柄，旧载荷与历史被擦除；这个接口提供证明证据，
不生成持久审计日志。Journal 读锁期间不调用插件，也不获取载荷锁。内核底层快照
仍要求配置来自同一 Journal；普通 Loader 适配层通过构造、私有字段和受限操作视图
保持该前提。这项 Rust 归属约束不等于完整 Loader 或任意回调的形式化证明。
完整 Component、Node 及源语义义务仍未关闭。

## 配置执行历史中的源 checkpoint

`Recorded<S, R, K, U, P, V>` 现在同时持有实际配置和对应的
`sources::Source<P, V>`。生产 `Loader` 不再另外存储可独立修改的源对象；
`load_file`、`load_json`、dispose 和 `SavePlan::commit` 都经过这个组合所有者。
只读引用仍供源投影与保存计划使用，但外部不能通过可变引用替换其中的配置或源状态。

`load_sources`、`clear_sources` 在存在未完成更新／恢复时拒绝操作，两个历史均保持
不变；加载拒绝还返回实际输入。保存接受仍消耗真实游标，验证原始域／修订票据，并
保留已处理前缀与待同步标志的规则。I/O 和接受期间，适配层独占借用整个所有者，
保存报告不能再修改另一个源对象。

源记录器由真实配置 ledger 构造。[`Sources` 转换](../crates/cordis-kernel/src/source_execution.rs)
在同一个 Journal 写锁期间认证该配置记录，并要求没有待完成事务。事件记录观察到的
配置状态，既包含已接受修订号，也包含执行序号：恢复和 refresh 可以保持修订号，
但仍对应不同的带序号状态。源转换必须走 `Member::update_guarded`，普通更新接口
不允许这类转换。实际载荷修改与释放发生在取锁之前，用户回调仍在锁外执行。

[`configuration_source_history::Snapshot`](../crates/cordis-kernel/src/configuration_source_history.rs)
在同一次 Journal 读取中捕获带类型的源历史与配置历史。`complete_projection` 覆盖
该源记录的全部修改；`accepted_configuration` 把加载、清空和保存追溯到同一轨迹中
更早的具体配置状态；`checkpoint_origin` 再组合真实加载／已处理文档历史，证明每个
保留的合并基线都有实际引入事件及对应的已接受配置状态。这些关联从执行产生，
无需调用方提供两份“预期匹配”的快照。历史、旧配置值与审查状态会被擦除；运行时
保留当前载荷和 Journal 句柄。

这一部分补齐了源／配置的归属和顺序，尚未证明任意加载 JSON 或三方合并结果就表示
已接受的 Component 树。真实解析器、include 展开、group 含义、文件系统事实与完整
原生／Node 解释仍需要各自的 refinement 前提。适配层现有的树、registry 和源内容
比较仍然必要：同版本 refresh 之后，仅凭数字修订号不能推出载荷相等。

两个组合案例覆盖同 Journal 回调交错、待办期间源修改拒绝、结构失败／重建、
checkpoint 保留、同步失败与无改写同步重试、外域拒绝及提交后的旧保存拒绝。
真实文件系统故障测试也已使用组合所有者。新增严格负例移除恢复期间的加载准入，
或把源记录器接到无关 Journal。更广泛的值写入／Future 捕获释放、完整配置语义
验收仍保留在上面的待办中。

## 实际保存执行与已审查版本

`SavePlan` 将真实文档存入
[`configuration_save::Document`](../crates/cordis-kernel/src/configuration_save.rs)。
原始／目标文本、不可变的路径／权限／配置载荷，以及持久化重试标志，都是受验证
`Save` 所有者的真实输入。`Save::step` 按下列顺序，对自己保存的文档调用宿主：

`Check → Prepare → Recheck → Replace → Sync → Done`。

生产回调检查源文本／权限及 include 目标，准备并同步同目录临时文件，再次检查源文件，
替换后同步父目录。只有真实成功返回才推进阶段。失败停止本次保存，保留已完成前缀，
本协议不再处理后续文件。未修改文件跳过准备与替换，但待完成的持久化重试仍必须执行
`Sync`。擦除的逐文件历史证明保存完成前经过全部必要成功阶段；没有公开的“确认成功”
接口可以跳过执行。

普通适配层从受验证进度生成 `SaveReport`。替换成功、同步失败的文件必须报告为
**已写入、持久化未确认**，不能重新列为尚未处理。重试未修改文件不会重复替换。
合同连接的是每次 I/O 的真实返回结果，不证明操作系统的持久化保证、跨文件原子性，
也不排除外部编辑者的并发写入。该协议是论文配置条目之上的明确持久化扩展，不是
论文中的文件系统崩溃恢复定理。

`Configuration::save_stamp` 仅在没有待处理更新／恢复时捕获真实已接受修订号；
`Loader::prepare_save` 传入实际运行域。`commit_save` 在任何文件操作前，通过
`Configuration::accepts_save` 核对当前域与修订。因此配置从 A 改到 B 再改回 A，
旧计划也不能重新被接受；另一个运行时即使配置和修订号相同，也不能接受该计划。
域唯一性仍由原生运行时分配器提供。registry／源文件／include 检查继续生效。

[直接协议案例](../crates/cordis-kernel/tests/configuration_save.rs) 在每个保存阶段
注入失败，检查部分结果、未修改文件、同步重试及停止派发；
[真实文件案例](../crates/cordis/tests/persistence.rs) 覆盖修订 ABA、跨运行时计划，
并保留原有 include、冲突、部分保存案例。严格负例分别跳过同步、隐藏持久化未确认状态、
忽略修订号或运行域；它们必须在完整编译与匹配正例通过后被指定合同拒绝。

这一结果关闭局部保存顺序、报告和已接受修订的来源证明。完整 group/include 语义、
配置到 Component 的含义、源投影／合并解释，以及完整 native／Node 语义组合仍需
完成。源 checkpoint 的归属和原生 Journal 顺序已在上下文连接，不能由逐文件协议
替代其余语义定律。

## 从真实保存推导源 checkpoint

实际 `Loader::configuration.sources` 由
[`configuration_save::sources::Source`](../crates/cordis-kernel/src/configuration_source.rs)
持有：加载的 root／文本／include 解析结果，以及每条路径的本地配置值和待同步标志。
`load`、`clear` 和已接受保存进入同一擦除历史；清空运行状态不会抹掉证明历史。
加载保留同名 checkpoint 尚未完成的同步；JSON 适配层只能读取这些字段。

生产保存通过 `SaveStamp::start` 在派发 I/O 前消耗已审查票据，并由实际 `Save`
持有；`step` 保证票据不变。没有给已执行游标换票据的接口。
`Configuration::accept_saved_sources` 消耗该游标，核对其中的域／修订与真实配置，
并要求没有待完成恢复。无票据、旧修订或外来运行域均返回原保存对象，保持源状态不变。
生产适配层在同步 I/O 和接受期间独占借用 `Recorded`，经其 `accept_saved_sources`
入口消费结果；两次检查之间不能修改配置。

checkpoint 更新直接消耗保存对象中的真实文档和阶段，不由 `SaveReport` 授权。
只有 `Sync` 或 `Done` 推进本地合并基准：目录 fsync 失败后的 `Sync` 保留待同步，
成功重试进入 `Done` 后才清除。更早阶段失败不改变该文件的 checkpoint。
`advance_origin` 证明同一键最后一份已处理文档决定最终值，覆盖重复键；
`advance_frame` 保持未处理键。`History::checkpoint_origin` 将每个保留基准追溯到
实际加载或已处理文档；`Saved::acknowledgement` 从真实阶段历史推导 Check 及必要的
Replace／Sync 成功。文件同步故障回归也改为从这份真实保留状态构造重试。

checkpoint 表示已保存的**本地意图**，不等于合并后的磁盘文本：外部字段可以保留在
磁盘上而不进入运行配置。保存保持加载文本、root 和 include 解析结果。

这关闭了源记录管理和审查／结果来源连接，属于 Definition 81 配置条目之上的明确
持久化扩展；它不证明 JSON 解析、源投影／三方合并含义、文件系统／路径规范化、完整
分组 Component 或整树收敛。有序映射证明要求标准的键比较定律；运行域唯一性和完整
native／Node 语义组合仍是独立义务。源／配置的共同 Journal 连接已在上文验证。
历史及保存授权证明值在编译时擦除，运行时保留当前记录、Journal 句柄及准入票据。

## 保证与审查入口

| 保证 | 可执行合同 |
| --- | --- |
| 旧计划不能静默用于另一个运行时、激活代次或配方版本 | `configuration_runtime::{configuration_target, configuration_target_is_current, replace_configuration}` 对真实原生 owner 检查运行域、组件 ID、代次和版本；成功替换后旧目标失效。 |
| Pending 不算成功；成功动作构成原始顺序的前缀 | `configuration_batch::Batch::poll_apply` 对应真实键、调用前后载荷和返回结果；失败关闭后续正向执行。 |
| 取消保留正向和逆向工作 | `configuration_future::Reversible` 拥有真实 Future，调用者只借用它们进行轮询；已结束的正向 Future 不会再次被轮询。 |
| 正向操作返回前不能启动 inverse | `Reversible::poll_rollback` 在实际正向结果产生后才调用 `prepare_inverse`；返回合同连接实际保存的工厂／Future 和实际结果。正向失败仍需回滚部分执行。 |
| 恢复不会丢掉失败的 inverse 或跳到更早动作 | `Batch::poll_rollback` 只丢弃未启动计划，选择最后启动的动作；只有其实际 inverse 成功才移除，Pending／错误保留计划及修改后的载荷。 |
| 待办工作不改变已接受快照和版本 | `Configuration::{work, poll_update, poll_rollback}` 保持已接受状态；`commit` 要求批次全部完成，`recover` 要求恢复栈为空且不递增版本。 |

`Success` 和 `Landing` 证据是 ghost 数据。运行时只保存驱动执行需要的计划、Future
和少量计数，不积累无界的运行时证明日志。事务不会暴露可变批次，也没有公开的
“确认成功”入口。

恢复有意继续使用捕获的 inverse，即使正向目标已过期。解析新实例再把旧 inverse 应用
到它身上是不正确的。插件仍须捕获自己修改的资源、撤销部分执行，并保证失败回滚可重试；
规划阶段必须没有外部状态修改。这些效果定律独立于已验证的所有权和执行顺序协议。

## 尚未完成的 R2 边界

[第 3 包](r2-configuration-semantics.zh-CN.md)现已验证实际模块／作用域绑定、递归 schema
与默认值规范化、三方合并、完整子条目排序和来源回读。`Prepared::entry` 补充原有保守的
叶条目投影；原生 group 使用受验证的空程序和结构化归属子条目。

- 第 4 包仍需把这些精确的类型化观察接入完整 native／Node 生产步骤解释；第 5 包负责
  R2 总验收。R2 继续保持 `in_progress`。
- JSON／URL／IEEE 编解码、文件系统身份与 I/O、服务键翻译、任意工厂体和 JS schema
  回调属于明确的适配或外部系统边界；原生 schema 与合并算法自身已是验证代码。
- Target 认证驱动实际分配的唯一 domain，不认证故意复用 domain 的独立运行时。配方
  revision 与实际 allocation／parent 检查保留现有合同。
- 快照和恢复载荷保留真实不可变规范化配方，但配置校验不授予任意工厂效果或回调逆操作
  Component 定律。轮询／panic 真实性与回调最终返回仍需独立合同。
- 成功规划、来源回读或单文件保存确认，不等于完整生产步骤 refinement、一般恢复、
  全局终止或合流。

## 验证

此前归属与联合观察源码检查点通过 **86 项定向 Verus 检查、77 项 Rust 回归（26 项内核、
51 项 Loader／保存／服务案例）、2 项文档测试和 8 项严格负例**，以及格式检查和
全工作区全部目标的严格 Clippy。证明选择原生配置组合、原生历史、源历史、配置历史
和 Recorded 包装层，没有重跑整个 Journal 或此前全部配置证明。

一个新运行案例在配置回调中改变真实生命周期状态，并在 Pending、失败和恢复后捕获
联合快照，保留源 checkpoint。生产 Loader 的失败／重试案例也观察联合快照，restart
保留的实际运行时，并等待保存的 `settle()` Future。成对文档案例验证普通操作，并
拒绝通过视图替换运行时。这项 Rust 归属检查不计入 Verus 严格负例；后者要求突变体
仍能完整编译。

两个新增严格负例拒绝在无关 Journal 构造配置，以及共享快照遗漏真实原生 member
认证。六个既有源／保存负例也在当时源码通过。每项均要求匹配正例、完整突变体编译、
准确的指定合同／锚点拒绝。全部 **295 个规范锚点**通过预检；这不是全量负例、校准、
完整开发或 R2 验收。对后续 Node 路径批次，这些数字属于历史证据；
见[当前范围](r2-execution.zh-CN.md#当前收口状态)。

```bash
source scripts/toolchain-env.sh
./scripts/verify.sh --verify-module lifecycle_state::native::runtime::configuration \
  --verify-module lifecycle_state::native::runtime::history \
  --verify-module configuration_source_history --verify-module configuration_history \
  --verify-module configuration_recorded --num-threads 2 --triggers-mode silent
CARGO_INCREMENTAL=0 cargo test --offline -p cordis-kernel \
  --test native_runtime --test configuration_recorded
CARGO_INCREMENTAL=0 cargo test --offline -p cordis-verus \
  --test loader --test loader_update --test persistence --test service_configuration
CARGO_INCREMENTAL=0 cargo test --offline -p cordis-verus --doc runtime::access
```

### 历史源／配置组合证据

前一源／配置组合通过 **244 项定向 Verus 检查、60 项 Rust 回归（9 项内核、
51 项真实 Loader／保存路径）和 6 项严格负例**，以及格式检查和全工作区全部目标的
严格 Clippy。证明覆盖配置、源、保存和批次所有者、带类型历史，以及整个共同 Journal
模块，包括已有原生、配方、值、工作、清理、宿主和控制投影。

两个新增负例拒绝恢复未完成时加载源、把源记录器接入无关 Journal。四个既有负例
拒绝未处理文档推进 checkpoint、丢弃同步重试、接受旧票据，以及 I/O 中丢失原票据。
每项都有当前源码的匹配正例、完整突变体编译，以及指定函数／错误类型／源码锚点的
准确拒绝。全部 **293 个规范锚点**通过预检；这不等于全量负例回归或校准。

```bash
source scripts/toolchain-env.sh
./scripts/verify.sh --verify-module configuration_recorded \
  --verify-module configuration_source_history --verify-module configuration_history \
  --verify-module configuration_transaction --verify-module configuration_batch \
  --verify-module configuration_save --verify-module reversible_value::joint \
  --num-threads 2 --triggers-mode silent
CARGO_INCREMENTAL=0 cargo test --offline -p cordis-kernel \
  --test configuration --test configuration_save --test configuration_recorded
CARGO_INCREMENTAL=0 cargo test --offline -p cordis-verus --lib persistence::tests
CARGO_INCREMENTAL=0 cargo test --offline -p cordis-verus \
  --test loader --test loader_update --test persistence
CARGO_INCREMENTAL=0 cargo clippy --offline --workspace --all-targets -- -D warnings
```

两个新增[组合案例](../crates/cordis-kernel/tests/configuration_recorded.rs)与既有回归覆盖
上文所述的局部行为。更广泛的值写入／Future 捕获释放、完整 Component 解释及 R2
总体验收仍待完成。本批次未运行全内核证明、完整开发、全量负例、Node 回归或各平台
发布验收。以下数字对应此前源码。

### 历史配置 Journal 证据

此前配置 Journal 批次通过 171 项定向 Verus 检查、56 项既有 Rust 回归、格式检查和
全工作区全部目标的严格 Clippy。291 个规范锚点通过预检，该批次未执行突变体。
本轮扩展了它的源／阶段组合；旧结果不能作为修改后源码的新通过记录。

### 历史源 checkpoint 证据

此前源 checkpoint 批次通过 **68 项定向 Verus 检查、55 项 Rust 回归（4 项内核、51 项
实际宿主路径）和 4 项严格负例**，以及格式检查和全工作区全部目标的严格 Clippy。
突变分别错误推进未处理文件、丢弃待同步状态、绕过原始审查守卫、执行期间丢弃票据；
每项都有新的匹配正例、完整突变体编译及指定合同拒绝。全部 291 项正式突变锚点
通过预检，这不等于全量负例或校准。

使用固定工具链复现定向正例与运行范围：

```bash
source scripts/toolchain-env.sh
./scripts/verify.sh --verify-module configuration_save \
  --verify-only-module configuration_transaction --num-threads 2 --triggers-mode silent
CARGO_INCREMENTAL=0 cargo test --offline -p cordis-kernel --test configuration_save
CARGO_INCREMENTAL=0 cargo test --offline -p cordis-verus --lib persistence::tests
CARGO_INCREMENTAL=0 cargo test --offline -p cordis-verus \
  --test persistence --test loader --test loader_update
CARGO_INCREMENTAL=0 cargo clippy --offline --workspace --all-targets -- -D warnings
```

本批次未运行整个内核证明、完整开发检查、全量负例或发布／平台验收。
R2 的剩余语义义务见上文；这些计数不代表整篇论文完成度。

### 历史配方证据

此前配方历史源码通过 **282 项定向 Verus 证明、0 错误**、**128 项 Rust 回归**
（57 项内核、71 项真实宿主路径），以及全工作区／全部目标／全部 feature 的严格 Clippy。
两个受影响的既有严格负例——替换登记函数体、将失败确认为成功——均通过新正例、完整
突变体编译与指定合同拒绝检查。全部 282 个正式负例锚点通过预检；这不是完整负例回归或校准。

本节结果对应此前配方批次，并由 [R2 执行进度](r2-execution.zh-CN.md) 链接；上文其他批次的计数保留为历史证据。
已有案例运行真实 Loader、配置和持久化路径，包括更新取消和恢复；新增展开／规划
集成案例仍在上面的待办清单中。

可以使用固定的本地工具链复现本轮配方历史、原生／Child／Journal／root 及配置采用证明和运行回归：

```bash
source scripts/toolchain-env.sh
./scripts/verify.sh \
  --verify-module lifecycle_state::native --verify-module reversible_value::joint \
  --verify-only-module lifecycle_state::registration::shared_child \
  --verify-only-module reversible_value::function \
  --verify-only-module reversible_value::service_function \
  --verify-module configuration_runtime --num-threads 2 --triggers-mode silent
CARGO_INCREMENTAL=0 cargo clippy --workspace --all-targets --all-features --offline -- -D warnings
CARGO_INCREMENTAL=0 cargo test --offline -p cordis-kernel \
  --test native_host --test native_runtime --test shared_child \
  --test registered_value_function --test configuration
CARGO_INCREMENTAL=0 cargo test --offline -p cordis-verus --all-features \
  --test loader --test loader_update --test service_configuration --test persistence \
  --test reversible_runtime
```

这些命令选择本次改变的原生、配方历史、共同 Journal、登记 root 和配置采用合同；
不覆盖全部配置规划／展开／保存证明，也不能替代完整开发记录或 R2 语义验收。

已有严格负控候选覆盖结构阶段守卫、路径缓存、更新／恢复守卫、正向返回和目标身份。
每项都要求匹配正例、完整突变体编译成功和指定合同拒绝；资源耗尽与前端错误不能算证明
拒绝证据。本批次只重跑上述两个受影响的候选；其余负例只检查锚点，新增配方历史、规划／展开
候选仍待集中补齐。

整个内核的开发检查、R2 语义验收、全部负控／校准、Node 运行及发布／平台验收分别记录。
