# 论文进展要求与真实代码合同

[English](progress-contracts.md) | 简体中文

项目的目标是建立可以审查的“论文约束 → 运行代码”对应。对于进展性质，这个对应需要
两个方向：调用成功时，实现必须符合允许的转换；转换条件满足时，实现也必须接受调用。
在各合同明确的实现定义域内，现在已将接纳、实际迭代、动态 child 注册、同步 Mixed/Fresh
单步、跨调用已接纳落地与有限执行循环接到可检查合同。
内核迭代、episode 接纳和普通宿主的一致性检查现在使用相同的绑定身份语义，
不再额外要求私有向量的顺序或重复次数一致。

审查依据是固定的[论文版本 arXiv:2608.25512v1](https://arxiv.org/abs/2608.25512v1)。
各项状态仍以[义务清单](paper-obligations.json)为准。第 73 条保持 **partial**；
这些合同尚未建立整篇论文的进展结论。

## 论文具体要求什么

| 论文条目 | 约束 | 对应代码及剩余范围 |
| --- | --- | --- |
| 定义 53–54、表 1 | 当前目标与已提交身份决定能否开始加载、迭代或受保护地卸载。 | `semantics.rs`、`refinement.rs` 描述这些守卫。下文的 `Kernel`、`StageProtocol` 合同把部分守卫接到真实调用。 |
| 定理 73(1) | 在定理前提下，非静止状态至少有一条生命周期规则可应用。 | `draining_can_progress` 在全部已安装节点都处于待恢复 Unloading 的范围内证明存在可清理节点。新的 `begin_cleanup` 成功等价合同使这一守卫足以保证真实内核调用成功。内核 iteration/finish 现在恰好在论文的 Loading/coherent 守卫下成功；已验证 driver 将捕获的绑定接到该守卫；完整宿主捕获和一般 continuation 定义域仍有独立义务。 |
| 定理 73(2) | 限制各节点步数、目标变化次数，进而说明极大生命周期序列以静止状态结束。 | `termination.rs` 已有有限轨迹计数和到达静止状态的构造，要求固定注册表、局部表修改范围、最终完整发布和 continuation 的递减秩。实际 `ProgramEpisode` 执行器从经过检查的前向指令推出有限执行；`FreshDriver::run_until_blocked` 还对单个 actor 的真实重复 step（含 child 注册）给出有限界，直到终态发布或首个实际错误。这不是完整的动态注册表结论。 |
| 推论 69 | 终态 Unload 后，表与其他 actor 步骤的重放观察等价，owner 表为空。 | `ProgramEpisode::execute_and_recover` 在固定程序范围内恢复传入的资源单元。Mixed/Fresh `unload` 现恰好在允许清理且当前 LIFO 逆序列有定义时成功；这条执行域结论本身不证明一般的 foreign replay 方程或任意外部资源恢复。 |
| 定理 71(2) | 加载中发生 Divert 的 episode 会闭合。 | 清单记录了原文允许的序列对无条件结论的反例。若加入调度条件证明最终闭合，得到的是修正后的条件性结论。 |
| 定义 74、定理 80 | 描述支持关系，并建立规范形、合流性。 | 支持关系是状态方程；合流还需要表示、轨迹传递和交换证明。时序库不会自动提供这些缺失连接。 |

第 73 条假设优先关系无环、组件长度有界、整个序列出现的名字有限，而且每步都是
生命周期规则。其结论针对**极大序列**：在规则仍可应用时就停止的有限前缀不是极大序列。
原文没有显式假设 Node 调度公平。宿主一直处理无关工作而不推进生命周期的无限执行，
也不同于论文所述的纯生命周期序列。直接加入弱公平、却不解释讨论对象的变化，会改变
实际检查的命题。

## 本轮补强的真实调用

操作已有机器的合同要求其 `wf()` 不变式；`run_from_empty` 自行构造机器，无输入状态
前提。`old` 表示调用前状态。审查时应读取源码中的
完整前置条件、后置条件、不变字段及错误行为，不能把摘要当作独立公理。

| 真实调用 | 已检查的成功条件 | 与论文的连接 |
| --- | --- | --- |
| [`Kernel::check_insert` / `insert`](../crates/cordis-kernel/src/lib.rs) | 在且仅在 `insert_enabled(parent, dependencies, provisions)` 时成功：身份容量足够、指定的 parent 已登记、声明无重复、provision 端口未被预留。 | O-Insert 的真实注册定义域，将实现表示边界与论文谓词分开列出。 |
| [`Kernel::begin`](../crates/cordis-kernel/src/lib.rs) | `result.is_ok() == old.begin_enabled(id)`：Inactive、目标可用、generation 存在且小于 `u64::MAX`。成功后递增 generation，并提交实际目标。 | L-Begin 的可执行接纳条件。保留实现中有限计数器的边界；论文投影擦除了该计数器。 |
| [`Kernel::begin_cleanup`](../crates/cordis-kernel/src/lib.rs) | `result.is_ok() == old.cleanup_enabled(id)`：已登记、Unloading、尚未开始恢复、没有存活的 committed dependent。 | 受保护 L-Unload 的实际起点。该调用在论文投影中保持状态，开放恢复过程；`finish_cleanup` 才完成投影中的 Unload。 |
| [`MixedDriver::unload`](../crates/cordis-kernel/src/mixed_driver.rs)、[`FreshDriver::unload`](../crates/cordis-kernel/src/fresh_driver.rs) | 在且仅在 `unload_enabled` 时成功：Kernel 允许清理，**且** `restore_receipts(journal(actor), primitive_state).is_some()`。 | 执行 L-Unload 的真实有限 LIFO 恢复；控制守卫本身不保证逆操作有定义。公共错误保持完整机器，内部草稿错误不具备同样保证。 |
| [`Kernel::check_iteration` / `finish`](../crates/cordis-kernel/src/lib.rs) | 在且仅在 Loading 且 `coherent(id)` 时成功。`paper_coherence`、`paper_iteration_guard` 证明此条件恰好对应投影中的论文守卫。 | L-Iter 接纳和 L-Finish 控制转换。利用已有的 provider 唯一性、绑定类型与覆盖不变式检查身份，不依赖缓冲区的顺序或重复次数。 |
| [`StageProtocol::admit`](../crates/cordis-kernel/src/episode.rs) | `accepted == (old.pending || (!old.settled && !old.cancelled && matching_target))`。`matching_target` 指 target 存在且完整绑定身份集合相等。已接纳的阶段在取消或目标丢失后仍保持接纳；结束与取消标记的更新也有精确合同。 | 迭代阶段的接纳与保留。`land`、`end` 提供 Iter/Finish 或延迟 Divert 在 token 层的累积器转换。显式宿主取消是扩展行为，不能据此认定论文目标已变化。 |
| [`ChildEpisode::check_child` / `land_child`](../crates/cordis-kernel/src/ownership.rs)、[`ChildDriver` 包装层](../crates/cordis-kernel/src/child_driver.rs) | 在且仅在 `land_enabled` 时成功：已有 pending、捕获身份和 generation 仍匹配、满足当前插入定义域。 | 定义 52 中有条件的真实 child 注册及逆操作捕获；接纳本身不保证插入成功。 |
| [`MixedDriver::insert`](../crates/cordis-kernel/src/mixed_driver.rs) | 在且仅在 `insertion_enabled` 时成功：蓝图索引及所需蓝图库前缀合法，且满足真实 Kernel 插入域。 | 闭合解释器的注册边界；`wf()` 不会使未使用的非法蓝图条目变得合法。 |
| [`FreshDriver::insert` / `begin` / `apply`](../crates/cordis-kernel/src/fresh_driver.rs)、[`preparation_command`](../crates/cordis-kernel/src/fresh_preparation.rs) | 对 `Insert`、`Begin`、`Step`，在且仅在当前 `preparation_enabled(command)` 时成功。Insert 复用完整 Mixed 插入域；Begin 还要求保留 journal 为空及 Kernel Begin 域。 | 将真实准备 dispatcher 接到精确的局部实现定义域；其他命令仍受支持，但不在该等价合同范围内。 |
| [`MixedDriver::step`](../crates/cordis-kernel/src/mixed_driver.rs)、[`FreshDriver::step`](../crates/cordis-kernel/src/fresh_driver.rs) | 在且仅在 `step_enabled` 时成功：actor 已登记、Loading 且 coherent，存在当前指令，满足其 primitive 定义域；终态指令执行后还须完整发布。 | 同步 L-Iter/L-Finish 解释器的精确局部接纳，与引理 57 和定理 73(1) 相关，不是整段执行终止。 |
| [`FreshDriver::admit` / `Admission::land`](../crates/cordis-kernel/src/admitted_fresh_driver.rs) | 接纳在且仅在 `admission_enabled`（即 `ready`）时成功；落地在且仅在 `land_enabled` 时成功：票据未消费且当前绑定有效、满足所选 primitive 的实时定义域，仅 coherent 终态还要求 `complete_after`。 | 跨已检查调用的精确接纳，包括目标丢失后的 L-Divert；接纳不预留值或 child provision。 |
| [`FreshDriver::run_until_blocked`](../crates/cordis-kernel/src/fresh_run.rs) | 在 `wf()` 下反复调用真实 `step`，直到终态发布或首个错误；已提交步数由输入程序位置的秩约束，无需 fuel 或未来成功前提。 | 单个已安装 actor 的有限真实执行；源 refinement 延伸输入机器已表示的良构源状态，不建立全局静止。 |
| [`run_from_empty`](../crates/cordis-kernel/src/fresh_bootstrap.rs) | 构造新机器，执行真实准备脚本；仅全部准备调用成功后运行一个 actor，返回 `SetupFailed`、`Blocked` 或 `Finished`。 | 无需输入源状态前提，建立一条从 empty 出发、同时表示准备后与最终机器的源执行；失败处的 Insert/Begin/Step 命令不满足其定义域；其他命令定义域与全局进展仍有独立义务。 |

论文中已使能的 Begin，在实现的 generation 计数器耗尽时仍会被拒绝；这一容量限制
并非第 73 条原文的前提。

`ResourceEpisode::admit`、`ProgramEpisode::admit` 的真实包装层也公开相同的成功等价
条件。构造函数和成功的 restart 保证新 episode 尚未取消，因此调用方无需查看私有字段，
就能证明新阶段会被接纳。

这比“成功后状态合法”更强。单向合同可能允许实现拒绝所有请求；成功的充要条件则排除
在前置条件及使能条件满足时无故拒绝请求的实现。

相邻的部分方法原本已经具备足够的成功条件：`land`、`end` 在且仅在 pending 时接纳；
`finish_cleanup` 在且仅在 restoring 时成功；`leave`、`leave_if_changed` 已有的错误
分类足以支持相应守卫路径。这些不是本轮才修复的缺口。

## 从定义 53 接到真实接纳

定义 53 描述依赖端口对应的 provider 身份。规范投影
[`binding_set`](../crates/cordis-kernel/src/episode.rs) 保留完整的
`(key, realm, provider)` 身份，本身属于运行时会被擦除的 spec；实际执行的
`same_bindings` 在且仅在两个身份集合相等时返回 true。
重排或重复完全相同的绑定不影响判断；改变 key、realm 或 provider，或者增加、遗漏一个
不同的绑定，都会导致不匹配。目标缺失的 `None` 仍然不同于可用的空目标。

具体审查路径如下：

1. `Kernel::target` 返回完整目标，或证明目标不可用；`Kernel::committed` 把实际捕获
   向量与论文中的 committed 集合对应起来。
2. [`Kernel::paper_captured_target`](../crates/cordis-kernel/src/lib.rs) 在 `wf()`、
   actor 已登记且处于 Loading、捕获集合等于论文 committed 的条件下，证明 target 与
   capture 集合相等恰好等价于论文 coherence。这里使用定义 53 在内核控制状态上的投影，
   将 Active provision 视为完整发布；真实宿主值是否可用仍单独检查。
3. [`Driver::admit`](../crates/cordis-kernel/src/driver.rs) 与
   [`ProgramDriver::admit`](../crates/cordis-kernel/src/program.rs) 读取真实目标并调用
   真实 episode。在各自持续保持的 `wf()` 下，在且仅在 actor 已登记且 Loading 时返回
   `Ok`；在 `Ok` 内，布尔值恰好为
   `pending || (!settled && !cancelled && coherent)`。`Ok(false)` 表示检查完成但未
   接纳新阶段，不是错误，也不代表阶段已接纳。
4. [`ChildEpisode::admit_current`](../crates/cordis-kernel/src/ownership.rs) 还检查捕获
   与当前 committed、episode generation 的对应。检查成功后接到相同的接纳公式。
   即使绑定集合相同，旧 generation 的句柄也不能重新使用；后续检查须使用同一 Kernel
   实例。

捕获本身也来自经过检查的 Begin：`Kernel::begin` 成功后建立
`iteration_enabled(id)`；`refinement::begin_preserves_target` 证明 L-Begin 保持刚刚
捕获的目标。两个已验证 driver 在 Begin 成功后公开新 episode 尚未 pending、结束或
取消，并满足论文 coherence 的合同。
[`Driver::begin_and_admit`](../crates/cordis-kernel/src/driver.rs) 随后顺序调用真实的
`begin`、`admit`：在且仅在 driver 的 `begin_enabled` 条件下成功，并建立首个 pending
阶段，无需调用方预先假设接纳成功。该调用内部没有宿主步骤插入，也没有执行阶段效果
或证明回调终止。

`StageProtocol::can_finish`、普通 Rust 的
[`LifecycleDriver::coherent`](../crates/cordis-driver/src/shared.rs) 与 driver 阻塞诊断
使用相同的可执行比较。原生宿主在轮询阶段前调用 `admit`，在发布边界调用 `can_finish`。
复用已验证函数消除了额外的向量相等守卫，但没有自动验证外围普通 Rust 宿主、锁、回调
执行或 episode 捕获过程。

比较不会重写已存储的向量。长度相同且逐项匹配的通常路径为 O(n)；否则执行双向有界
成员扫描，对长度 n、m 的向量最坏为 O(nm)，不额外分配集合。这是语义对齐，不是性能
提升结论。逆操作日志、child 累积器和回调 token 仍保持原有顺序与 LIFO 行为。
仅凭比较本身也不能确认任意低层快照是合法 provider 映射；这一连接来自 Kernel 来源
及其不变式。

## 动态 child 注册的定义域已有真实检查

[`Kernel::check_insert`](../crates/cordis-kernel/src/lib.rs) 只读检查与真实 `insert`
相同的 `insert_enabled` 谓词。插入在写入节点或声明前调用该检查，在且仅在条件成立时
成功。既有拒绝顺序保持不变：先检查身份容量，再检查 parent 是否登记，随后检查
provision 冲突及 dependency 重复。插入失败保持 Kernel 不变。

与论文的连接单独列出：
[`refinement::insertion_domain`](../crates/cordis-kernel/src/refinement.rs) 描述
O-Insert 的 parent 登记与 provision 预留前提，`insertion_has_domain` 从既有
`Rule::Insert` 关系推出这些前提；
[`Kernel::paper_insert_domain`](../crates/cordis-kernel/src/lib.rs) 将实际输入守卫归约到
这些前提，加上实现中的有限身份容量、dependency/provision 向量各自无重复的条件。
端口同时包含 key 与 realm。Inactive 或已退休但尚未移除的节点仍预留其 provision；
没有已发布服务值并不意味着该端口已释放。插入不要求 dependency 已可用，也不要求
parent 活跃；新 child 以 Inactive 登记，之后的 Begin 再检查就绪条件。这条注册连接
没有证明任意 child body 满足原论文的 Component membership 前提。

规范谓词 [`ChildEpisode::current_matches`](../crates/cordis-kernel/src/ownership.rs)
描述 owner 已登记且 Loading、generation 尚未绑定或与当前匹配，以及捕获集合与当前
committed 集合一致。规范谓词 `land_enabled` 在此基础上增加 pending 和对应 owner 的
`Kernel::insert_enabled`；运行时检查由可执行的 `check_snapshot`、`check_child` 完成。
只读 `check_child` 与实际 `land_child` 都公开相同定义域下成功的充要条件；
[`ChildDriver`](../crates/cordis-kernel/src/child_driver.rs) 包装层也将此条件公开到持有
内核的 driver 边界。成功落地会把真实插入返回的 child 身份追加到真实逆操作日志。
当前 target coherence 不作为额外落地前提：已接纳的 pending 阶段在退休或目标丢失后
仍可落地，driver 随后走已有的 Divert 路径。

[`ChildDriver::check_and_land_child`](../crates/cordis-kernel/src/child_driver.rs)
顺序执行真实的预检查和落地，中间没有其他注册表操作。成功的 `check_child` 建立定义域，
据此证明后续 `land_child` 成功，不需要调用方假设其返回值。组合调用在且仅在调用前的
`land_enabled` 条件下成功，并记录真实 child 的 inverse。同一次调用内的这一结果，
不意味着之前单独进行的预检查取得了预留权。

预检查不做预留：不接纳阶段、不捕获 generation、不消耗身份、不写 inverse，其结果
只描述检查当时的状态。若中间发生注册或 episode 变化，落地必须重新检查；实际方法已
执行这些检查。失败合同也不意味着整个 episode 原子不变：`ChildEpisode::land_child`
失败时保持 Kernel、children 和阶段视图，但 detached 句柄可能在插入失败前已经捕获
当前 generation。`ChildDriver::land_child` 失败时保持 control，以及已登记 actor 的
journal 和 pending，其中的接纳刷新仍可能更新 cancellation。只读预检查自身不会改变这些字段。

这里补齐的是可执行的**注册定义域**合同，不是 child effect 或整段执行的总性。
下一节单独列出同步 Mixed/Fresh 单步的精确定义域。blueprint 合法不保证 provision
之后仍未被预留、所需值存在，或终态
已经发布全部声明服务。已有
[`guarded_child_domains.rs`](../crates/cordis-kernel/src/guarded_child_domains.rs)
仍说明：表观察相同、actor 均 coherent 且 Loading，也可能因某项已登记声明预留了
端口，而具有不同的 child 分配定义域。该反例、失败行为和原论文 Component／总性
义务均未改变；本轮没有增加失败转换来取得进展结论。

## 真实 Mixed/Fresh 解释器的精确单步定义域

[`MixedDriver`](../crates/cordis-kernel/src/mixed_driver.rs) 在真实 `u64` 服务表、
Kernel 和混合逆操作日志上执行闭合指令库。同一份可执行方法由 Cargo 编译、Verus
检查。下面的谓词描述调用前状态，不要求调用方先假设解释器或模型执行已经成功。

`ready(actor)` 要求 actor 已登记、Loading、coherent，且存在当前指令。
`installed_instruction` 从已安装的蓝图和程序位置选出指令，包括终态 Unit。
在已有 `wf()` 下，`primitive_enabled` 列出其余效果定义域：

| 指令 | 执行效果之前所需的状态 |
| --- | --- |
| Unit | 没有额外的效果定义域限制。 |
| Provide | actor 有相应声明槽位，且尚未填入值。 |
| Xor | 能解析 committed／自身表的 provider，且该 provider 的实际表已有相应值。 |
| Child | expected 身份等于真实 next ID，所选 child 蓝图及所需蓝图库前缀合法，且满足 Kernel 插入域。 |

实际 `provider` 在且仅在 primitive 状态的解析器返回 provider 时成功。但解析成功不
等于值可用：自身尚未填值的 provision 槽位可以解析，却不能供 Xor 读取。
实际 `execute` 在其声明的调用前提下，在且仅在 `primitive_enabled` 时成功。

终态指令还要求完整发布。`complete_after` 从调用前的表出发，计入本条指令的效果：
本次 Provide 可以补上最后一个空槽。若要求执行这条 Provide 之前就满足
`fully_provided`，会错误拒绝合法终态。执行效果之后，`commit_landing` 在其方法
前提下，在且仅在存在 continuation，或者实际表已完整填值且 actor 仍 coherent 时
成功。`instruction_enabled` 结合 primitive 域与终态 `complete_after` 条件，
`step_enabled` 再结合 `ready`。公共 `MixedDriver::step` **在且仅在**该谓词成立时
成功，合同不再仅仅表达成功后的安全性。

[`FreshDriver::selected_instruction`](../crates/cordis-kernel/src/fresh_driver.rs)
在本次调用中，以分配器当前 `next_id` 实例化 Child 模板。其 `step_enabled` 对实例化
后的指令使用相同的效果与终态检查；实际 `FreshDriver::step` 公开相同的成功等价合同。
自动 fresh 身份免去调用者固定 expected ID 的要求，但不会免除 provision 预留、
值可用性或发布完整性检查，也不会为后续调用预留分配器身份。

公共 `step` 方法在副本上执行，全部检查成功才提交。错误因此保持其 `same` 关系定义
的完整公共机器，包括分配器、表、程序位置和日志。在 `step_inner` 内部，成功的
`execute` 可能先写值或插入子插件，随后 `commit_landing` 才拒绝发布。这种内部错误
不会恢复副本；公共方法通过丢弃副本实现回滚。

这是同步单次调用的结论，对应引理 57 的实现连接与定理 73(1) 的局部使能性。它不证明
原论文的完整递归 Component／context 解释或整段执行终止界。跨调用接纳协议另有
下节的精确定义域；任意回调与宿主调度仍有独立义务。
`primitive_enabled` 不成立时，严格守卫的 child 反例仍适用；精确拒绝描述的是这条
边界，没有引入新的生命周期失败规则。

## 已接纳阶段在落地时重新检查当前定义域

拥有机器的 [`fresh::admitted::Admission`](../crates/cordis-kernel/src/admitted_fresh_driver.rs)
会话捕获 actor、generation、蓝图、程序位置和指令模板。`FreshDriver::admit` 在且仅在
`admission_enabled(actor)` 时成功，该条件就是内层 driver 的 `ready(actor)`。
它检查 coherent Loading 控制状态与已安装位置，不检查所有效果前提，也不预留服务值
或 provision 端口。因此，即使中间没有其它调用，接纳也可能成功，而后续落地因值缺失
或 child 预留冲突而失败。

`admit` 成功合同还明确说明，返回的
`admitted.land_enabled() == self.step_enabled(actor)`，右侧指调用前机器。
因此，刚接纳后不插入其它操作而立即落地，其成功条件与同步 `step` 完全相同。
这只是接纳定义域的等价，不意味着接纳本身保证落地：`admission_enabled` 只检查较弱的
`ready`。一旦插入其它调用，这个相对于旧输入状态的等式不保证继续成立。

票据 pending 期间，`Admission::apply` 允许执行已检查调用。`selected_instruction`
保持捕获的模板，仅将 Child 的 fresh 身份实例化为当前机器的分配器身份。`bound`
检查同一 actor 仍已登记且 Loading，generation、蓝图、位置和模板均与捕获值匹配。
它不要求当前 target 继续 coherent。

真实 `land` **在且仅在**调用前的 `land_enabled` 成立时成功：

- 票据尚未消费，且仍 `bound` 到它拥有的机器。
- 所选指令在当前机器中满足 `primitive_enabled`。
- target 已不 coherent，或者指令有 continuation，或者终态指令满足 `complete_after`。

因此，coherent 终态落地仍须完成发布，包括本次 Provide 填上最后一个空槽。目标丢失后，
落地则记录真实 inverse 并转入 Unloading，不要求完整发布；但 primitive 本身仍须有
定义，目标丢失不会让缺值的 Xor 或已预留的 child 端口变得有效。真实 `commit_divert`
在已有 `wf()`、actor 已登记且 Loading、target 不 coherent、receipt 匹配的前提下保证成功。`land` 成功时，`Landing.diverted` 恰好等于
调用前 coherence 的否定；返回的 child 身份恰好等于本次落地前机器的 `next_id`。

所有落地错误都保持 `Admission::same`，包括完整机器、捕获身份与 consumed 标志。
尚未使用的票据失败后仍未消费，可在已检查调用使定义域满足后重试。已消费或 stale 的
票据仍被拒绝，重试不会把它重新绑定到其它 episode。中间插入的注册可使原先接纳不再
足以落地；冲突条目退休后仍预留 provision，移除后才释放。本轮强化合同没有改变已有
执行分支和错误检查顺序。

[接纳回归](../crates/cordis-kernel/tests/admitted_fresh_driver.rs)覆盖了 coherent 终态
失败后使用同一未消费票据在目标丢失时 Divert，以及 child 冲突在退休后仍存在、移除后
才可成功的情况。测试检查 payload、日志前缀、分配器状态与单次消费。普遍接纳结论来自
实际 `admit`、`land` 方法的 Verus 合同，而非仅凭这些示例。

这补齐的是单个票据、闭合指令协议的局部成功域，不会让任意 Future 返回，不证明任意
回调效果，也不建立多步动态执行终止或整篇进展。第 73 条和引理 57 的完整 context／
整段执行义务继续独立保留。

## 验证真实客户端，而不只验证另一份模型

[`cancelled_admission_witness`](../crates/cordis-kernel/src/episode.rs) 是 Verus
检查的可执行 Rust 函数。它创建阶段、以匹配目标接纳、取消、在目标缺失时继续保留已经
接纳的阶段，然后调用实际的 `land` 或 `end`。它证明返回状态已取消、已结束、无 pending；
若调用方提供了 inverse token，恰好保留该 token。过早的 `pop` 返回 `None`，阶段仍为
pending；调用方提供结果并落地后，恰好保留所提供的 token。

这个客户端的终态结果由调用方直接提供。它没有让任意 Future 运行至返回，保留一个
token 也不等于证明宿主清理回调已释放资源。`ResourceEpisode` 另外把 token 接到真实
Journal 写入和逆操作。

同一份 `crates/cordis-kernel/src/` 既由 Cargo 编译，也由 Verus 检查。运行时通过
[`cordis-driver`](../crates/cordis-driver/src/shared.rs) 和
[`runtime.rs`](../crates/cordis/src/runtime.rs) 调用这些方法。driver 还有未完成 action
及容量守卫，宿主清理前也会等待 pending setup/stage。因此内核调用会成功，并不能直接
推出整个宿主工作流会接受请求或完成。

## 检查程序定义域，并执行到结束和恢复

[`ProgramEpisode::new`](../crates/cordis-kernel/src/program.rs) 在且仅在
`valid_program` 成立时成功。实际校验会检查资源索引、分支的两个目的位置，并要求每个
目的位置严格向前，允许到达 `code.len()` 的终止位置。因此，解释器的定义域与有限递减量来自对输入代码的检查，
无需另行假设每一步都会成功。

`run_to_completion` 只要求 episode 内部的 `wf()` 不变式。它在运行时检查接纳条件，
对已有 pending、已结束、已取消或目标不匹配的状态返回 `NotAdmitted`。成功时，循环
调用真实的 `admit`、`step` 直到终态，证明每次调用成功、由剩余指令量与终态标记组成的
递减量严格下降，并满足
`count.steps == count.writes + 1`。其中包括最后一次 `Finished` 调用，空程序也会计入
这一调用；写入次数不超过初始剩余指令数。这是解释器调用计数，不是整个论文生命周期
的步数。拒绝不会修改资源、执行位置或日志深度；接纳检查可能将目标不匹配的 episode
标为取消、结束。

`execute_and_recover` 不要求调用方预先假设操作成功或 target 相等。它在且仅在程序
合法、target 与传入的 committed 向量包含的完整绑定身份集合相等时成功：实际构造
episode，执行它，再调用
真实 `rollback`。后置条件逐个确认返回资源恢复为输入值、无 owner、深度为零；返回的
计数来自这次真实执行。非法指令返回 `InvalidInstruction`；合法程序的目标不匹配时
返回 `NotAdmitted`。

该范围是调用期间 target 固定的同步指令语言，覆盖数据相关分支及真实 Journal 逆操作。
它不包含动态 child、一般 Future、目标变化或服务发布要求。这是具体的有限执行与恢复
证明，还不是整个宿主的全局静止定理。

## 将单个 Fresh actor 运行到终态或首个错误

[`FreshDriver::run_until_blocked`](../crates/cordis-kernel/src/fresh_run.rs) 位于
`mixed_driver::fresh::runner`，循环调用真实的事务 `step`。它只要求已有 `wf()`，
不需要调用者传入 fuel、未来成功前提或源轨迹。重新导出的 `RunReport` 提供运行时
字段 `steps: u128` 与 `error: Option<DriverError>`。

循环遇到首个真实 step 错误，或 `Outcome::Finished`／finished Child 时返回。
没有错误时，`run_finished` 保证 actor 已登记且 Active，并且没有当前指令。
出错时，已经提交的成功前缀保留，只回滚失败的那一步；整个 run 不是撤销先前全部
工作的单个事务。未知、Inactive 或已经 Active 的 actor 仍返回既有 step 错误，
不会被静默当作一次成功执行。

递减秩来自真实程序的剩余向前位置：有效当前位置的
`run_budget = code.len() - pc + 1`。位置无效或缺失时秩为一，让真实 step 调用
报告错误。额外的一计入可能的终态 Unit 调用；向前跳转可以跳过位置，因此这是上界，
不是精确执行长度。`steps` 统计已提交调用，包括终态调用，不统计最后失败的尝试。
已检查的后置条件包括：

- `steps <=` 调用前的 `run_budget`。
- 没有提交任何一步时，完整机器与输入满足 `same`。
- 出错时，`steps + 1 <=` 该输入预算，且最终 actor 不满足 `step_enabled`。
- 无错误时至少已提交一步，且 `run_finished(actor)` 成立。
- actor 在输入分配器范围内时，其 journal 长度恰好增加 `steps`，保留成功效果与
  inverse 前缀。

空程序仍执行一次终态 Unit；向前跳到代码末尾也仍需执行该 Unit。新建 child 保持
Inactive：循环注册它并捕获 inverse，但不自动 Begin 或运行 child 程序。
因此当前 actor 进入 Active 并不意味着全部 actor 已静止。

refinement 的输入边界单独保留。`RunReport::refines` 的含义是：**对输入机器已经
表示的任意良构源配置**，构造恰好包含真实成功调用的源执行扩展，并使最终机器表示其
终点。`source_chain` 从实际调用的 acknowledgement 推出该序列，不要求调用者假设
成功结果。公共 proof 方法 `RunReport::advance_source` 在已建立 `refines`、输入
representation 和源良构的条件下提取该有限源执行，供后续证明组合。这条条件化扩展
不会从任意 `wf()` 输入推导出这样的源状态一定存在。
下述 `run_from_empty` 入口通过真实 `run_script` 调用建立到达该输入机器的路径，
并组合两段源执行。仅供证明的 outcomes、机器快照和源状态序列都是 ghost 数据，由可执行
Rust 擦除；不会为这份证明分配运行时历史缓冲区。

[Fresh driver 回归](../crates/cordis-kernel/tests/fresh_driver.rs)覆盖跳转、
Xor/Child/Provide 执行、终态发布、阻塞前缀的恢复、终态 child 回滚、空程序和错误
phase。这证明单个已安装同步程序会有限返回，不会把 strict primitive 变成全域操作，
不会运行全部 child，也不保证最终解除阻塞，或为整个动态注册表／异步宿主实例化
定理 73。

## 真实 LIFO 清理的精确定义域

[`MixedDriver::unload_enabled`](../crates/cordis-kernel/src/mixed_driver.rs)
组合两个独立条件：

```text
kernel.cleanup_enabled(actor)
    && restore_receipts(journal(actor), primitive_state).is_some()
```

第一个是真实清理守卫：actor 已登记、Unloading、尚未恢复且没有存活的 committed
dependent。第二个在当前 primitive 状态上，用 `mixed_grammar::undo` 从后向前解释
实际保留的 receipts，并要求整段有定义。它不是假设下一次调用成功的标志。该谓词只用于
证明；真实方法仍依次调用 `begin_cleanup`、执行实际逆日志，再调用 `finish_cleanup`。

在已有 `wf()` 下，公共 `MixedDriver::unload` 和 `FreshDriver::unload` **在且仅在**
输入满足 `unload_enabled` 时成功。`FreshDriver::same_unload_domain` 证明完整
`same` 的机器具有相同定义域。receipt 的 owner 已登记且 Unloading 时，内部
`undo_one` 在且仅在该 receipt 的模型 undo 有定义时成功，成功后的 `primitive_state` 等于模型 undo 结果，并保持全部 Kernel restoring 标志。循环维持
当前 actor 正在恢复，每次成功逆操作后移除一条 receipt，以真实 journal 长度为递减量。
`unload_inner` 有相同成功等价合同，成功时建立 journal 为空、没有当前指令，actor 在
模型恢复及释放 commitment 后为 Inactive。公共包装层将结果接到已有的 Unload
refinement acknowledgement。

一次失败的 `undo_one` 保持它自己的输入；但 `unload_inner` 在后续 inverse 失败前，
可能已经进入清理并恢复了更晚落地的 receipts，因此其失败没有完整机器回滚合同。
公共包装层在副本上执行，仅成功时发布，所以**公共错误保持完整输入机器**，包括值、
receipts 与清理状态。Child inverse 退休捕获的 child，不移除注册项，不执行该 child
自身的清理，也不回退分配器。

这是精确接纳与有限返回合同，并未证明 `wf()`、`!relied` 或清理许可足以让任意逆日志
都可恢复。完整逆序列的有定义性仍是显式合取条件。对引理 57，它将真实 inverse 实现
接到 strict 源语法；对推论 69，它补充模型恢复的执行证据，一般 foreign replay 的
观察等价方程与 owner 表为空仍需相应历史及独立性论证，不承诺任意外部资源物理复原。
对定理 73，它把允许且有定义的清理接到一次真实有限调用，不证明动态 child 全局进展
或最终调度。这三项在清单中均保持 **partial**。

准备 dispatcher 的精确范围仍只有 Insert/Begin/Step。直接 `FreshDriver::unload`
调用已有新合同，但 `preparation_command` 不包含 Unload，通用 `apply` 的成功等价
未扩大。[已有 Mixed driver 测试](../crates/cordis-kernel/tests/mixed_driver.rs)覆盖
被依赖 provider 的清理拒绝、捕获的 provider 与混合 Xor/Child/Xor 恢复；测试补充合同，
不能证明任意 inverse 都有定义。

## 从新机器经过真实准备与执行

[`run_from_empty(blueprints, setup_commands, actor)`](../crates/cordis-kernel/src/fresh_bootstrap.rs)
是可执行入口，由 `mixed_driver::fresh` 与 `FromEmptyReport`、`FromEmptyStatus`
一起重新导出。它构造新机器，调用真实 `run_script`，仅当所有准备命令成功后才调用
`run_until_blocked(actor)`。调用者不传机器、源执行见证、fuel，也不假设未来调用成功。

| 返回状态 | 实际停止位置与已检查报告 |
| --- | --- |
| `SetupFailed(error)` | 准备阶段在第一次真实调用返回错误时停止。`setup` 是比输入命令列表短的成功前缀，`steps == 0`，没有调用自主执行循环。所选 actor 仍可能已使能。 |
| `Blocked(error)` | 所有准备命令已成功；自主循环在首个错误处停止并保留提交前缀。最终 actor 不满足 `step_enabled`，且 `steps + 1 <= prepared.run_budget(actor)`。 |
| `Finished` | 所有准备命令已成功，自主循环到达终态发布。`steps > 0`，actor 为 Active 且没有当前指令，`steps <= prepared.run_budget(actor)`。 |

`setup: Vec<Transition>` 记录真实成功的准备调用，包括传入脚本中的 `Command::Step`。
`steps: u128` 只统计随后自主循环的已提交调用，包含终态调用，不包含准备调用或失败尝试。
自主步骤为零时，完整返回机器与准备后的机器满足 `same`。不能把准备失败理解成所选
actor 被阻塞：另一个 actor 的准备命令可能失败，而所选 actor 已经 ready。

`FromEmptyReport::refines` 无需调用者提供输入 representation，直接建立**一条从
empty 出发的源执行**。同一条执行在准备接缝处表示真实 prepared 机器，在终点表示返回
机器；每个源状态都良构且 `resource_safe`。准备见证建立原有条件化
`RunReport::advance_source` 所需前提；`concatenate` 在两段相同的接缝状态连接，
只保留一次该状态，不增加管理步骤或失败事件。公共 proof 方法
`FromEmptyReport::source_execution` 提取这条已建立的执行供进一步组合。
prepared 快照、自主 outcomes 和源状态都是运行时擦除的 ghost 数据；成功准备记录的
`Vec<Transition>` 仍是运行时分配。

准备命令已有一个精确定义域范围：
[`preparation_command`](../crates/cordis-kernel/src/fresh_preparation.rs) 只选取
`Insert`、`Begin`、`Step`。这些谓词只用于证明，真实执行分支与错误顺序保持不变。

| 命令 | `preparation_enabled` 使用的当前机器谓词 |
| --- | --- |
| `Insert { parent, blueprint }` | `FreshDriver::insertion_enabled` 复用 Mixed 域：蓝图索引及所需蓝图库前缀合法，并满足 Kernel 对容量、parent、声明与 provision 预留的插入检查。 |
| `Begin { actor }` | `FreshDriver::begin_enabled` 要求 actor 已登记、保留 journal 为空，且满足 Kernel Begin 域，包括 Inactive phase、目标可用和 generation 容量。 |
| `Step { actor }` | 已有 `step_enabled`：actor ready、满足当前 primitive 精确域，终态指令执行后完整发布。 |

对这一范围内的命令，`FreshDriver::apply` **在且仅在**输入机器满足
`preparation_enabled(command)` 时成功。`run_script` 返回错误且失败命令属于该范围
时，返回机器不满足该命令的谓词。`run_from_empty` 的 `SetupFailed` 将这一结论传播
到 `prepared` 和返回机器，失败命令位于 `setup_commands[setup.len()]`。谓词在成功
前缀之后、真实失败处的当前状态求值，并不要求整份脚本的命令在初始 empty 状态就全部
使能；此前成功的命令也可以包含该范围以外的命令。当前命令失败仍不能推出另行指定的
自主 actor 被阻塞。

`Retire`、`Depart`、`Unload`、`Remove` 仍由 dispatcher 正常支持。
`preparation_enabled` 对它们返回 false，只因为它们不属于这一证明范围；成功等价条件
受 `preparation_command` 限制，这不是拒绝这些命令的声明。直接 Unload 已有上文的
独立精确域，但 dispatcher 范围未扩大；其余命令的域与 dispatcher 等价仍须补齐。
合同也尚未逐个从输入谓词刻画 `Unknown`、`Retained` 等具体错误枚举值。这里证明的是
明确实现域内的接纳，保留蓝图合法性、有限容量和 strict 值可用性约束，并不保证所有
论文中已使能的准备命令都被接纳。原有成功前缀的源执行结论保持不变。

[Bootstrap 回归](../crates/cordis-kernel/tests/fresh_bootstrap.rs)覆盖 actor 已使能时
准备失败、成功准备加执行与恢复、strict primitive 阻塞、空准备、准备期间已完成的
actor、provider 发布后才使能的 Begin、非法蓝图库前缀、已登记 provision 预留及
Begin/Step 失败时的前缀保留。新 child 仍保持 Inactive。这个真实入口关闭了初始源
状态存在性缺口；整个系统的
进展仍需多个 actor、child 执行、恢复域与全局递减量的连接。引理 57 和定理 73 仍为
**partial**。

## 更完整进展结论还缺什么

1. **完整宿主捕获与执行。** 共享比较和已验证 driver 的捕获证明已关闭向量顺序／
   重复次数缺口。普通 Rust／Node 宿主仍需证明：异步执行全过程中的真实捕获值、episode
   身份、可用性检查和发布边界都符合这些合同。调用已验证的 matcher 不等于外围宿主
   已获得 refinement 证明。
2. **一般 continuation 定义域。** 固定程序的构造函数从实际检查导出定义域与向前
   递减量；动态 child 注册也已有精确输入域合同，同步 Mixed/Fresh 单步现已公开
   精确效果域与终态发布域，拥有机器的接纳协议也在跨已检查调用后重新检查精确落地域。
   一般 child body 与任意回调仍需各自的定义域连接。Fresh 循环现已推出单个已安装
   actor 有限返回，但它可能报告 primitive 被阻塞，并未建立全部动态程序的总性或
   最终成功完成。严格守卫的 child 案例依然是边界。
   增加失败出口会改变转换系统，需要单独审查。
3. **整个系统执行的组合与准备／恢复域。** `run_from_empty` 现已通过真实准备建立
   初始源状态并组合单个 actor 的执行，无需把这一入口前提留给调用者。
   Insert/Begin/Step 准备范围已有精确接纳域，直接 Mixed/Fresh Unload 也已有守卫加
   inverse 的精确域。Retire/Depart/Remove、更广的 dispatcher 与其他恢复路径仍需
   定义域等价；从可达历史推出逆操作有定义，与执行有定义的逆序列仍是不同义务。
   准备谓词也未刻画具体错误枚举值。还须组合多个 actor、
   动态 child 与恢复，接到论文的全局计数／递减量论证。这些入口没有为整个宿主实例化 `termination.rs`。若目标命题
   包含可能延迟已使能生命周期工作的宿主执行，还须明确调度合同。

生产共享 Driver 还接入了[已验证清理结果协议](cleanup-protocol.zh-CN.md)，
将精确动作完成、显式失败／重试与真实的 commitment 释放调用连接起来。
这是局部安全合同；宿主回调结果、外部效果以及最终获得调度仍是独立义务。

## 这里需要 verus-tla 吗

**本轮合同修复不需要。** 普通 Verus 已能表达并检查状态谓词、成功等价条件、带递减量的真实执行循环、
资源恢复和有限轨迹论证。本轮没有增加 Cargo 或运行时依赖。

[`verus-tla`](https://github.com/anvil-verifier/verus-tla) 提供可复用的时序逻辑定义和
证明规则。如果之后明确要证明无限宿主执行上的性质，它可以有帮助。例如：取消后的阶段
已经收到终态回复，且持续可执行的推进动作最终会被调度，那么阶段最终会结束。首先仍须
证明真实推进函数实现了该时序动作，并显式保留调度和回复前提；引入库不会自动证明前提。

按“论文约束对应实际代码”的主线，下一步应优先补上剩余的完整宿主捕获和 continuation
连接。
先明确需要什么命题，再决定是否借助时序库；不能用一份未连接实现的时序模型代替尚未
完整的真实代码合同。

## 复现检查

在仓库根目录、固定工具链及依赖已缓存的环境中运行：

```sh
cargo test --offline -p cordis-kernel --lib iteration_tests
cargo test --offline -p cordis-kernel --test insert_domain
cargo test --offline -p cordis-kernel --test program checked_
cargo test --offline -p cordis-kernel --test episode_protocol
cargo test --offline -p cordis-kernel --test ownership
cargo test --offline -p cordis-kernel --test child_driver
cargo test --offline -p cordis-kernel --test mixed_driver
cargo test --offline -p cordis-kernel --test fresh_driver
cargo test --offline -p cordis-kernel --test fresh_bootstrap
cargo test --offline -p cordis-kernel --test admitted_fresh_driver
cargo test --offline -p cordis-kernel --test admitted_script
cargo test --offline -p cordis-kernel --test driver
cargo test --offline -p cordis-kernel --test episode_identity
python3 scripts/check-paper-coverage.py
python3 scripts/check-paper-review.py
python3 scripts/record-development.py --offline
```

开发记录器会运行启用 `--no-cheating` 的完整内核验证、编译、Rust 测试、Node 兼容测试
及打包检查。[记录文件](development-report.json)通过源码哈希绑定检查结果；它不等于
完整发布门禁，也不替代全部标准负向对照。
