# 论文 v1 的机械化审计

审计对象是锁定的 [A Programming Paradigm for Spatiotemporal Composability, arXiv:2608.25512v1](https://arxiv.org/abs/2608.25512v1)，重点为 §4.2–4.3。论文 PDF 哈希和来源见 [研究输入](../reference/README.md)。这里的页码是 PDF 页码。

本项目确认了 Lemma 62、75、77 及 Theorem 71(2) 无条件闭合断言的原文反例：
它们只用 Unit 和相应编排／生命周期规则，直接证明全域 identity witness。Child 的交换、删除和 canonical ordering 见证则先限定于
full-State 九规则编码，所用模型尚未完整实例化到原文 Definition 48／56 的全域
组件类型。因此 78／79／80 保持 partial；保留反例证据及适用范围，
不把它们写成原文全部前提下的无条件反驳。严格 guarded fresh-binder 的字面同名
输入见证也有同样的表示边界。整篇原文证明尚未完成。

这里缺的不是多跑一次 Verus：`paper_counterexamples::creation_model` 的实际 Child
调用满足 fresh Insert、局部 inverse witness 和 preservation，但它在离迹输入上
无条件覆盖固定 child，并未证明属于原文的 full Γ grammar。即使空接口观察关系
使部分强 witness 容易成立，也还须解释这种离迹行为与 Definition 52 fresh 操作的关系。
下文明确区分原文反例、编码规则内的障碍、已验证修订结论和未完成义务。

## 定义与实现加强条件

`paper_invariants::registry` 单独编码 Definition 63 的四条；实现还要求 committed
provider 不等于 consumer、provider 声明被绑定的 key。已证明实现不变量蕴含原四条，
反向不成立。一个有限 self-committed 状态满足原文的形状与四条，但不能从 empty 的
Begin 自举得到；这个区别不能省略为“论文良构与实现良构相同”。

Definition 76 的 total provision 是组件级性质，需要量化完成执行。仅检查某个状态
中的 Active 表域，会在所有节点 Inactive 时真值为空成立。新定义区分通用 iterator
完成总性、真实交错 activation 总性和当前状态后果；Unit 声明非空 provision 后实际
合法 Finish，却没有发布该键，机械化说明三者不能混同。通用完成与全域交错组件的
表示连接仍须证明。这两处修正的是本项目的编码边界，不是原文反例。

## Lemma 62：残留条目仍影响父子守卫

论文 p42 的 vestigial 定义要求条目 retired、Inactive、服务表为空、没有 child。它没有要求该条目没有 parent，也没有禁止后续 O-Insert 以它为 parent。

第一个反例只需两个空条目：

| 名称 | parent | retired | phase | 服务表 |
| --- | --- | --- | --- | --- |
| `p` | root | true | Inactive | 空 |
| `c` | `p` | true | Inactive | 空 |

从空 registry 依次 insert `p`、insert `c`、retire `c`、retire `p` 可达。`c` 是 vestigial，但 O-Remove(`p`) 在原状态被 child 守卫阻止，擦除 `c` 后才允许执行。Lemma 62(2) 所列例外只有两种 O-Insert 情况，遗漏了这个 O-Remove。

第二个反例在只有 retired、Inactive、空表、无 child 的 `p` 时出现：O-Insert 一个 fresh child 并令 parent=`p` 满足原规则。擦除 `p` 后，parent 不存在，同一步不再合法；保留 `p` 并完成插入后，它也不再 vestigial。这同时违反 Lemma 62(1) 的可执行性和“仍是 vestigial”两项陈述。

[semantics.rs](../crates/cordis-kernel/src/semantics.rs) 中的 `vestigial_parent_counterexample`、`vestigial_insert_counterexample` 将这两个失败条件写为 Verus 结论；`counterexample_reachable` 给出四步严格控制轨迹，`counterexample_reachable_full` 用惰性 Model、空服务表和完整辅助字段证明对应的四步完整规则可达性。[paper_vestige.rs](../crates/cordis-kernel/tests/paper_vestige.rs) 在真实 Kernel 上复现。

已证明的局部修正是：

- `vestigial_removal_guard`：原状态没有 `p` 的 child，当且仅当擦除后的状态没有 `p` 的 child，且被擦除条目的 parent 不是 `p`。
- `vestigial_insert_forward`：O-Insert 的新 parent 不能是被擦除条目；其它 fresh-name、provision 冲突条件仍须保留。
- `vestigial_observations`：target 和 relied 确实不观察 vestigial 条目。这个较弱结论不能替换所有规则的双向模拟。

实现也因此修正了 raw `Kernel::insert`：只要求 parent 注册，允许已获 admission 的 child stage 在 parent retired 后落地。普通宿主主动 mount 的 phase/retirement 检查仍由 Runtime 执行；这两个调用边界需要分别描述。

## Theorem 71(2)：离开 Loading 不等于本序列已经闭合

Definition 58（p39）明确允许最后一个 episode 不闭合。Theorem 71（p48）却在
`r < u` 且离开 Loading 的规则为 Divert 时，无条件断言 episode 在某个 `u > r`
闭合；该定理没有公平性或最大执行的前提。

`resolution_completion_counterexample::actual_counterexample` 从 empty 构造四步：
Insert(0)、Begin(0)、Retire(0)、aborting Divert(0)，然后序列结束。组件的空声明
Unit 在所有状态上都有强 witness 并终止；同一轨迹同时满足真实解释器和 total Unit
Model 的规则。episode 为 `[2,4]`，Loading 区间为 `[2,3]`，`step_3=Divert` 且
`3<4`，末状态是仍 installed 的 Unloading，序列里没有 Unload。闭合谓词显式要求
后继存在于本序列，不用越界状态，也不把“存在可追加的一步”替换成实际已经闭合。

末状态的 Unload 确实 enabled。`arbitrary_delay(count)` 还证明任意有限数量的
O-Retire 可以推迟它；这些轨迹不声称最大或公平。反例只否定原文(2)的无条件闭合，
不否定固定 committed resolution、Finish/Divert 二分，也不否定在实际 Unload 后
成立的条件恢复。修订陈述应以实际闭合为条件，或另列足够的调度／进展前提。

## Lemma 75：纯外部编排也能形成混合环

主见证位于 [orchestration_support_cycle.rs](../crates/cordis-kernel/src/orchestration_support_cycle.rs)。
它从 empty 只执行六条外部规则，没有 activation 或 Child primitive：

1. Insert `P`，声明提供 `x`。
2. Insert root `A`，依赖 `x`。
3. Insert `C`，parent=`A`，依赖 `z`、声明提供 `y`。
4. Retire `P`。
5. Remove `P`。
6. Insert root `D`，依赖 `y`、声明提供 `x`。

全部组件使用同一个总 Unit 程序；所有条目保持 Inactive，表和历史为空。最终 provider
precedence 是 `C → D → A`，有明确 rank；加入 parent 边 `A → C` 后形成环。
`provider_rankings` 同时证明每个实际前缀及完整历史接口 catalogue 的 provider 图有
rank，`catalogue_provenance` 证明 catalogue 中每个名字确实曾经注册。

`total_unit/component_witness` 直接证明任意状态类型上的总 Unit 强 witness，再实例化
到论文的表观察；`actual_execution` 同时给出 mixed grammar 和固定 total Unit Model
下的完整六步执行。因此该反例不依赖 Child 的严格 partial 域，也不借未完成的
Lemma 57 代替组件实例化。Lemma 75 不要求后面的 Definition 76 total provision，
本例也不声称满足它。

原 O-Insert 明确允许任意 registered parent。Definition 74 的说明却把所有 nonroot
条目当作父 activation 创建，Lemma 75 的论证使用了这个未写入外部规则的限制。
`quiet_mixed_cycle` 证明终态静止且混合关系不可排序；`support_still_unique` 另证明
本例的 support 解唯一为空。因此反驳的是良基性结论，不能进一步宣称 support
必不唯一或一般 confluence 已被推翻。

旧的 `global::replacement_cycle_reachable` 及真实 Kernel 的
[paper_support.rs](../crates/cordis-kernel/tests/paper_support.rs) 保留为含 Child 的
实现回归；现在的原文反例以这个独立、纯 Unit 的六步见证为依据。

## 已验证的替代控制唯一性证明

`quiet_active_unique_by_precedence` 直接从静止状态的 target 方程沿 provider precedence 归纳，证明 Active 集合唯一。它无需 parent/provider 合并图有 rank，也无需 retirement closure。

`quiet_control_unique` 进一步证明两个完整控制 registry 相等，包括 phase 和确切 committed provider identities。前提为两个状态均良构、静止，拥有相同注册名、parent、依赖、provision、retired 输入，并且 provider precedence 有显式 rank。这里采用 Active 发布全部声明端口的特化；一般服务表需要 `total_active` 对应证明。

这提供了不依赖错误 Lemma 75 的控制正常形唯一性。这个控制定理本身不覆盖服务值及 inverse 历史；`program_normal_form::driver_quiet_confluence` 已为实际固定程序 API 历史补齐这两者，范围是私有 provision cells 的语言。另有 `alpha` 的完整规则名字重命名/fresh allocation 匹配，和 `canonical` 的动态独立 family 调度、合法 owner 删除；不同动态 registry 的完整闭合 episode 删除仍未由这些局部结果连通。

## Lemma 77：外部子节点不受父 activation 支配

原 O-Insert 只要求 parent 已注册，不要求 parent Active 或未退休。以下五条完整规则从空状态到达 quiet：

1. O-Insert 创建 root `p`，依赖与 provision 都为空。
2. O-Retire(`p`)，`p` 保持 Inactive。
3. 外部 O-Insert 创建 `c`，parent=`p`，依赖与 provision 为空。
4. L-Begin(`c`)。
5. L-Finish(`c`)，idle stage 返回 identity inverse。

终态 `c` Active、`p` Inactive/retired。状态良构、quiet、满足 total provision，provider precedence 为空，parent/provider 合并图也有 rank。但原 Definition 74 的 parent clause 要求 child 被支持时 parent 也被支持，因此 Active 集不是该方程的解。反例不依赖 Lemma 75 的混合环，也没有错误地把 ownership 当成服务依赖。Definition 74 后文将外部插入等同于 root，与 §4.2.1 可选择任意 registered parent 的规则不一致；这里反驳的是按该打印规则得到的结论。显式加 external-roots 限制会排除此见证，但会收窄原规则。

[child_history.rs](../crates/cordis-kernel/src/child_history.rs) 的 `external_parent_support_counterexample` 证明全部五步、上述前提及失败结论；[paper_child_support.rs](../crates/cordis-kernel/tests/paper_child_support.rs) 在实际 Kernel 上复现。

一般 birth/history invariant 单独不阻止先删除 retired child、再复用名称导致旧 token 指向新对象；后述全 accumulator retention 协议才排除这种 ABA。

该模块的正向结果从真实 trace 计算 `Birth {parent, episode, landed_at, inverse}`，将出生记录定位到实际 child yield，并在恢复时从父 accumulator 找到对应 inverse。于是 lifecycle-born child 的退休闭包可从执行导出。若所有非根 child 均由 lifecycle 创建，`quiet_support_from_creation_history` 得到原 support 方程；外部只插入 root 是满足该前提的一种显式附加 profile。

保留一般 O-Insert 时，`origin_support_clause` 只对 lifecycle-born child 加 creator 支持条件，外部插入的 parent 保持 ownership 含义。`execution_quiet_origin_support` 证明真实 quiet 终态的 Active 集满足此修订方程。它是已验证的修订结论，不是原 Lemma 77 的证明，也不等于所有 support 解或完整 lifecycle 正常形的唯一性。

## Lemma 78(2)：插入的 parent 可能由前一步创建

论文 pp52–53 允许 activation 与不同 fiber 上的 orchestration 交换，只排除 activation 创建该 orchestration 的目标名称。这个条件遗漏了 O-Insert 读取的新 parent。

从空 registry 依次执行四条完整规则：

1. O-Insert 创建 root `m`，没有 dependencies/provisions。
2. L-Begin(`m`) 提交空 target。
3. L-Finish(`m`) 的实际 iterator yield 创建 child `k`，并返回 `Retire(k)` inverse。
4. O-Insert 创建 `n`，令 parent=`k`。

`m` 与 `n` 不同，前一 stage 创建的是 `k` 而不是 `n`，满足原文列出的排除条件。第四步若移到第三步以前，`k` 尚未注册，因此 parent guard 失败；不存在相同 parent 的逆序 O-Insert。原文 O-Insert 的 parent 前提允许任意已注册名称，并未将外部 orchestration 限制为 root 插入。

[paper_counterexamples.rs](../crates/cordis-kernel/src/paper_counterexamples.rs) 的 `transposition_parent_counterexample` 证明两步完整规则合法、相关状态良构和逆序不可用，并保留真实 child retirement inverse 的 table 恢复观察；`transposition_counterexample_reachable` 给出从空状态的四步完整可达性。child 创建保留在实际 yield 中，没有展开成额外 orchestration。真实 Kernel 回归见 [paper_transposition.rs](../crates/cordis-kernel/tests/paper_transposition.rs)。

`mixed_transposition::observed_pair` 已给出对应的局部正向修订：从真实 Child landing／O-Insert 两步，排除新 parent 等于刚出生的 child 后，构造并证明反序执行。最终完整状态、roots 和 current 相等，receipts 对应，但每条新历史记录仍保存自己的实际输入。`concrete_diamond` 与 `concrete_parent_rejection` 分别检验非空 provision 正例及被遗漏的 parent／provision 守卫；`mixed_transport::child_diamond_suffix` 进一步构造同标签的任意已合法有限 suffix 并证明所有对应状态相等；它仍未给出所有 orchestration 的全局排序或完整 canonical form。

`mixed_orchestration::orchestration_diamond` 现将这个局部修订扩展到所有 mixed 节点和 Insert／Retire／Remove：Insert parent 已在原前缀存在，Retire 目标已存在且不同于 acting fiber，Remove 则从原始合法后置删除推导逆序守卫。它使用观察 primitive witness，保留实际 inverse、历史来源和严格失败域，并构造任意已合法有限 suffix 的同标签对应。局部可交换不等于所有编排均能前置，也不等于全局 confluence。

修正至少要跟踪 orchestration 读取的名称，包括新 parent，不能仅检查目标名称是否由跨越的 stage 创建。限制外部插入只允许 root 也是可能的规范改动，但那是新增限制，不能声称原文已有该条件。这个见证可扩展到静止终态，进一步检验编码规则中的 Theorem 80(1) ordering，见下一节。

## Lemma 79：删除出生 episode 会破坏外部 parent 引用

Lemma 79 的前提没有禁止外部插入引用 episode 创建的名称。下面八条完整规则满足原引理列出的 quiet、total provision 和 episode 条件：

1. O-Insert 创建 root `n`。
2. L-Begin(`n`)。
3. L-Finish(`n`) 的实际 yield 创建 child `r`，返回 `Retire(r)` inverse。
4. 外部 O-Insert 创建 `m`，parent=`r`。
5. O-Retire(`m`)。
6. O-Retire(`n`)。
7. L-Leave(`n`)。
8. L-Unload(`n`) 执行真正的 child inverse，退休 `r`。

所有 dependencies/provisions 都为空，最终三个条目均 retired、Inactive、空表，状态 quiet。只有 `n` 有 episode，并且已经闭合；`r` 和 `m` 从未激活。因此没有依赖 `n` 的闭合 episode，`n` 创建的 `r` 也没有 episode。可是 `r` 有 child `m`，不是证明声称的 vestigial。删除 `n` 的 episode 后，保留的 `Insert(m,parent=r)` 找不到 parent；删除步骤作用的名称集合只含 `r`，不会同时删除作用于 `m` 的这条输入。

[deletion.rs](../crates/cordis-kernel/src/deletion.rs) 的 `deletion_counterexample_quiet` 证明八步完整且局部 admissible 的执行、所有上述前提和失败的 vestigial 条件；`deletion_counterexample_prefix_impossible` 证明保留插入的前缀不存在，即使按原 episode 下标保留 opening Begin 也不成立。[paper_deletion.rs](../crates/cordis-kernel/tests/paper_deletion.rs) 用真实 `ChildEpisode`、child inverse 和 Kernel parent guard 复现。

修订的 `full_step_bisimulation` 覆盖九条完整规则，两种 Divert 及实际 LIFO restore；需要 primitive 的擦除/保留合同，以及 parent 读取、父删除和 provision 冲突的正确例外。`suffix_deletion` 从原 suffix 构造并证明合法的删减轨迹，删除真实 Retire/Remove，保留末端服务表观察。`unload_born_leaf_vestigial` 从出生历史、仍保留的实际 inverse token 与完整 Unload 推导退休和空表，但必须要求没有 descendant 引用这个 child。它没有假设最终已 vestigial，也没有把 suffix 定理当成整个闭合 episode 删除。

## Theorem 80(1)：所要求的 canonical 顺序不存在

将上述第 4 步之后的 `k` 和 `n` 各用 idle component 激活，得到从空 registry 出发的 8 步执行。最终 `m/k/n` 全部 Active，所有 declarations/provisions 为空，状态 quiet、良构且满足 total provision。provider precedence 为空；parent 图为 `m → k → n`，support 图也有 rank。反例因此不依赖 Lemma 75 的混合环。

原执行只有两个外部 orchestration 输入：`Insert(m, root)` 和 `Insert(n, parent=k)`。Theorem 80(1) 要求在 orchestrator 插入的 fiber 上发生的 orchestration 先于每个 lifecycle 步；这包括两个 Insert，且要保留它们的原顺序。但执行第一个 Insert 后，registry 只有 `m`。`k` 必须等 `m` 的 lifecycle stage 才出现，第二个 Insert 的 parent guard 因而不能成立。没有满足所述顺序的前缀，也就没有该形态的 canonical 执行。三个 fiber 最终都 Active，没有可删除的闭合 episode。

`canonical_counterexample_quiet` 机械化证明这条 8 步完整规则轨迹、静止性、total provision、有效 provider/support rank 和支持集；`canonical_orchestration_prefix_impossible` 证明所需的两输入前缀不存在。通用的 `missing_parent_prefix` 对任意三个不同名称成立，双射重命名不能生成尚不存在的 parent。

这里是编码的完整九规则、实际 child primitive 和局部 typed map 的合法 trace 见证。它机械否定该编码下的 orchestration-first ordering；原文 Definition 48／56 的全域组件实例尚缺，故不能升格为原文 80(1) 的无条件反驳，也不反驳原文 80(2)。

修订版可以保留 O-Insert 的能力，把 canonical 输入顺序改成尊重所有被读取名称的创建依赖；或者显式限制外部插入只能为 root。后者会收窄原规则。两种修订都需要新的统一证明，不能用现有局部交换定理直接宣布完成。

## Theorem 80(2) 的解释边界：字面同名输入与出生对象引用

原文 p54 说两个执行采取相同 orchestration steps；p55 的证明先按出生树选择双射，再直接使用“相同外部退休”。Lemma 61 的重命名却也作用于规则标签的 actor，因此这里需要明确输入本身如何对应。

[allocation_inputs.rs](../crates/cordis-kernel/src/allocation_inputs.rs) 给出同一个固定 fresh-binder 程序的两条九步轨迹。root 0 的组件创建提供 A 的 child，root 1 的组件创建提供 B 的 child；两者都不观察、比较或选择名称的数值，且已证明程序 naturality。外部输入完全相同：`Insert(0, SpawnA)`、`Insert(1, SpawnB)`、`Retire(2)`。

| 生命周期调度 | 名称 2 的来源 | 名称 3 的来源 | 退休 2 后激活 3 的服务 |
| --- | --- | --- | --- |
| 先激活 root 0，再激活 root 1 | A child | B child | B |
| 先激活 root 1，再激活 root 0 | B child | A child | A |

两个执行均从 empty 开始。每个前缀只使用四个名字，dependency 图为空，parent/support 图有 rank；每个组件最多一次 landing，所有成功完成的组件都装满声明的 provision。最终均为 quiet，退休的 child 2 保持 Inactive 空表。全表投影的 key 域分别是 `{B}` 和 `{A}`，任何 fiber 名称双射都不能重命名服务 key，因此终态连最粗的全表观察也不相等。`total_component` 对所有良构输入证明成功完成时装满 provision；`bounded_catalogue` 将该条件及有限名称、rank、阶段界连接到两条实际轨迹。

这精确否定已编码严格 guarded fresh-binder 解释中的“字面相同具名外部输入足以推出汇合”。它证明 least-grammar membership、naturality 及 Definition 76 意义的 total-on-provision，却没有证明原文 Definition 37／48 的全域 Γ iterator witness：片段之外已有同 key 的 child 声明时，完整 O-Insert 守卫会拒绝创建，即使两侧表观察相同。Definition 52 的 guarded primitive 与原文全域 witness 的对应仍须另证，所以不能把此见证升级为原文所有前提下的无条件反驳。若输入用出生对象的稳定引用解释，则左边针对 A child 的 `Retire(2)` 应运输为右边的 `Retire(3)`；这两个外部输入不再对应，反例被排除。`external_inputs::execution_inputs` 证明完整 Insert actor／parent／root 及 Retire／Remove 的运输，`literal_stream` 给出字面相等所需的固定点条件。原文应明确采用这种输入运输，或限制外部输入仅引用被重命名固定的外部 root。该修订下的一般汇合仍需证明，不能由这个反例或局部交换定理自动得出。

## Guarded child 的成功域与进度边界

[guarded_child_domains.rs](../crates/cordis-kernel/src/guarded_child_domains.rs)
把上述 witness 缺口本身机械化。`pending_domain_gap` 的两个输入均来自真实的
empty 前缀，均是同一 actor 的 coherent Loading 状态，current 与 committed
完全相同，任意 key 集的服务投影也相同。同一个 fresh child 名称在两边均未注册，
但一侧已有空表、Inactive child 声明相同的 provision，因此创建在一边成功、
另一边失败。`domain_respect_failure` 由此否定该解释的严格成功域观察不变性；
仅保留 successful calls 的条件会被对应负控拒绝。

`strict_progress_boundary` 进一步给出同一固定 natural 程序从 empty 的七步执行：
两个 root 都准备创建声明 A 的 child，第一个创建成功并使 child 完成发布，第二个
root 留在 Loading。此时状态不是 quiet，但六种 core lifecycle 规则都无法继续。
轨迹仅用三个名字，dependency 为空，有 support rank，每个组件至多一次 landing，
所有成功 Finish 均完整提供服务。这说明这些有限性和 total-on-provision 条件
不足以保证严格 partial 解释的进度；原文全域 iterator witness 仍是独立义务。
它不无条件反驳原 Theorem 73，也不涵盖额外加入失败退出的扩展规则。

## Definition 52：child inverse 的定义域

child creation 的 inverse 调用 O-Retire。O-Retire 要求 child 仍存在；若外部 orchestration 已 retire 并 remove child，原样的 inverse 就不能应用。原文 p35 的全局 totality 表述需要补充条件或扩展操作。

[ownership.rs](../crates/cordis-kernel/src/ownership.rs) 的 `ChildEpisode` 保存实际 fresh child identity；rollback 实际调用 `Kernel::retire(child)`。完整恢复成立的 `retirable` 条件要求被记录的 children 仍注册。若 child 已删除，`rollback_one` 返回 Unknown 并保留 witness；完整 `rollback` 先检查所有 child，返回 false 且不消费任何 inverse；`finish_restore` 在进入 Kernel cleanup 前返回 Unknown。这些检查在普通 Rust 中也执行，测试覆盖三个入口。可选的语义修正是保留仍有 inverse 引用的 child，或另行定义 absent-child retirement 为幂等操作；当前没有把后者冒充原论文 O-Retire。

严格退休 inverse 现在还有一条单独的保留协议证明：`retained` 检查所有实际 accumulator 中的 child 引用，`remove_unreferenced` 禁止在 inverse 仍引用时移除该身份，即使 child 已 retired。`primitive_inverses` 把 child inverse 解释为实际 retirement，并保留普通 table inverse 的局部合同；`retained_recovery` 推导完整 LIFO 的定义域与恢复合同，`retention_protocol_refines` 从空执行证明这个合同在每次 Unload 成立。这里证明 child 退休、定义域与 table footprint／typing，不证明任意 table inverse 的值恢复或 Theorem 68。该协议是可验证的附加 orchestration 策略，没有偷偷收紧公开 Kernel 的原 O-Remove。新的 `child_driver::ChildDriver` 已在可执行 Rust 中私有持有 Kernel 与 journals，实际扫描引用并返回 `Retained`，且证明其 retention 投影与 `remove_unreferenced` 对应。它把这项修正落实到独立拥有型路径，仍不宣称原文无条件 totality 成立。

## Partial grammar 与 Definition 42 的全域解释

`iterator_bridge` 将严格 partial grammar 的 monoid 与 continuation 最大 bisimulation 相连，但 yield 稳定性仅在 foreign 应用成功时比较。`provisions_refute_totalization` 给出两个合法、key 分离的最小 provision grammar：它们满足严格 partial 独立性，却在 `encode_partial` 的全域 Option context 中不满足 Definition 42，因为 foreign 失败进入 sink，local 的 continuation 从 Some 变为 None。

严格 lifting 保持 definedness-sensitive 的 map 交换；问题出在全域 yield 稳定性，不能靠 map 交换掩盖。这个见证否定的是特定失败编码到全域定义的自动推论，不否定所有受限状态域或其它 partial 解释；Lemma 47 保持 partial，单独列明已经完成的 guarded coinductive 桥接。

## Definition 28：全函数集合解释的障碍

原式 `Γ∞ = μΓ. Γ × (Γ → Γ) × Σ` 若把箭头解释为所有集合函数，并要求 constructor 与三个 projection 的方程成立，则不存在 inhabited、非平凡的 Γ。`recursive_context::unrestricted_accumulator_obstruction` 对 `accumulator(x)(x)` 作对角翻转，将所得函数编码回 Γ 后在自身处得到矛盾。`nontrivial_coeffect_obstruction` 进一步从两个不同 Σ 值构造两个不同 Γ 值，因此普通共享可变状态已触发该障碍。

证明只需 constructor/projection 方程，没有假定函数的表示标识或可计算性。单例投影方程有模型，但不能据此声称 μ 的最小不动点成立。这是对全函数集合解释的精确限制；受限函数语言、递归域或有限层编码不受该命题排除，仍需另外提供模型及语义对应。覆盖清单保留 Definition 28 为 partial，未将所有可能解释一概判为错误。

## 复现与剩余义务

运行 `./scripts/verify.sh --triggers-mode silent` 验证上述反例及修正结论，运行 `cargo test -p cordis-kernel --locked` 复现可执行路径。完整检查及源码哈希见 [verification-report.json](verification-report.json)。负向检查还验证：把 child inverse 改成 retire parent、跳过 Driver 的真实恢复、或让正常形输入忽略 retirement，都会在可编译之后被证明检查拒绝。

整篇 refinement 必须显式采用修正后的 vestigial 模拟、child inverse 定义域、orchestration 名字依赖和控制唯一性路径，再证明完整 lifecycle 历史的交换和删除。任意双射下的完整规则 name-renaming 及不同 fresh allocation 的局部匹配已经机械化；它们不会修复缺失的 parent guard。现有 [Driver](../crates/cordis-kernel/src/driver.rs) 封装真实资源路径与 provider guard，value-carrying 规则规范接入 iterator/continuation/accumulator；它们仍不意味着任意 Rust callback、外部 I/O 或完整异步 Runtime 已满足论文所有效果公理。完整义务清单见 [refinement.md](refinement.md)。

全部 81 个原文编号条目的状态见 [覆盖清单](paper-coverage.md)。`--require-complete` 检查明确拒绝已被反驳的原文引理及未完成的表示／全局连接；普通质量检查通过只证明当前源码契约与清单一致。
