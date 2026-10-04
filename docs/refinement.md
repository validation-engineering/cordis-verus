# 论文 refinement

规范为锁定的 [arXiv:2608.25512v1](https://arxiv.org/abs/2608.25512v1)，尤其是 §4 的九条转换规则。这里给出控制状态、带服务值的完整规则规范、iterator 协议、真实资源/child 组合路径、效果历史和条件进展的机械化关系。审计已确认原文 Lemma 62、75、77 及 Theorem 71(2) 无条件闭合断言的 Unit 反例；另有编码 full-State 规则中的 Child／canonical 反例，其原文全域组件桥接尚待补齐，不能按原文声称整篇已证明；反例及替代证明见 [论文审计](paper-audit.md)。具体证明数、冻结源码和未完成的质量检查见[项目状态](status.md)与[验证说明](validation.md)；当前不附已通过完整发布门槛的 v3 记录。

## 控制状态投影

[refinement.rs](../crates/cordis-kernel/src/refinement.rs) 定义独立的关系规范：registry 是 fiber identity 到 fiber 的映射，每个 fiber 有 parent、retired、phase、依赖集合、provision 集合和 committed 集合。`target` 根据 Active fiber 的 provision 解析 provider identity；`relied` 读取所有 installed consumer 的 committed。规则带有完整的其它 fiber 不变条件 `frame`。

[Kernel::paper](../crates/cordis-kernel/src/lib.rs) 将实际 Vec 存储投影到该规范。投影隐藏已删除 identity、失效绑定、声明的存储顺序和 `restoring` 标志。这不是把 `wf` 改一个名字：转换关系不提 concrete Vec 的索引、历史记录或压缩算法，而具体方法的后置条件需要证明它们确实满足这些关系。

| 可执行操作 | 抽象规则 / 效果 |
| --- | --- |
| `insert` | O-Insert：fresh identity、parent 存在、provision 不冲突、初始 Inactive，其他 fiber 不变 |
| `retire` | O-Retire：只修改 retirement flag |
| `remove` | O-Remove：retired、Inactive、无 committed、没有 child，删除一项 |
| `begin` | L-Begin：提交调用前的完整 target，进入 Loading |
| `check_iteration` | L-Iter 的控制投影：Loading 且 target 等于 committed，控制状态不变 |
| `finish` | L-Finish 的控制投影：Loading 且 coherent，改为 Active |
| `leave_if_changed` | 严格 L-Divert / L-Leave：target 失配时从 Loading / Active 退出 |
| `leave` | 显式 Restart 扩展；若旧 target 失配，同时满足论文 Divert / Leave |
| `begin_cleanup` | 检查所有 installed dependent 的守卫，抽象控制状态不变 |
| `finish_cleanup` | L-Unload 的控制投影：清除本 episode 的 committed，回到 Inactive |
| 两种 `compact_*` | 不改变抽象状态的步骤（stuttering） |
| 被拒绝的状态修改 | 原具体状态不变，因此抽象状态也不变 |

论文的 iterator、服务表 `σ` 和效果上下文 `Γ` 被这个投影擦除。特别是 L-Unload 在控制层只有最终提交改变状态；其间 inverse 对资源的实际影响不能因控制层 stutter 就视为无效果。effect 层必须另外给出对应关系。

这些转换以单次 Kernel API 调用为边界。Definition 52 允许一次 effect stage 内创建 child，并由 inverse 退休 child；这会改变 registry，不能仅按擦除效果值处理。新 `ownership` 与 `semantics` 模块将真实 Insert/Retire 连接到 child stage 和 accumulator（见下文）。`frame` 仍只描述单次 kernel 控制调用；含动态 child 的完整 effect stage 需要保留其它条目的相应变化。

`refines_paper` 还证明投影良构，包括有限 registry、parent 有效、provision 不相交、installed committed 是完整函数及 provider 存活。模型要求存在严格下降的 parent rank；具体实现以分配序号提供这个存在性 witness，抽象规则不比较名称大小。`alpha` 已证明任意双射下的控制及完整规则 equivariance，并通过交换目标端两个 fresh 名字扩展部分匹配；扩展保持所有已有名称及其 parent/committed 引用。完整 child 历史规范化还需将这些局部匹配沿 creator episode 组合。`finite_execution_refines` 用逐步模拟 witness 归纳得到有限抽象执行；它是组合定理，不自动生成普通 Rust scheduler 的 witness。

该控制模型采用 total-provision 特化：Active fiber 的每个声明端口都存在。host 检查 payload 后才发布，但这个普通 Rust 检查与 `σ` 的对应还没有机械化。realm 被编码成 `(key, realm)`，而 fresh identity 的整数大小只用于实现，不成为论文可观察的身份关系。

## 带服务值和效果映射的规则规范

[semantics.rs](../crates/cordis-kernel/src/semantics.rs) 的 `State<V>` 在控制 registry 外保存每个 fiber 的实际服务表、effect、iterator 和 inverse accumulator。发布及 target 读取表的实际 domain，允许只发布声明的一部分；`total_targets_agree` 在显式 total-active 前提下证明它与 Kernel 的 target 相同。

`Model::iterate` 返回实际改变后的 context、inverse identity 和 continuation。九条 `step` 规则包括 L-Divert 的两种分支；landing 分支先保存该次 yield 的 inverse。`restore` 实际按 LIFO 调用 `Model::undo`，`accumulated_restore` 将它连接到已有有限恢复代数。`ordinary_step_erases` 在普通 effect 保持控制字段的条件下证明控制投影。

`child_lands` 保留 stage 创建的 child，并同时写入父 lifecycle 的 phase/continuation/accumulator。`witnessed_child_lands` 另外要求实际 yielded inverse 满足 child-retire 契约，证明即时恢复的服务表观察；`lift_kernel_child_effect` 和 `lift_kernel_child_inverse` 将真实 Kernel 契约提升到这些辅助字段。

`preservation` 已从局部 table/child admissibility 推导全部九规则的良构保持，再归纳得到从空状态出发的有限执行安全性；允许 partial provision，不以 successor well-formedness 充当前提。`quotient` 从 primitive iterate/undo 的观察相容性构造全部九规则的匹配后继，并重放任意有限 trace。该模型中控制字段、effect/iterator/inverse token 精确相同，table values 逐键相关；它尚不是允许任意不同 continuation token 的全部观察商。

这里提供的是可验证的规则规范与组合引理。`Model` 是显式数学参数；任意传入函数并不会自动满足 confinement、inverse 正确性、稳定 continuation 或良构保持。即使某个 raw `step` 存在，也不能据此声称其任意 callback 已是论文合法组件。

## 实际执行的 iterator 协议

[episode.rs](../crates/cordis-kernel/src/episode.rs) 的 `StageProtocol` 直接用于 [runtime.rs](../crates/cordis/src/runtime.rs) 的 effect group，包含冻结的 committed bindings、in-flight / settled / cancelled 状态和真实 cleanup token 栈。

- `admit` 对新 stage 检查 target 与 committed 完全一致。已经在途的 stage 保留落地资格；丢失 target 会锁存 cancellation，不会在 target 恢复时继续运行后续 stage。
- `land` 先把该 stage 返回的 inverse token 追加到 accumulator，再结束 in-flight。未获 admission 的落地被拒绝且状态不变。
- `cancel` 保留在途 stage 和已收集 inverses；在迭代边界则丢弃 continuation。
- `pop` 只有 iterator 已 settled 时才取出最新 inverse，精确保持剩余前缀。
- `can_finish` 检查该组已 settled、无在途 stage、target 仍一致。局部 effect group 的 cancel 可以作为该组已结束；整个 fiber 是否能 Active 还由 kernel 和其它组决定。

`AccumulatorView` 还提供延迟 diversion 投影：pending cancellation 在抽象 iterator 仍为 Loading；`land` 保存 inverse 的同一步才线性化为 Divert。宿主可以提前把 kernel phase 标记为 Unloading，这与论文原子 L-Divert 的组合不能直接使用裸 kernel phase。当前已证明局部 accumulator 转换，整个 host/kernel/effect 联合关系仍待连接。

这补上了原先只有一个 LIFO 容器、阶段标志完全在 host 中维护的缺口。根 setup callback 的结束、callback token 到 closure 的对应、future 的 poll、跨组等待及 kernel guard 的调用仍在普通 Rust 层。`register` 允许 callback scope 额外登记 cleanup，是宿主扩展，不将它假称为论文的一次 iterator yield。

## 有 witness 的资源历史与恢复

[history.rs](../crates/cordis-kernel/src/history.rs) 的 `Journal` 拥有自己的 `Store` 和不可复制的 inverse。ghost 快照序列记录每次成功 write 后的状态，并证明当前 store 恰好等于历史末尾、每个 inverse 对应相邻快照。生产代码不保存 ghost 快照。

`rollback_one` 的 invariant 保证顶层 inverse 一定匹配当前 store，undo 必定成功，结果恰好是上一个快照。部分 rollback 保留指定前缀；完整 rollback 恢复初始值、owner 和 depth。失败 write 保持状态和历史不变。这个 API 同时封闭了 raw `Store::undo` 由调用者确保“把 inverse 交回原 store”的义务：journal 不暴露内部 store 或 inverse。

该模块还把任意有限交错 trace 按 effect group 投影成保留内部顺序的 lanes，并机械化证明：

| 结果 | 使用的前提 |
| --- | --- |
| `partition` | 跨组每一对实际操作交换，即可将一组移到前面，保留两侧内部顺序 |
| `normalize` | 有限 group 集合与上述独立性，得到按 group ID 降序排列的 canonical value |
| `interleaving_confluence` | 两条 trace 的每组内部历史相同且各自独立，最终状态相等 |
| `erase_closed_group` | 该组在入口状态恢复为恒等，且跨组操作交换，可以删除整个闭合组而保留 foreign trace |

这里的“操作”包括 inverse，不能只检查 forward/forward 交换。`recover_group` 从逐步 inverse witness 与 LIFO 历史导出闭合组擦除。`run_refinement` 将 concrete 操作逐步映射到 abstract 操作，`observational_confluence` 因此允许两个 concrete 终态的隐藏状态不同，只要求观察相等。基础正规化使用固定的实际纯函数历史和状态相等；[calculus.rs](../crates/cordis-kernel/src/calculus.rs) 另证明显式等价关系下的恢复。动态 `iterator_diamond` 另将 Definition 42 的上下文交换、yielded inverse 与 continuation 稳定性同时写入条件，证明交换两个 stage 后上下文、两个 yield 记录和 accumulator 均相同；`yield_stability_sequence` 将这种稳定性推广到有限 foreign 组合。`dynamic_pair_recovery` 使用真实 state-dependent yield 的 inverse witness 证明该局部交错恢复。

`canonical` 进一步处理真正动态的 iterator family：每一步读取当前 context，返回实际 inverse 和 continuation；由 primitive independence 导出交换，再构造合法后缀，证明任意完整调度结果相同，不再要求调用者给出相同 lanes。下降 rank 可构造完整串行执行。`erase_execution` 删除一个 owner 的阶段，同时证明剩余调度仍合法、保留其它实际 continuation/inverse，并精确对应真实 accumulator 恢复。

这些结果仍限定于固定 owner family 的跨 owner 独立性。provider-consumer 的 entangled lifecycle 和动态 registry 不能仅凭这一定理替代 Theorem 80。

## 具体资源路径的组合证明

[witnessed.rs](../crates/cordis-kernel/src/witnessed.rs) 的 `ResourceEpisode` 将 `StageProtocol` 与 `Journal` 封装为同一个可执行对象。其 invariant 不仅要求二者长度相同，还要求每个 token 精确等于对应 journal entry 的位置。调用者不能替换内部 store、inverse 或 token，也不能调用 scope 的额外 `register`。

`land_write` 在获 admission 的 stage 中执行真实 write，成功后才同步登记该 witness 的 token；失败保持资源、快照历史和 pending 状态不变，允许重试或结束。`rollback_one` 先按协议弹出 token，再调用对应的真实 inverse，证明恰好恢复前一快照。`rollback` 在 settled 前拒绝执行，全部恢复后证明 value、owner、depth 等于初态。这条具体路径把 token 协议和资源恢复联系起来，超出了仅验证两个独立模块。它不包含 kernel provider guard，允许已结束的 episode 显式 rollback；不是完整 L-Unload 的模拟器，也不能替代任意 closure 宿主的组合证明。

[driver.rs](../crates/cordis-kernel/src/driver.rs) 的 `Driver` 进一步私有持有 Kernel 与每个 fiber 的 ResourceEpisode：installed episode 的 committed 集合精确等于 Kernel 中的 provider identities；Inactive 或已删除 fiber 没有 pending stage 和未恢复 history，Active episode 已 settled。

- `insert_with_resources` 配置初始 cells；`begin(id)` 读取真实 committed，并使用 `ResourceEpisode::restart` 保持资源值，仅重建阶段协议。
- `admit` 读取真实 Kernel target；`land_write` 必须发生在 Loading。`depart` 拒绝在途 stage，使原始 phase 的 diversion 延迟到落地之后。
- `unload` 先调用真实 `begin_cleanup` 守卫，再完整 rollback，最后 `finish_cleanup`。后置条件同时保证严格控制 L-Unload 和精确资源恢复，调用者不能提前直接完成清理。

这封闭了独立 ResourceEpisode 缺失的 provider-guard 组合义务。Driver 的 cells 仍是受控资源，并非任意服务 payload；`land_write` 参数由调用者提供。新增 `program::ProgramEpisode` 则在构造时固定代码，支持 `Set / Copy / BranchWrite`，动态读取 entry cells 得到写入值和 continuation，证明每次成功 step 等于纯解释器 `interpret`，并维持真实执行前缀 `prefix`。

`ProgramDriver` 私有拥有 Kernel、program 与 Port layout；constructor 检查长度和 Port 唯一性，finish 检查全部 cells 已写入，自动维持 Active total provision。admit 读取真实 target，unload 经过真实 relied guard 并恢复 actual inverse。它不允许调用者在 admission 后改变写入内容。此有限语言还没有跨 provider payload 操作和 child 创建指令，也没有替代普通 Rust Runtime 的跨组异步 scheduler。

`program_refinement` 从真实 Driver 快照生成 `State<Cell>`：只有 depth>0 的实际写入 cells 进入服务表，Port 来自经过检查的 layout。`model` 固定同一份 code、owner、layout 和 initial；读取/分支使用当前表解码后的真实 cells，undo 使用实际 stage index 对应的代码 prefix。每次执行方法的后置条件给出具体字段关系，而桥接引理从这些关系推导完整规则，未把完整 step 作为调用方前提。

`ProgramDriver::land` 原子执行已获准阶段并确认 target drift，成功返回直接对应 L-Iter、landing L-Divert 或 terminal 行政步骤；finish 收集 terminal identity yield，unload 接到模型的 LIFO restore。`program_trace::driver_trace_refinement` 从真实分配水位推导不复用名称和静态配置保持，构造覆盖历史插入／移除的单一 `history_catalog`，并将成功 API 序列转换为完整规则 trace、保留端点投影。它不接受完整 step 或固定 catalog 作为前提。底层 `step` 调用序列、失败调用及任意 callback 不在此定理范围，详见 [固定程序](verified-programs.md)。

`land_write` 与后续 `depart` 是两个可执行调用；pending 期间延迟 phase 转换有行为测试和局部契约，但完整状态下将两者线性化成单个 landing Divert 的联合模拟仍待证明。不能用裸 `control()` 把失配后的资源落地标成合法 L-Iter。

[ownership.rs](../crates/cordis-kernel/src/ownership.rs) 的 `ChildEpisode` 则保存 stage 实际创建的 fresh child ID，将 token 序列与这些 ID 精确绑定，rollback 真正执行 LIFO `Kernel::retire(child)`。`child_iteration`、`child_unload` 描述 child effect 与 accumulator、guard、外层控制转换的组合；`finish_restore` 不等待 child 进入 Inactive 或被 remove。raw Kernel 允许在 retired 但仍注册的 parent 下落地 child，符合在途阶段的规则。

ChildEpisode 的完整恢复需要 `retirable`：所有待退休的 child 仍注册。运行时会实际检查这个条件；若外部已删除 child，`rollback_one` 返回 Unknown，完整 `rollback` 返回 false 且不消费任何 inverse，`finish_restore` 在进入 cleanup 前返回 Unknown。这个定义域限制暴露了 Definition 52 所称 inverse totality 的缺口，不能省略；详见 [论文审计](paper-audit.md)。

`ChildEpisode::attach` 从 Kernel 读取实际 committed 和 episode generation；`admit_current` 与 `land_child` 同时检查 phase、committed 与 generation。每次成功 `Kernel::begin` 严格增加 generation，失败或 compaction 保持它，达到 `u64::MAX` 后拒绝新的 begin。因此即使重新激活后的 providers 完全相同，旧 handle 也不能给新 episode 落地 child 或执行 `finish_restore`。检查在插入和 cleanup 前完成；在途 stage 仍可跨 target 丢失落地。

低层 `new/admit` 接受调用者提供的快照；`new` 到第一次成功的 current 检查才捕获 generation，后续不能重新绑定。若首次 `land_child` 的 current 检查成功而插入失败，handle 保留已捕获的 generation，Kernel、协议和 child journal 不变。独立 `rollback/rollback_one` 仍可退休旧 journal 中的 child，不完成父节点的新 episode。所有这些身份只在同一个 Kernel 实例内有效；此改动没有证明任意宿主的全局句柄隔离。

`child_driver::ChildDriver` 私有拥有 Kernel 和全部 ChildEpisode，不向调用者暴露可绕过检查的 mutable handle。`remove` 扫描真实 journals；任一待执行 inverse 仍引用 child 时返回 `Retained`，即使 child 已 retired、Inactive。`retention_snapshot` 只投影控制和实际 child tokens，`refines_retention` 将真实状态接到 `child_history::retained`，成功 remove 推出 `remove_unreferenced`；这不是完整服务表模拟。`land_child` 把真实创建、inverse 登记和 target 漂移后的 L-Divert 原子组合。父 unload 执行真正的 guarded LIFO child retirement，无需等待 child 删除；实际服务依赖仍控制恢复次序。该可执行保留策略是 Definition 52 的显式修正，未改写裸 Kernel 的 O-Remove。

## 完整规则的历史 frame 与 ordering

`rule_frames` 将九规则分解为冻结的 state map 与 bracket edit，证明实际 successor 等于两者的组合。`Source` 保留实际 iterator 或 accumulator 来源，只有 L-Unload 选择完整 accumulator 恢复。冻结映射可在其它输入上求值，但这不证明反事实状态上同一 rule 仍合法。不可变 metadata 与 retirement 单调性从实际 primitive 推导；若 retirement 在 Unload 内发生，`retires` 追踪真实 LIFO inverse 调用路径上具有 child-retire 形状的转移，不单独证明 captured child handle 身份。`entry_origin` 与 `foreign_change_key` 补齐新 entry 的来源和依赖交集中的实际变化 key，连同 episode frame 覆盖 Lemma 59 的五项结论。

`lifecycle_ordering` 以实际 installed 状态定义包含开放尾部的最大 episode，证明仅 Begin 开启、仅 Unload 关闭，committed 固定。Begin 的每个 dependency 都有实际发布的 key；已绑定 provider 的整个表域在 consumer episode 内保持，并在 consumer 卸载前不能恢复。包含该 Begin 的 provider episode 必须更早开启；若关闭，必晚于 consumer。Loading 是 episode 的唯一初始区间，所有 Iter／Finish 使用 opening committed，退出只可能为 Finish 或 Divert；有限前缀不蕴含最终一定 Unload。

`grammar_ordering` 进一步从实际 Operation／Receipt 推导 provider 值变化的精确 key 与 provider 来源。一次 Unload 的净变化可追到实际递归恢复路径中的某次 inverse 调用。`history_entry_origin` 和 `invocation_prior_landing` 在空初始 history 下回溯到严格更早的真实 forward landing，避免把预装历史当成执行证据。`indexed_ordering` 允许每个实际步骤提供自己的语义 Model，因此任意 `I` 无需编码成 nat。`mixed_ordering::empty_episode_ordering` 将 Theorem 70 各条款接到同一条 dependent／child trace：包括真实 LIFO 调用的前后状态、原始 `I` 节点和严格更早的 operation landing。恢复经过的 child retirement 状态完整保留。该结构性关系不宣称不同步骤共享一个全域解释器。

## 支持集与终止上界

[progress.rs](../crates/cordis-kernel/src/progress.rs) 实现 `support`，其输入是显式拓扑排序后的 provider/parent 图和 enabled 标记。它检查每条前驱边指向更小的拓扑位置；缺少 provider 或已退休的 fiber 不应 enabled。输出精确满足 Definition 74 的递归支持方程，`support_unique` 按拓扑前缀归纳证明这个方程只有一个解。小图测试还枚举全部 DAG、enabled 集合和候选解进行独立核对。

拓扑位置不是 fiber ID。尤其是 provider 可以在 consumer 后插入，不能用分配序号冒充 precedence order。[global.rs](../crates/cordis-kernel/src/global.rs) 已直接在实际控制规范上定义 provider 和 parent 关系。`quiet_active_support` 在显式 `retirement_closed` 条件下推导 Definition 74 支持方程。`child_history` 从实际完整 trace、子创建 inverse token 与逐 episode 记录导出 lifecycle-born child 的退休闭包；所有非根子节点均有此出生来源时，得到原 support 方程。一般外部非根插入下，原 Lemma 77 存在五步静止反例。`execution_quiet_origin_support` 保留一般 O-Insert，只对 lifecycle-born child 加 creator 约束，证明修订的 support 方程。

论文 Lemma 75 的合并图无环推导已被机械化反例否定。替代的 `quiet_active_unique_by_precedence` 只沿 provider precedence 证明静止 Active 集合唯一；`quiet_control_unique` 进一步证明同静态输入下整个控制 registry 相等，包括 committed identity。它不要求合并图有 rank，也不要求 retirement closure，但仍需要静止、良构、同注册名字及 parent/dependency/provision/retirement 输入和 provider rank。

`control_no_deadlock` 从任意非静止、良构且 provider precedence 有 rank 的控制状态构造可执行的 lifecycle rule。`semantics::full_no_deadlock` 在 shaped、total-active 的完整状态中提升这一结果：Loading 使用实际 iterator yield，Divert 使用 landing 分支，Unload 使用实际 inverse accumulator。该结论保证参数化规则存在下一步，不保证任意 Model 的输出保持良构，也不保证真实异步 future 最终落地。`target_change_strictly_precedes` 从普通控制步骤证明目标变化只能来自严格 provider 前驱；registry-changing child effects 需要额外的组合分析。

基础 `finite_step_bound` 机械化 Theorem 73 的计数归纳：给定每个 fiber 的步数 `S`、target 变化数 `V` 和 iterator 上界 `K`，要求 `S(i) ≤ (K+3)(V(i)+1)`、`V(i) ≤ 1 + Σ S(j)`（`j < i`）。由此证明总步数不超过有限的递归 budget。这使用全部较早 fiber 作为前驱的保守上界，算术使用无溢出的自然数。它证明计数论证，不假定普通 Rust future 会结束，也不把无限次 restart 纳入此终止结论。

`termination` 已把上述两个计数不等式连接到实际固定 registry 轨迹：每个 target 恒定区间的 potential 随 lifecycle 步下降；target 变化来自真实 provider 步或 retirement 的唯一上升。`finite_lifecycle_bound` 允许 Retire 交错，`finite_execution_bound` 给出纯 lifecycle trace 长度界，均由真实步骤导出计数前提。

`ordinary_model` 要求 forward/restore 的局部 table footprint、真实 terminal yield 发布全部 provision，以及 continuation rank 严格下降。由这些 primitive 条件、初始 full configuration 和 provider 拓扑证书，`normal_form_exists` 构造一个满足完整 `landing_step` 规则的有限执行到 quiet。它调用完整规则 preservation 和 no-deadlock，实际 yield 决定 Iter/Finish；没有假设某条完整执行已存在，也没有任意提前 Finish。范围为固定 registry 的 ordinary table effects；动态 child、无限 orchestration、任意 future 不属于该结论。

## 前置代数与 coeffect 语义

`foundations` 给出 tracking/twisted composition、effect monoid、提升同态、真实 state-dependent inverse witness 与恢复。`observation` 将所有有限 operation/inverse 测试的 definedness 和 outcome 定义为观察，证明其等价性、operation respect 和最粗性；另证明观察关系下的 witness composition、tracking 与 sequence recovery。

`iterator_independence` 完整表达 Definition 42 的两条双向条件：least reachable iterator 的所有 forward／actual inverse 生成 monoid 交换，且每个 yield 的 inverse maps 与最大 bisimulation continuation 保持。`generator_criterion` 证明 generator 条件与完整 monoid 条件等价。无限 parity iterator 实例允许原始 continuation 标识不同但行为等价。

`quotient` 的 iterator relation 是包含任意长度 continuation 的最大 bisimulation。通过逆关系和关系组合证明 Lemma 35 的对称、传递与 self-respect，不以有限 rank 代替 coinduction。`monoid` 定义最小 continuation-closed reach 集和任意有限 generator words；Lemma 41 同时涵盖 generator commutation、完整 monoid inclusion 和 yield stability 的闭包。

`iterators` 区分任意索引 family 的最小递归成员与 coinductive respect/witness。`inductive_termination` 从 µ 成员推导每个输入运行终止，不需要共同有限高度；`whole_effectiter` 通过完成运行定义，证明 fuel 选择无关并满足 Definition 18 的递归等式。一般允许无限 continuation 的 family 仍有可恢复的有限前缀，但不会被冒充终止迭代器。严格 partial family 的编码保留 None 的定义域区别，并将实际 grammar 接入递归 witness；typed codec 进一步输送单个 value-family 成员的观察合同。

`projection` 精确实现 Definition 51：对所有注册 fiber 的 tables 按键取并集，包含 Inactive/Loading，而非只取 Active publication。唯一 owner、空条目插入/删除及 phase edit 不影响对应观察；operation/provision 的实际 full State 写入投影等于 `mediated::run` 后继，返回 inverse 恢复原 State。

`coeffects` 从真正 key-local operation 的值、inverse 和 outcome 出发，证明不同 key 的所有 generator pairings 独立；同 key 情形消耗值层的 coeffect witness。`family_independence` 再把这些局部条件接到动态 family，`coeffect_schedule_independence` 接到实际调度唯一性。更一般的 partial grammar 与观察关系见 `mediated`，其中 precondition 失败是没有 transition，不悄悄读默认值。

`contexts` 将 Definition 19 的有限 dependent map 编码为 key-indexed value predicate 与双向 codec，证明 typed get/set、实际逆闭包以及异构 bool/int 实例。隔离保留共享表、只改变 realm resolution；拦截使用每个 key 的 metadata monoid，证明声明在左、上下文在右的合并顺序。`typed_mediated_operation` 和 `typed_mediated_provision` 将这些表示连接到实际 grammar yield。`recursive_context` 证明原 Definition 28 若按集合及其所有 endomorphism 理解，带 constructor/projection 的非平凡模型不存在：将 accumulator 在自身编码上求值产生对角矛盾；两个不同 coeffect 已足以推出矛盾。单例满足投影方程，但不是 μ 的最小不动点证明。有限层、受限函数或 domain-theoretic 解释必须另行说明，不能原样宣称解决递归方程。

`partial_independence` 保留失败、缺席绑定及 inverse 定义域的区别。不同 key 的四类 generator 交换、同 key 的观察相容 witness、least grammar 的实际 reachable continuations，共同导出任意生成 partial-map word 的交换和 inverse／raw outcome／continuation 稳定。`actual_exchange` 还证明真实两步执行的 enabledness 与观察等价结果。`mediated` 的 provision inverse 已修正为仅在 key 存在时定义，`provision_inverse_domain` 明确检验此条件。`iterator_bridge::grammar_independence` 已把既有 nat-indexed 最小 mediated grammar 接到适用于任意索引 partial family 的独立性定义，包含完整变换 monoid 和最大 continuation bisimulation；yield 稳定性只在 foreign 应用成功时要求。reach 与 strict Option 编码一致，clause (1) 的观察交换也能输送；但一个由不同 key 的两段合法 provision grammar 组成的实例证明，失败 sink 会把 continuation 改为 None，不能据此自动得到全域 Definition 42。这个边界不等于否定所有其它域解释。这些结论尚未与所有 FullState child 和 entangled 生命周期组合。

`observational_algebra` 补齐 Lemma 38 的 §3.1 代数传递：monoid、tracking、effect lifting、每个反向前缀和整个递归 iterator 的恢复都在观察等价下成立。`full_accumulator_recovery_iff` 保留关键量词：对所有 accumulator 恢复，要求本次返回的 inverse 在所有 forward 输入上成立；仅在本次输入成立的 witness 不足以替代它。`tracking_trace_soundness` 只要求当次输入恢复，就可推导实际轨迹的 accumulator respect 与恢复不变量。

`dependent_grammar` 把有限 context 的值类型、每种 operation 的参数和 outcome 类型分别编码为 dependent family，并用双射 codec 对接不同 Rust 类型。continuation index 可以是任意类型；least membership 只检查该 operation 的合法 outcome 所命名的 continuation。由 primitive contract 推导严格 partial inverse、观察相容性、实际输入恢复和完整 `paper_partial_witnessed`，没有统一有限高度前提。

`grammar_lift` 在完整 registry State 上解释 Unit、Operation、Provision：依赖操作沿已提交的 provider identity 解析，实际返回的 Receipt 捕获 provider 与 inverse。语法解释直接推导 confinement 和 projection，不要求调用者另给 `forward_map`。九规则 execution 从空配置出发保持资源安全、grammar membership、实际 receipt 历史和 accumulator token 所有权。失败的操作或 inverse 保持未定义；L-Unload 只有在实际 LIFO restore 成功时才有 transition。重复的相同 actor／iterator／完整输入调用复用最早记录的 token，每次实际 landing 仍追加历史记录。`catalog_execution_refines` 从最终历史构造一个固定 total `Model`，自行推导所有成功 iterate／restore 调用的一致性，不再要求调用者提供 `calls_agree`。数学 Model 在未记录输入及失败域上的补全不改变 partial interpreter 的 transition；尚未证明任意干扰后 restore 必成功，也未纳入 child 节点和一般异步宿主。

`dependent_lift` 把 key-indexed value、operation-indexed argument/outcome 和任意 continuation 类型 `I` 接到完整 registry。`Configuration.current` 保留真实 `I`，旧 State 中的 `Some(0)` 只表示 Loading 的 iterator 存在，不是 `I` 的数值编码。九规则从空执行归纳得到所有前缀的结构与绑定安全、值类型、有限 context、grammar membership 和真实 receipt provenance；`run_projects`、`run_definedness`、`inverse_projects` 对应有限 dependent context 的实际状态、原始 continuation 和严格定义域。`trace_current_witness` 再把当前 iterator 接到 Lemma 39。`mixed_syntax` 在相同 least membership 中加入 Child，包括 child root 和 parent continuation；`mixed_grammar` 在相同完整状态、真实 `I` 和 journal 上解释九规则。实际创建检查 fresh 注册身份和 Insert 守卫，actual inverse 只退休 captured child；retention 从空执行归纳导出，并使真正到达的 child inverse 有定义。表 inverse 失败仍中止恢复。`from_empty_safe` 的前提没有最终良构或最终恢复结论，`mixed_examples` 给出 parent 恢复时 child 仍 Active 的无前提实际交错见证。任意未来创建仍受给定 usize 身份和 fresh guard 约束，不额外声称全局分配器定理。

Receipt 本身只检查 captured provider；episode 所有权由合法 trace 的 accumulator 管理，不能用于判断任意外部传入的旧 Receipt 属于哪个 episode。

## 从实际轨迹到恢复与删减

`entangled::full_episode_recovery` 从完整规则轨迹计算每一步的值操作和实际返回 inverse，证明该 journal 等于真正的 accumulator。自己的局部 inverse 恢复、foreign operation 的逐键交换，以及 provider journal 中已经存在的 restriction，导出任意有限交错的恢复；`full_terminal_recovery` 再连接实际 L-Unload。consumer operation 与 provider operation 不必逐对交换：实际 provision 的 restriction 可以吸收该 key 上的干扰。`pinned_provider_lifetime` 从 committed binding 与九规则守卫推导 provider 在整个 installed consumer episode 中保持 Active 或 Unloading，不能提前恢复。

`grammar_recovery` 与 `mixed_recovery` 直接读取任意 `I` 的真实九规则执行，从 empty-origin trace 的真实 Begin 推导 episode 的初始空 journal、provider pin、有限类型和 provision/restriction 历史，再推导每次 forward／actual inverse 的投影与 foreign compatibility。`actual_terminal_recovery` 将结论接到实际成功 Unload：owner 表为空，全部表值等于删去 owner 效果后的 foreign 值重放。child 创建和 retirement 在值层对应 Identity，但真实控制迁移和 journal 中的 child token 仍完整保留。调用者不再需要提供 `episode_profile` 或完整恢复方程。 `recovery_examples` 证明所有整数平移及其真实减法 inverse 满足非空 scalar 接口，并构造 12 状态的 mixed trace：parent 的 7 经 +5 变为 12，child 的 42 经 −3 变为 39；实际 parent Unload 清空自己的表，child 仍 Active、保留 39 并被退休。该 witness 实例化通用 terminal 定理，是数学解释器中的真实规则执行，不是异步 Runtime 的模拟证明。

这里的值解释采用明确的 key-local、精确相等 profile；缺席 key 的 operation 按论文 Lemma 67 的约定不产生作用。部分值操作失败时选择 identity 作为全域扩展，但只在原始严格操作有定义时证明对应，未把失败变成合法 transition。新的语法恢复证明显式要求同 key 的所有 scalar forward／实际返回 inverse 在 identity extension 下精确交换；这比一般观察等价或严格 partial-map 交换更强，不能省略。`partial_domains` 从实际 inverse witness、foreign respect 和 inverse commutation 推导真实两步的定义域，并在相应逐输入 witness 条件下推导 forward 的 identity-extension 交换；它没有给每个 returned inverse 凭空添加自己的逆，尚未消除完整 scalar interface。child 控制字段也不能只靠值投影恢复。 `foreign_state` 是选定 key-map 含义的值重放，不是已经构造出的合法反事实 lifecycle trace；实际输入处的 projection 合同也不自动覆盖每个反事实上下文。

`deletion::full_step_bisimulation` 从局部 iterate/undo 擦除合同证明九规则双向对应。`suffix_deletion` 构造删减后的状态与标签序列，推导 vestigial 保持或永久缺席，删除作用于该名称的实际 Retire/Remove，并证明最终服务表观察不变。`unload_born_leaf_vestigial` 通过出生历史和 retained inverse 推导 Unload 后的删除边界，而不是要求调用者预先给出 vestigial 结论。编码规则中的 Lemma 79 删除反例表明：必须处理外部输入对 child 名称的 parent 引用。合法 suffix 不自动证明闭合 episode 内保留步骤也有合法执行。

`mixed_transposition::observed_pair` 已补一个直接作用于真实语法执行的局部交换：Child landing 后的外部 O-Insert，只要新 parent 不读取刚出生的 child 名称，就能构造逆序的两条合法规则。freshness、provision 冲突、root membership 和 target 均由原步骤及局部守卫推出，最终完整 State／roots／current 相等，实际 receipts 对应。新 history entry 保存各自真实输入，因此两份 history 可以不同；`mixed_transport` 进一步证明这些对应的 receipts 解释同一严格 inverse；构造右方后继并逐步输送任意已合法的有限 suffix，规则标签完全相同，每一步完整 state／roots／current 相等，旧 history 的不同 input 得到保留，新 entry 来自右方真实当前输入。右方后续合法性与良构由证明导出，不作为前提。正例包含非空 provision，负例检查 parent 读取和 provision 冲突，仍不能替代一般 canonical form。

固定程序路径另有 `program_normal_form::driver_quiet_confluence`：相同初始输入和提取的编排序列、两个 quiet 终态及 provider rank，推出完整投影相等。代码、初始值和真实执行深度决定服务表及 accumulator，不需假设这两者相同；证明范围详见 [固定程序执行](verified-programs.md)。

## 观察等价下的同一执行器

`observational_grammar` 将 primitive witness 分解为 observation respect 与实际输入处的观察恢复。它保留原始 outcome 相等、partial inverse 的成功域以及 dependent typing；允许撤销修改不可观察的内部状态。旧精确合同蕴含这个合同。相同 `dependent_grammar::run` 的 least membership 仍导出递归 witness、实际 continuation 与最大 bisimulation，未选择等价类代表。

`observational_lift` 沿用 `mixed_grammar` 的 State、Configuration、run、step、receipt 和严格 LIFO restore，没有另写一套弱化的执行规则。它从这个 primitive 合同推导九规则成功前缀安全、有限类型、真实历史与 child retention；`mixed_ordering::observational_empty_episode_ordering` 保留 provider 生命周期和实际 operation/inverse 来源。原始精确入口仍作为特化保留。

`observational_recovery` 在同一个 `entangled::Action/Event` 解释上证明观察 respect、journal 交换、restriction 吸收和整段恢复。`observational_execution` 将这些结论接到同一实际 mixed trace：从空起点、真实 Begin 和成功 Unload 导出全部表的观察恢复及 owner 空表。这里已经消除了精确值恢复与精确 scalar 交换前提；同 key 的 identity-extension 观察交换仍是明确的 coeffect 接口，不能与任意 strict-partial 交换混同。`partial_forward_commutation` 利用真实 inverse witness 输送成功域，仅导出 forward 扩展交换，没有为任意 returned inverse 发明另一个 inverse。值重放仍不是合法反事实 lifecycle 执行，成功 Unload 也不等于所有表 inverse 总有定义。

`observational_examples` 给出不能代入旧精确理论的实际实例。父组件提供 `(visible=7, hidden=10)`，两个 child consumer 提交同一个 provider/key，依次执行 `+5 / hidden:=1` 与 `+3 / hidden:=2`；第一个 consumer 的真实 Unload 执行 `−5 / hidden:=0`，留下 `(10,0)`。删去它的贡献后的 foreign 值重放为 `(10,2)`。实际值不同而观察相等，且库不满足旧的精确 primitive theory 和 scalar commutation；证明直接实例化新的整段定理。

`mixed_orchestration` 将局部编排交换扩到所有 mixed 节点和 Insert、Retire、Remove 三条外部规则，在同一个观察 primitive 理论下构造中间状态和逆序实际执行。Insert 的 parent 必须在跨越前已存在；Retire 目标必须已存在且不是当前 acting fiber。对于 Remove，原始合法两步和良构性已经足以推导 Inactive、空表、非 provider、无 child 和无 journal 引用等逆序守卫，不增加反序合法性前提。最终完整状态和活 continuation 相同，receipt 对应，但历史输入保存各自实际值。随后任意原先合法的有限 suffix 都有同标签对应执行。这些局部构造尚不是全局 canonical form。

`causal_normalization` 已把这些交换组合成有限轨迹的构造。`adjacent_swap` 构造两条反序规则并输送整个合法 suffix；递归 `normalize` 以 lifecycle-before-external 倒置数严格递减，返回没有可用相邻 lifecycle／编排交换的轨迹。原始起点、相关终态、lifecycle 标签顺序，以及每个外部 Insert 的 actor／parent／dependencies／provisions／原始 root `I` 都被保留，Retire 和 Remove 的 actor 顺序也被保留。一个实际 Operation／Retire 见证恰交换一次；出生后才存在的 parent 会阻止 Insert 前移，并留下一个倒置。这是指定局部重写关系的终止与存在性，已涵盖全部 lifecycle 规则；同一轨迹的重写唯一性由下文 `rewrite_confluence` 补齐，一般调度 confluence 仍未推出。

`observational_permutation` 补齐 Theorem 43 的观察等价版本：由 Definition 36 的
witness 和 Definition 42 的独立性，推出实际返回的 inverses 按任意排列执行都恢复
原观察。证明把 respecting maps 提升到等价类，复用排列定理，再返回实际状态的观察
关系；不要求隐藏值相等，也不要求某次 inverse 是所有输入上的统一逆。非字面实例
验证两个逆序留下不同 hidden 值而仍恢复 visible 值。

`functional_quotient` 进一步解释 registry 中的函数字段。effect／current IDs 由最大
bisimulation 比较，accumulator 由完整 restore 函数比较，允许 token 和栈长度不同。
在总 Model 与显式 table-only primitive frame 下，它构造九规则后继及完整有限轨迹；
真实 from-empty 例使用不同 roots、continuations 与 inverse tokens。这里比较全部键 K，
接口 S 到全键 K 的比较已有下文 `interface_observation` 的条件式 frame 桥；
下文 `strict_partial_quotient` 已构造合法输入 PER 下的严格九规则模拟。每个原组件
满足该 frame、内部 Child／退休同步、原文纯 table 函数关系与递归 Γ 的对应
仍未完成，不能将这些充分子类写成完整 Lemma 60。

`paper_invariants` 将原 Definition 63 的四条与实现的加强不变量分开，证明后者蕴含
前者，并给出满足原四条但带 self-provider commitment 的非可达反向例。Definition 76
则量化任意满足 dependencies 的输入和任意完成 iterator run；当前 `total_active` 只是
状态后果。另一个 operational 谓词量化真实 Begin 到 Finish 及其交错，并给出完成后
Active 表域的保持。两种组件总性之间的完整表示桥仍单列，未由当前状态检查替代。

## 整篇完成门槛

完整逐条义务现在由 [paper-obligations.json](paper-obligations.json) 记录，生成 [81 项覆盖表](paper-coverage.md)。每项都列出原文编号、状态、源码符号和准确范围。普通 `quality.sh` 要求编号无遗漏、引用存在、生成表未过期；它不会要求把反例和未完成项目改成通过。

`python3 scripts/check-paper-coverage.py --require-complete` 是独立的整篇门槛。原文存在已验证反例，同时已建立的条件 entangled recovery、child episode 结构历史、合法 suffix deletion 尚未连接到一般 admissible grammar 与完整 lifecycle canonical form，因此这个门槛应失败。不可把局部独立 family 的 confluence、固定 registry 的 termination 和控制唯一性相加，直接宣称原文 Theorem 80 或整个异步宿主已完成 refinement。


`administrative_orchestration` 补齐 Begin、Leave 和终止 Divert 对三类外部规则的实际交换，并接入相同倒置数归约。只有 Begin 跨越自身 Retire 被禁止；其余反向守卫由原始合法两步导出。完整 Configuration（包括 history）相同，所以原始 suffix 可以直接复用。Unload 的严格 journal 交换由 `unload_orchestration` 补入同一归约。

`isolated_deletion` 现在构造删去 owner 生命周期后的真实执行，并证明每个原始时间前缀都有合法对应。owner 注册条目及其外部 Retire 保留，foreign 可以创建 child、执行 Unload，甚至以保留的 owner 为外部 Insert 的 parent。目标 history 记录实际目标输入，新 journal token 使用保留项的前缀计数；没有假定目标执行存在。当前前提是初始 history 为空、owner 为 Inactive 空表、持续注册且没有 dependencies 或 Child landing，其他组件声明与其 provisions 分离。初始全部表为空且 owner 最后 Inactive 时，从实际 provision journal 导出 owner 空表和全部 control／tables 相等。共享 dependency、owner 创建 child 和非空初始 history 仍待推广。

`strict_journal` 在严格 partial maps 上推导整段撤销成功和 foreign 值重放成功。输入只包含每个真实 forward 的局部 inverse witness，以及 foreign forward／其返回 inverse 与既有 owner journal 各项交换；目标恢复等式和最终 inverse 成功不是前提。结论覆盖每个前缀，且保留失败输入。已验证反例说明仅 forward 交换仍可能令 pending inverse 失去定义。这个抽象事件结论还需完整接到 mixed lifecycle；任意 foreign Unload 不自动拥有本定理要求的局部 inverse witness，值重放也不保证原始 outcome 和 continuation 相同。


`unload_orchestration` 沿实际成功的 inverse journal 逐项推导反序恢复的定义域与结果，再构造 Unload／外部编排 diamond。Insert 和 Retire 不需额外读集前提；Remove 要求目标不是 owner，且 owner 当前 journal 没有捕获该 child。provider 排除、Inactive、空表及其他 journal 不引用目标均从原始合法两步导出。反序终点是完整 Configuration 相等。实际非空 Operation／Retire 轨迹经归约移动一次；已退休的 Inactive child 若仍有 captured inverse，其 Remove 会被正确阻止前移。


`rewrite_confluence` 补齐这个特定 guarded 重写关系的汇合与正规形唯一性。它先证明逐状态／receipt 对应保持 guard、完整外部输入与实际交换，再构造两个不相交可用交换的局部 diamond。`unique_normal` 用倒置数递减归纳证明：同一原始实际轨迹的任意两条重写路径若到达 normal，标签序列相同且每个 Configuration 都保持实际 receipt 对应。`normal_join` 为任意两个重写后继构造共同对应的 normal 后继。两个可选起始交换的非空 Operation 实例已验证；省略 receipt 对应会被负控拒绝。该结论不包含从不同生命周期调度起点推出同一终态，也不恢复已被反例推翻的编排优先顺序。


`shared_replay` 与 `shared_execution` 已把 strict partial 恢复接到共享依赖的实际删后轨迹：保留非空初始 history，重新执行 foreign 操作并生成它自己的 receipt／token，证明每个前缀合法。最后 owner 的真实 Unload 成功由局部 witness 推导，终点 control 相同、全部表观察相等。当前限固定 registry、新阶段为 Unit／Operation、片段内部无 Unload、owner 初始 Inactive 且无 provisions；允许共享 dependency。一般 foreign Unload、owner provisions 和 Child 仍待扩展。

`mixed_iteration_exchange` 构造两个 actor 的真实 Iter 交换，允许共同操作第三个 provider 的同一个 key。局部接口同时约束值、原始 outcome 和 actual inverse；反序 history 保存各自输入并交换新 token。只有值交换不足以保留 continuation，已给出对应反例。`entangled_loading` 则从空状态真实执行导出 provider pinning，补出 Lemma 67(3)：Loading 期间 entangled foreign 步的实际值操作词为空。


`MixedDriver` 现在用一条可执行路径统一真实 Kernel、跨 provider 的 `u64` XOR、Provision、Child 和混合 LIFO journal。公开 `run_script` 从新建空状态执行命令并构造同一条 `mixed_grammar` 轨迹，证明每个源前缀安全；首个失败保留完整机器及成功前缀。蓝图 DAG 和向前 continuation 由执行时检查，发布前要求声明表完整。当前 Child 使用固定 `expected` 身份：分配器不匹配时原子失败；自动 fresh-name、任意 callback 和异步在途落地仍在边界之外。
`MixedDriver::represents` 按真实 journal 次序把每个 Receipt 对应到源 history 中的实际 landing token，允许源保留已消费的历史。实际程序按 `(blueprint, pc)` 解释；蓝图库在执行中不改变，不随当前 allocator 任意改换源 program。`run_script` 每次成功调用 `advance_source` 与 `configuration_preservation` 构造后继，首个失败使用完整 `same` 状态关系保留原对应。这消除了只给单步条件 `ack` 而未构造可达初态及共同 history 的缺口。公开 API 的错误合同还覆盖 blueprint、当前 pc、完整 journal 与 Kernel generation，不仅是可见 payload。

`mixed_observational_runs` 与 `mixed_observational_transport` 把共享 provider 的 Iter 交换延伸到后续全部九规则。两份历史保留各自真实输入，交换的两个 token 使用明确双射，后来追加的 token 保持不变。Operation inverse 只要求严格观察关系，既允许原始值不同，也保留 None 域。旧 receipt 的适用性由从 empty 开始的实际前缀导出；目标 suffix 的合法性不是前提。实例执行双方真实 journal，把值从 15 恢复到 13，再到 10。这是一次合法交换及其完整后缀的对应，不是任意两种调度的汇合。

`foreign_unload` 解决 foreign inverse 的局部反向见证：保存每次真实 forward 与其实际 inverse，并沿合法调用运输见证；展开真实 LIFO Unload 时，原 forward 成为当前 inverse 调用的反向见证。因此可从真实混合执行导出 strict foreign 值重放及最终 owner Unload 成功。当前 fixed-registry Unit／Operation 片段允许非空初始 history，但 foreign Unload 只能消费片段中新建的 token；初始任意旧 journal 不自动满足当前见证。完整删后生命周期轨迹仍须另行构造，不能用值重放替代。

`fresh_grammar` 将 Child 的 child ID 改成固定程序内的 fresh binder，并从实际 receipt 重建每次 allocation choice。run、undo、restore、历史以及 fresh choice 的 alpha 运输均保留严格失败。名称扩展保护整个配置的支持集，包括已删除对象留下的历史名称及 continuation 内的名字。程序需满足明确的结构 naturality；未来外部命令若引用出生节点，其 actor、parent 和 name-bearing root 必须随同运输。动态可执行驱动与全部生命周期连接在单独模块继续实现。

`external_inputs` 连接实际混合轨迹的完整外部输入提取与 alpha 运输，Insert 的 actor、parent、原始 root 都在证明范围内。`literal_stream` 给出字面相同输入的准确条件：所有这些字段必须在所用重命名下保持不变。交换两个出生名称时，`Retire(2)` 会被运输为 `Retire(3)`；仅声明终态允许 alpha 等价并不能省去输入条件。

`fresh_semantics` 为同一 fixed fresh-binder Programs 给出完整九规则与实际 history，保留每次 landing 的 choice，证明 configuration preservation、从 empty 的所有前缀资源安全和原始索引 ordering。`allocation_inputs` 用这一解释器给出严格 guarded fresh-binder 模型中、与 Theorem 80(2) 字面同名输入读法有关的反例：同一自然程序、相同完整外部输入、有限四名称、无环依赖和单阶段组件到达无法 alpha 对齐的 quiet 终态。该见证尚未满足原文全域 recursive-context 组件 witness；guarded Child 的域桥接以及按出生对象运输外部引用后的汇合，仍是单独待证的命题。

`shared_unload_execution` 现已构造含 foreign Unload 的真实删后轨迹。保留旧 history，压缩本片段 surviving token，并在目标当前状态真正运行返回 inverse；原始值和 inverse 函数无需字面相同。`terminal_deletion` 推导 owner 最后 Unload 成功以及完整 control／所有表观察相等。仍限定固定 registry、新 Unit／Operation、owner 初始 Inactive 且无 provisions，foreign restore 只能消费初始 offset 之后的新 token；旧 live journal、Provision、Child 和动态 registry 另待推广。

`fresh_equivariance` 将 least membership、全部九规则与实际完整轨迹接到名称运输。对结构 natural 的程序，重命名后仍使用同一安装的 Programs；`natural_from_empty` 推导全部目标前缀安全。`external_inputs::natural_execution_inputs` 同时构造合法的同程序轨迹及它的完整外部输入，不把目标成功或输入对应作为前提。

`mixed_driver::fresh::FreshDriver` 复用已经证明的真实表、Kernel 和异构 journal。Child 蓝图只有组件索引，没有 expected identity；执行时读取当前 allocator，实例化一次栈上指令，安装的程序不变。`run_script` 从空状态构造 `fresh_semantics` 的完整实际历史，支持 provider replacement、外部插入和多次 activation，过去 inverse 仍捕获各自旧身份。源轨迹只描述成功前缀；首个 Rust 错误由完整机器不变契约覆盖，未额外声称源错误分类完备。当前为同步闭合指令语言，不含任意 callback 或 future 执行。


`mixed_driver::fresh::admitted` 已把单个已准入阶段的跨调用协议接到真实落地：会话拥有
机器，捕获 generation／pc／模板，目标失配后仍执行原动作并登记 inverse，再线性化为
landing Divert。`admitted::script::run_script` 从 empty 构造同一程序的完整源历史，
明确区分 Call／Land 与 Admit／Release 元数据步骤，并证明事件完整性和输入顺序。
失败或旧准入不改变机器；这补齐该闭合语言的两阶段模拟，仍不证明任意 future 或
callback 的内部效果，也不替代普通 Rust Runtime 的多组异步 scheduler。


`providing_owner_execution` 将共享依赖删除扩展到会提供服务的 owner：owner 初始
Inactive 且显式空表，允许 Unit／Operation／Provision；其 provision 与所有 foreign
声明分离，依赖键仍可共享。foreign 新步骤仍限 Unit／Operation，其 Unload 只消费
本段新 token。`selective_foreign_recovery` 只要求涉及 foreign 的跨记录交换，避免
错误要求同一 owner 的严格 Provision 与自身交换。`every_prefix` 构造真实目标轨迹，
`terminal_deletion` 推导末次 owner Unload 成功及终点相同 control／全部表观察。
历史、inverse 函数和 accumulator 不要求字面相等。

`providing_owner_examples::bootstrap_execution` 从 empty 建立实际初始 history；
完整例中 owner 发布私有键值 99 并对共享键加 5，foreign 再加 7 并实际卸载，
owner 最终按 LIFO 减 5、撤销私有键。删后执行使用自己的回执，将 token 3 压为 1，
两边共享值都恢复为 10，私有表都为空。更一般的 owner 消费者、foreign 新 Provision、
旧 live journal、Child 与动态 registry 尚未纳入这个删除定理。


`strict_batch_recovery` 为旧 foreign inverse 提供新的代数连接：保持整个 pending own
批次的 redo／undo 局部见证，从源调用成功、respect 及与整批 redo／undo 的严格交换，
推导目标调用和恢复都成功，无需给每条旧 inverse 重新假设单独的反向见证。真实
`Provision(9); +1` 的回执说明在值 10 的 cut 上单条 Provision 回程性质为假，
完整 LIFO 批次却仍可恢复；另一例实际重放这些旧回执。

`old_receipt_support` 从真实 empty-origin 历史取得旧回执及其权限，
`old_journal_unload` 将旧 Unit／Operation Unload 接到批次交换与实际目标恢复，
`old_journal_closure` 再推出末次 owner Unload 和两边最终 control／所有表观察相等。
`old_journal_interleaving` 进一步允许窗口内的新 foreign Unit／Operation landing
及真实 Unload；后者消费本窗口新 token。固定 registry、owner 初始 Inactive／空表、
owner 私有 provision 与所有 foreign 声明分离仍保留。窗口末尾的 Unload 可消费
cut 前的任意长度操作回执，随后证明 owner 最终恢复和完整两端执行。非空例把新
foreign token 3 压为 2，保留旧 token 1，两端共享值均归 10、私有表清空。
`mixed_age_unload` 已解除末端栈的纯旧限制：同一 episode 的真实栈 `[1,3]`
在目标成为 `[1,2]`，一次 LIFO 恢复消费两种 token，再接 owner 最终卸载，证明
终态控制和全部表观察一致。旧 token 的位置不变，新 token 必须使用压缩映射，
两者都指向各自真实历史中的回执。

`old_provision_support` 另行处理会改变表定义域的旧 Provision：从源端真实
逆操作成功和已安装 owner 的 no-user guard 推导键分离，得到严格交换和目标删键
的定义域，再构造合法目标 Unload。通用定理从良构截点开始；具体例提供从空起点
建立的 K=10、Q=99 前缀。它目前只覆盖单个旧 Provision，尚未接最终 owner 卸载。
Inactive owner 的真实反例说明不能删掉“已安装”前提。
`old_provision_journal` 已把末端清理扩展到任意长度 Table journal：旧 Provision、
旧／新 Unit／Operation 逐项用真实源端成功推目标定义域，随后接最终 owner 卸载。
非空例的 `[1,2,4]` 映射为 `[1,2,3]`，两次卸载后共享值为 10，两张私有表均清空。
它保留前缀窗口内只卸载新 token 的约束。

`internal_old_unload` 另行解除操作回执的内部年龄限制，支持窗口中任意数量和位置的
旧／混合 Unit／Operation 卸载。证明直接在真实 source/target 状态上归纳；landing
catalogue 只保存 own redo/undo 的来源，绝不将忽略 Unload 的目录当作值执行。
实例在 mixed Unload 之后继续 owner Finish，再完成最终恢复。

`internal_table_unload` 将内部清理统一为任意年龄 Table journal，包括 Provision。
owner 尚 Inactive 时从真实空 journal 推出 own F/W 为 identity；已安装时用真实
no-user guard 推导删键分离。`foreign_provision_transport` 再从当前缺键和已定义
own inverse word 推出新 foreign Provision 与 pending own stages 异键，构造实际
目标 landing 与更新后的 batch；不预设目标成功。

`generalized_table_deletion` 把两者接入同一完整归纳：固定 registry、owner 初始
Inactive／空表和私有 provision 分离下，所有 Unit／Operation／Provision landing
及任意位置的旧／新 Table 清理均可交织。目标完整执行与最终 owner Unload 为结论。
实际例中新建 R=77 后做两次共享操作，foreign journal `[3,4,5]` 压为 `[1,2,3]`；
清理源端 29→15、目标 24→10，再经 owner 恢复，两边都为 10 且 Q/R 清空。
Child、owner 消费者、动态 registry 和窗口内 owner 自己的 Unload 尚不在该 profile。

### Definition 81 的记录与 host 投影

`configuration_entry::Entry` 准确编码原文六字段；URL、两类注解和配置保留为
不透明参数，没有把 parent 塞进记录。父节点与 stable id 组成 reconciliation key。
构造、行政开关和配置编辑的帧条件由 Verus 检查；模块与原始配置的绑定单独定义。
因此该编号定义已完整 formalized。

普通 Rust 的 `Entry::as_paper_entry` 只投影具名插件叶节点，并要求调用方显式将
工厂名解析成 URL；不把注册名直接当作 URL。group、include、未解析名称和含孩子的
条目不在此投影范围。测试覆盖父级禁用不改变子条目自己的 disabled 字段，以及
intercept 前的原始 config 保持。整个树的解析、增量协调、回调执行和持久化仍属于
host 连接缺口；没有用六字段定义替代这些实现证明。


### Definition 23 的两种 realization

`effect_realization` 用 location-based heap 形式化 alias：in-place 修改同一 cell，
捕获真实 inverse 恢复；derived 分配 fresh child、保持所有旧 cell，值 inverse 是
identity，恢复动作另行 discard child 并返回 parent。两者当前 context 的 forward
值与直接恢复终点相同，不声称前向整个 heap 或 inverse 函数相同。具体例明确展示旧
alias 读值 11 与 10 的区别，child 后续改为 99 也能通过 discard 恢复 parent。
这是该定义的数学模型；不代表任意 Rust 指针、嵌套共享对象、callback/future 或
Definition 28 递归继承已经 refinement。

### 接口 S 到全键 K 的函数字段观察

`interface_observation` 对任意 carrier、投影、键、值和 continuation index，逐键
合并接口内观察与接口外 frame，推出全键函数关系。总函数和严格部分函数均覆盖；
部分函数的成功域来自原局部关系，返回 inverse 保持其真实成功域，没有失败 no-op。
同一 frame 再通过最大 bisimulation 提升完整 continuation 与闭合恢复见证，不假设
索引可数或共享终止 rank，也没有用最大关系替代 least membership。

`model_iterators` 与 `model_accumulators` 直接供给既有 `functional_quotient` 的全键
函数字段关系，允许不同 roots、tokens 和 journal 长度。例子中不同 bool iterator
持续迭代，隐藏值 10/20 不同，visible 值及接口外键相同。正式反例和负控说明省去
接口外 frame 会使该推导失败。每个原组件的全域 frame 来源、Child 注册表同步以及
原文纯 table 函数关系与严格解释器仍需连接；下文的九规则模拟使用更强的合法输入 PER。


### 任意 I/J 的严格 grammar independence

`dependent_independence` 直接对真实 `dependent_grammar::family` 证明
`iterator_bridge::independent`。左右可以有不同 operation/argument/outcome carrier，
continuation 分别为任意 I/J；没有从任意索引到 nat 的枚举假设。单节点投影只为复用
键代数暂时丢弃 continuation，随后用真实 raw outcome 恢复原 selector 的结果。

实际 reach 保持 least grammar membership；有限 Map 的实际 forward/returned inverse
与无限 Map 单阶段解释保持成功域、值和 inverse 对应。两向 generator 等式、任意 word
交换、yield 稳定和最大 continuation 关系给出完整严格结论。前提只包含弱观察 primitive
理论、provision/interface 分离和 shared-key scalar 独立，未把整个 monoid 结论塞进
组件前提。

非空例在同一键上做 +5/+7，左 outcome 为 int、右为 bool；索引分别携带任意谓词与
任意整数集。实际 next 由结果选择，缺键保持失败，两条真实 inverse 将 22 恢复至 10。
负控保留 scalar generator 交换、只移除 yield/outcome 稳定，正常编译后证明失败。
原文不带成功守卫的 total Definition 42/47、完整 Γ 解释仍未由此自动成立。


### 动态注册表中的完整 Table 删除

`dynamic_table_registry` 从真实 source O-Insert/O-Remove 推出 target 对应步骤。
新 Insert 仅另查 dependency 不读取 owner 的私有 provisions；provided-key 分离
来自原插入守卫。Remove 使用 source 的真实 retired/Inactive/空表/无 child 条件，
并沿实际 token 压缩运输 live Child-reference 守卫，没有要求历史从未引用该名字。

`dynamic_table_deletion` 将它接入全部前缀归纳：owner 的接口保持，foreign 名字
可插入、卸载、移除和重用；每个历史 entry 读取自己的原始 input，不读取已移除
actor 的当前接口。任意年龄 Table journal、所有 Table landing、完整删后执行和
最终真实 owner Unload 同时成立。source 的逐前缀分离与 target 成功均为结论。

实际例先保留 owner 的 Q99/+5，再插入 actor3 执行 +7、卸载并移除：源端共享值
22→15，目标17→10，真实 token3 压为1，删除后历史仍保存 actor3 的 entry。末次
owner Unload 将两端都恢复为10且Q为空。删除局部 dependency guard 的可编译负控
使真实 successor separation 结论失败。

该定理解除上述 Table profile 的固定注册表限制；owner 仍须初始 Inactive/空表且
保持注册，新增依赖不消费其私有服务。Child landing/cleanup、owner 消费者和窗口
内部 owner 自己的 Unload 尚未纳入，原文完整 Γ 与一般 confluence 仍开放。


### 真实严格函数的配置模拟

`strict_partial_quotient` 直接解释 `mixed_grammar::run` 和 `restore`。root 与
current 比较最大 bisimulation，accumulator 比较实际部分函数；history、token、
栈长不要求相等。追加 landing 时，两端保存各自真实 receipt，组合真实 inverse。
从源执行构造九规则 target successor，再证明目标步骤合法和全部中间配置良构；
调用与卸载的成功域均由关系推导，失败仍为 `None`。

`strict_partial_quotient_reflexive` 将任意索引的最小 dependent grammar 接到
函数自相关，并证明代码别名可以不同。静态 primitive 合同负责类型合法性，真实
调用守卫负责当前声明，两者各自保留。`strict_partial_quotient_per` 从对称性和
传递性推出严格函数、最大 bisimulation 与配置关系的 PER，不要求所有输入自反。

非空实例从两条真实空起点轨迹开始：一端读到 0；另一端在外部 +1 后读到 1，
再多读一次，外部真实 Unload 随后恢复 0。切点 root/current 不同，worker 的真实
inverse word 长度分别为 1、2。例中展示合法注册输入上的 `None` 与 `Some`，
并由通用定理输送 Finish、Retire、Leave、Unload 全部后缀。

关系的测试输入要求两端良构、actor 注册、control 相同和逐 provider 的表域相同；
它是明确的合法输入 PER，不能替代 Equation (54) 比较函数字段时使用的纯表
观察；Equation (54) 的完整状态关系本身也比较 control。当前构造要求
Table 指令及 live Table receipts；Child 创建、退休、全域原组件和递归 Γ 的桥接
仍开放。下文补齐了 Definition 58 的条件式定义；Lemma 60 的原文定理仍为 partial。


`strict_partial_quotient_boundary` 还机械化了此限制的必要性：同一实际例的两个
空起点前缀均良构、actor 均已注册，全部 table 与 `project(full)` 字面相同，
但 committed provider 不同使同一 root 和两条真实 inverse word 呈现 `None/Some`
差异。因此它们不满足严格 pure-table 函数自相关；在合法输入 PER 下仍自相关，
因为该关系不将这两个输入配成一对。这不反驳原文假定的 total witnessed 组件。


### 原文条件式定义与实现所属关系

`paper_components` 汇合 Definition 48 的完整 `(d,p,e)`：给定 G、coeffect 投影
和总 iterator family，组件须具有最小 `paper_witnessed` membership，而非只有
最大闭包。实际安装事件另受 p 约束；仅净表域变化不足以充当事件来源证明。
非空整数例执行 +1 并返回真实 -1 inverse。该定义没有添加 d/p 不相交或必须提供
全部 p 的条件，也不假定任意严格 grammar 都属于原文 ℭΓ。

`paper_observations` 汇合 Definition 58 的任意 G/N/K/V/I 接口：全 phase table
投影、原 Equation (54) 函数字段关系、有限／无限空起点执行、最大 installed episode
及冻结 state map。实际 Model adapter 在所有输入上使用同一 owner 选择，因此
函数字段中的全域比较不会被当前状态良构条件悄悄缩窄。现有九规则 bracket 与
state map 的真实 factorization 也接入此接口。

因此 48、58 按“原定义已准确编码”的标准标为 `formalized`，与已完成的 23、81
一致。这不证明非平凡递归 Γ 存在，不证明所有 strict/Child 程序满足原组件类型，
也不自动证明 57、60 或宿主 refinement。Definition 52 的 full Component 输入门已由下述条件式原语接入；56 的缺口仍是原 total lift 含义，而非最小语法尚未编码。

`paper_confinement` 对齐 Definition 55 的 Writes，而不额外禁止 foreign dependency
键的存在性变化。Reads 的 source-indexed 原句读法与对称 presence-aware 读法分别
命名；双向前者等于后者，非空 registry 例证明单向前者并不对称。完整 map/effect
谓词量化所有输入、reachable stages 和每个实际返回 inverse。原文缺席名字的含义
及 Child 例外的原语解释仍需明确，故 55 继续 partial。


### Foreign Child 的真实落地与撤销

`foreign_child_transport` 将真实 fresh Child 创建、payload、root 和捕获 receipt
接入删除 owner 前后的共同 registry。Child 的全表投影恒等仅用于值批处理；
freshness、提供项分离、生命周期 guard 与 live-journal retention 分别证明。
任意年龄的纯 Child 栈可逐项执行真实 retirement，并从源执行推出目标撤销有定义。

非空空起点例包含 owner 发布 Q99／执行 +5、foreign parent 创建 child3、parent
卸载后移除 child3、最后 owner 清理。压缩的 token 指向目标自己的真实记录，
历史输入保持原值；仍被 live receipt 引用的退休 child 不能提前 Remove。
下述组合完成混合 Table／Child 栈的受限全段删除；原文总 Component witness 仍单列。


### Typed instantiation 与依赖值解释

`paper_typed_context` 将每个 key 的值域写成所有 G 输入都满足的投影条件，
并连接有限 Map、实际 FiberCodec 及异构 Flag／Count 例。使用共同枚举载体不等于
所有 key 具有同一类型；组件真实 +1 操作及返回的 -1 inverse 均保留原值域。

`paper_instantiation` 接入原 Definition 48 的完整最小组件 witness，而非只检查
当前可执行语法。Definition 52 的实际 fresh name 同时传给 body 与 inverse；
inverse 只退休所捕获的 child。局部 editor 的 readback／background 联合单射且
满足精确 Insert／Retire frame，不要求任意函数字段 registry 都有表示。
非空可满足例包含 Active parent 表、typed Unit child 和依赖名字的 continuation。

52 因而按条件式原语定义标为 `formalized`。这不关闭递归 Γ、57 的全域 witness
或未来任意执行的 retention；缺席 child 的 retirement 明确失败，未被补成恒等。


### Mixed foreign journals 的完整删除归纳

`mixed_foreign_restore` 与 `foreign_child_deletion` 将 foreign Child 接入动态删除
归纳。外部真实日志可任意混合早于／晚于 cut 的 Table、Provision 和 Child receipt；
递归实际执行捕获 child 的 retirement，并证明另一侧的部分逆函数仍有定义。
只限制被删除 owner 的新记录为 Table；foreign 历史不再套用纯 Table 假设。
target 的完整执行、所有压缩 token、最后 owner 的真实 Unload 和观察等价均为结论。

非空例先执行 foreign +7，在 owner Q99／+5 中插入 Child、R77、+11，得到真实
source 栈 `[1,4,5,6]` 和 target 栈 `[1,2,3,4]`。foreign Unload 退休 child 后
才允许 Remove；最终 owner 撤销恢复 K10，Q／R 表为空。删除 child 的私有依赖
分离 guard 会触发 `source_metadata` 的真实前置条件失败。

该组合也扩大了 68／69 的受限终点恢复范围：`closed_deletion` 从真实空起点
setup、源执行、初始 Inactive／空表 owner 及局部 fragment 条件，推出最后 owner
恢复有定义、真实 guarded Unload 合法、与构造出的 surviving execution 终态具有
相同 control、逐表观察等价，以及两侧 owner 表为空。foreign Child 的落地和混合
journal 清理已包括在这个同一归纳中，不再只是独立的 retention 结论。

这段终点定理没有直接把任意中间前缀等同于原 Equation (55) 的冻结 Ψ 组合；
`landing_catalogue` 只提供真实历史来源，不能当作省略旧 Unload 的值 replay。
68、69、79 均继续 `partial`：该构造要求 owner 保持注册、使用 Table 指令、
私有提供项无 foreign consumer，且窗口内部不包含 owner Unload。owner Child、
原 full-context Component／independence 桥及无限执行仍单列。


### 全历史 pairwise independence 的条件接口

`paper_trace_independence` 编码 Definition 65 的复合谓词，保持 Definition 42 的
两侧完整变换 monoid 与双向 reachable yield stability。Child 的 d／p 与实际
fresh actor 下的 root 在同一个 greatest relation 中比较；解释出的 family 必须
与 View 的真实函数字段一致。历史量词覆盖有限／无限执行中的所有已持有记录，
包括内部 Child、已删除名字及名字复用。原文字面不同名字与不同 incarnation
两种条件分别命名。

共用操作 key 来自 semantic reach，不以声明或已调度调用代替。总函数 lift
adapter 与保留 None 的 strict Library adapter 分开，后者从真实 scalar laws
推出跨全部 argument monoid 的 raw outcome／inverse stability。非空整数平移
例同时保留缺键失败；Unit 例构造空起点的插入／退休／移除／复用轨迹。

65 仍为 `partial`：payload provenance 尚不是 typed52 与 captured Retire 的完整
解释；strict adapter 也未证明总 Language 等于真实部分解释器。因此不升级 66。
