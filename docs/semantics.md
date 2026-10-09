# 论文语义与验证边界

本项目以 *A Programming Paradigm for Spatiotemporal Composability* 的 [arXiv:2608.25512v1](https://arxiv.org/abs/2608.25512v1) 为规范来源，以锁定的 Cordis 和 DeepSeek Harness 官方源码为功能参考。目标是用同一份可执行 Rust 内核承载 Verus 契约与证明。当前证明涵盖 registry 结构、provision 唯一性、已安装依赖的类型与完整覆盖、依赖链的严格下降顺序、解析唯一性、begin/iter/finish 的绑定条件、provider 存活、恢复守卫及 cleanup token 的 LIFO 顺序；另有具体可逆资源实现与明确前提下的效果代数证明。不能据此声称整个 Cordis、任意插件或论文全部定理已被验证。宿主的显式 restart/update 和子树退休是额外运行时操作，下面单独标出。

控制状态投影、逐操作 simulation、实际执行的 stage 协议、witness journal 与历史正规化现已单独记录在 [论文 refinement](refinement.md)。下文讨论完整语义以及尚未纳入验证的宿主边界。

新增的 value-carrying 规则规范、受控资源 Driver、真实 child inverse、条件无死锁与静止控制唯一性，也在该文档中分别陈述。机械化审计确认原文 Lemma 62、75、77 及 Theorem 71(2) 无条件闭合断言的 Unit 反例；Child／canonical 的其它见证先限定于已编码规则，其原文组件桥接尚未闭合，详见 [论文审计](paper-audit.md)。严格 guarded fresh-binder 解释中另有字面同名输入反例，但它未建立原文全域组件 witness；Theorem 80(2) 的一般结论及域桥接仍待证明。

## 来源与版本

论文共 92 页，v1 发布于 2026-08-26；2026-10-03 检查官方 arXiv 页面仍只有 v1。官方 paper 仓库目前只提供指向 arXiv 的 README。[upstream.lock.json](../upstream.lock.json) 固定三个官方仓库的 commit、source tree，以及论文 PDF 和定位文本的 SHA-256。

[reference/README.md](../reference/README.md) 记录论文副本的来源和许可。本文的页码以论文页码为准；`text:L` 指本地提取文件 `reference/arxiv-2608.25512v1.txt` 的行号，供离线定位。该提取文件用于检索，数学排版以 PDF 为准。旧 TLA+ 项目中的 2026-08-13 草稿与旧定理编号不作为规范。

## 状态、身份与两种解析

论文 component 是 `(dependencies, provisions, effect iterator)`；fiber 是一次实例化，具有父节点、服务表、退休标记和生命周期。依赖与 provision 在 fiber 插入时固定。实现把依赖端口表示为 `(key, realm)`，把提供者表示为 `FiberId`。ID 单调分配且不复用，是对论文 fresh-name 条件的保守实现选择；不是服务值，也不是配置 entry 的永久身份。

四种 phase 对应如下：

| 实现 phase | 论文状态 | 是否 installed | 能否用于新的依赖解析 |
| --- | --- | --- | --- |
| `Inactive` | Inactive | 否 | 否 |
| `Loading` | Reloading | 是 | 否 |
| `Active` | Active | 是 | 是，限已安装的 provision |
| `Unloading` | Unloading | 是 | 否 |

`present` 区分 registry 中仍存在的条目与已删除的 tombstone。`retired` 表示退休请求，单调从 false 变 true；它不等于已卸载或已删除。`restoring` 表示已经通过恢复守卫并进入清理区间，是拆分原子 L-Unload 所需的运行时状态，不是论文增加的第五种 phase。

实现另保存每个 fiber 的 `generation`：初始为零，只有成功 begin 才递增，溢出时在修改前返回 Capacity；compaction 不重置它。`ChildEpisode` 捕获此值以区分 committed 完全相同的两次 activation。generation 是同一 Kernel 实例内的句柄检查元数据，不进入论文控制状态投影，也不是跨 Kernel 的身份。

`target(n)` 是根据当前 Active provider 重新计算的目标：若 n 自身 retired 或有必需依赖缺失，则没有目标；否则每个声明端口得到一个 provider ID。`committed(n)` 是该 episode 开始时保存的 `{key, realm, provider}` 绑定，在 Loading、Active、Unloading 期间保持不变，清理完成才清空。Rust 外层在 setup 中沿 committed 获取服务，清理 closure 可以捕获这些服务，不能依靠面向宿主的 `Runtime::get` 重新解析旧依赖。

内核仅存 provision 声明，不存任意类型的服务 payload，因而以 Active provider 提供全部声明端口作为抽象。外层在 setup 返回后检查每个 provision 确实已有 payload，才调用 finish。这个 total-provision 策略比论文允许的部分 provision 更窄；普通宿主的任意 payload 与检查逻辑仍未整体形式证明；独立 `MixedDriver` 已验证 `u64` 服务表的发布完整性，并通过 `total_targets_agree` 接到实际表解析。

来源：Definition 48–53，pp31–36，text:1366–1593；式 (46) 定义发布视图，text:1439–1474。

## 论文规则到内核操作

下表给出语义对应和接口行为。控制投影已由独立抽象规则和具体方法的后置条件连接；iterator/effect 部分的组合边界见 [论文 refinement](refinement.md)。Rust 外层同时提供同步与异步 setup、多步 `EffectIterator`。每个新 stage 之前检查 `check_iteration`；已开始的 stage 在目标改变后仍允许落地，记录 inverse 后转入恢复。stage admission、在途落地和 token accumulator 由实际调用的 `StageProtocol` 验证；future、callback 以及整个 scheduler 的组合仍未获得整体 refinement 证明。

| 论文规则 | 内核需要检查及保持的行为 | 来源 |
| --- | --- | --- |
| O-Insert | fresh ID、parent 存在；固定 dependencies/provisions；同一 `(key, realm)` 不能被两个仍注册 fiber 声明提供；初始 Inactive、未退休、无 committed | p34，text:1519–1522 |
| O-Retire | 仅请求退休；不立即删除条目，不跳过 cleanup | p34，text:1523–1535 |
| O-Remove | 仅删除 retired、Inactive、无保留服务且没有孩子的条目 | p34，text:1525–1535 |
| L-Begin | 仅当 target 存在时进入 Loading，自动解析并保存整组 provider identities | p36，text:1599–1601 |
| L-Iter | 每次成功 stage 记录对应 inverse；继续前检查 target 仍与 committed 相同 | p36，text:1602–1604 |
| L-Finish | 完成初始化时再次检查 target=committed，再进入 Active 并发布服务 | p36，text:1605–1607 |
| L-Divert | 初始化中 target 改变则进入 Unloading；已在途的 stage 可以落地，其 inverse 必须入栈；不能短暂发布为 Active | p37，text:1626–1641 |
| L-Leave | Active 的 target 改变时进入 Unloading；立即停止用于新解析，保留旧服务、committed 和 cleanup | p37，text:1629–1646 |
| L-Unload | 先等待所有仍 committed 到自己的 installed consumer 完成清理，再开始自己的恢复；最后清除 committed 和服务，进入 Inactive | pp36–37，text:1621–1653 |

内核把 L-Unload 拆成 `begin_cleanup` 与 `finish_cleanup`。前者检查依赖守卫并设置 restoring，后者表示外层已经完成全部清理后才可撤销绑定。证明必须同时保证：restoring provider 不会接受新的 committed consumer；已经存在的 committed consumer 不会在 provider 清理完成前失去其 binding。外层必须准确调用完成接口，不能把“发起异步清理”当作“已完成”。

当前公共 `Kernel::leave` 接受 Loading 或 Active，不强制 target 已改变。Rust 外层在 target 改变、setup 失败或显式 restart 时调用它。因此这是已单独建模为 `Restart` 的宿主扩展；新增 `leave_if_changed` 只在 target 失配时成功，其后置条件直接证明 L-Divert / L-Leave。无条件 `leave` 不是 L-Leave 的精确 refinement；尤其是稳定 Active 的主动 restart 并非原论文 L-Leave 规则。`Runtime::restart` 可以清除失败 latch 并让同一 fiber 开启新 episode，`Runtime::update` 保留 dependencies/provisions 和 ID、替换 setup 后 restart。原论文配置 revision 的 retire/remove/reinsert 证明不能直接用于这些操作。

`Runtime::replace` 另提供接近论文 configuration revision 的组合操作：retire 旧实例、等待其清理与删除、以新 ID mount 新 plugin，再等待 settle。它仍是普通 Rust 编排，尚无整个组合操作对论文的 refinement 证明。

论文允许 O-Retire 后 provider 暂时仍为 Active。发布视图的式 (46) 仅按 Active 筛选，不按 provider 的 retired 标记筛选；其自身 target 变为空后，由 L-Leave 撤下发布。也允许 consumer 暂时 Active 且 target 已与 committed 不同，直到它执行 L-Leave。因此 **`Active ⇒ target=committed` 不是本项目的全局不变量**。只有 quiescent 状态对所有 Active fiber 要求相等（Definition 53，pp35–36，text:1572–1581）。

## 服务恢复、父子与 realm

依赖守卫以 provider identity 检查全部 installed consumer，包括 Loading 与 Unloading 中的 consumer。它不能只扫描 Active，也不能只比较 key、服务值或 target。相同值由不同 provider 提供仍是不同绑定。论文依据是 Definition 54 与 Theorem 70，pp36–37、47–48。

论文中子 fiber 的创建应登记一个“退休该 child”的 inverse，而非立即 remove child。父子关系本身不产生依赖守卫：若 child 没有声明依赖 parent 的服务，parent 可以先执行自己的 inverse；删除 parent 条目仍需等孩子删除。如果两者共享资源，必须通过显式服务依赖和效果契约保证顺序。来源：Definition 52，p35，text:1544–1559；p37，text:1663–1666。

Rust 外层支持宿主 mount 与 `Setup/AsyncSetup::mount` 动态创建 child。后者把退休 child 的 inverse 登记到父效果组的相应位置：inverse 发出 retire，不等待 child remove。这遵循 Definition 52 及 p37 的明确说明，避免父消费子服务时形成相互等待；所有权本身不保证 child cleanup 先于父的其它 inverse。显式 `dispose` 请求退休子树；parent leave 时，实际消费 parent 服务的后代必须提前退休以满足依赖守卫。父条目删除仍等待所有 child 删除。宿主子树驱动与任意子树恢复的观察等价未形式化。

同一 logical key 可在不同 realm 由不同 provider 提供。当前模型固定 fiber 插入时的 `(key, realm)` 端口，直接对应 §4.4 将键集扩展为 `K × R` 的解释。同 realm 内的 provision 冲突检查覆盖仍存在但未激活的条目，不能在旧条目尚未 remove 时复用该 provision。运行时改 realm 或 dependencies/provisions 需要 dispose、settle、重新 mount；不会原地改变这些声明或把 retired 改回 false。单纯替换 callback 的 update 是上面说明的额外操作。论文的完整配置 revision 见 pp56–57，text:2666–2710。

`child_driver::ChildDriver` 是独立的可执行验证路径，私有持有 Kernel 和真实 child journals。删除前检查全部 inverse 引用，仍被引用则返回 `Retained`；child landing 遇 target 漂移时直接进入 Unloading。其投影证明的是 child retention 和实际 child-effect／控制转换，并不包含任意服务 payload 或整个 Runtime 的模拟。父卸载执行真实 LIFO retirement，保留论文规定的“不等待 child remove”。

## Verus 可以支持的结论

当前 `Kernel::wf` 及相关契约覆盖 Definition 63 / Theorem 64 的一部分安全义务（p43，text:1950–1997）：

- 每个仍存在的非 root parent 引用有效，parent ID 小于 child ID；不存在的节点为 Inactive 且不 restoring。
- 同一 `(key, realm)` 的 provision 在所有仍注册 fiber 中具有唯一 owner，包括 Inactive 与 retired。
- 每条 live committed link 连接 consumer 声明的 dependency 与 provider 声明的匹配 provision；双方都仍存在且非 Inactive，provider 不 restoring。
- 每个 installed fiber 的所有 dependency 均被 live committed link 覆盖；没有超出声明域的绑定。
- 沿已安装依赖链，link 的登记位置严格下降，所以不能形成已安装依赖环；新 activation 的 links 追加到现有历史之后。
- finish、leave、retire、begin_cleanup、remove 保持所有绑定记录不变；begin 添加绑定，finish_cleanup 撤销自己的绑定。
- `begin_cleanup` 成功时，不存在 live committed link 指向该 provider，且后续转换保持恢复期间不能新增指向它的 live link。
- `ordering` 证明从 wf 推出已记录 consumer-provider 关系的 provider 仍存在、installed 且未开始恢复。

查询与 activation 方法还有以下正式契约：

| 方法 | 已陈述并验证的结果 |
| --- | --- |
| `resolve(port)` | Some 的 provider 为 Active 且声明匹配的 `(key, realm)` provision；None 表示没有匹配的 Active provider |
| `target(id)` | Some 中每条 binding 都属于已声明 dependency 并匹配 Active provider，且覆盖每个 dependency；None 表示 fiber 不存在、已退休或至少一个 dependency 无可用 provider |
| `committed(id)` | 返回项均对应 live binding，且覆盖该 consumer 的全部 live binding |
| `begin(id)` | 成功后的 committed 相对于调用前状态是完整 target：条目有效，且每个 dependency 均被覆盖 |
| `check_iteration(id)` | 成功说明仍在 Loading 且 committed 与当前 target 一致；没有改变状态 |
| `finish(id)` | 成功说明调用前的 committed 覆盖全部 dependency，所有 provider identities 与当时解析匹配；保持原绑定记录 |

这些 soundness/completeness 契约使用端口与 provider identity，而非服务值。`finish` 契约刻意指向调用前状态，不引入 `Active ⇒ target=committed` 的永恒条件；其他组件以后仍可以改变 target。

这些约束现已全部写入 `wf`，并由实际转换方法保持。`resolution_unique` 从 provision 唯一性推出同一 port 的解析唯一。`draining_can_progress` 进一步证明：有限 registry 中若至少一个 fiber installed，且所有 installed fiber 均为尚未恢复的 Unloading，则至少一个 fiber 没有 committed dependent、可通过 cleanup guard。证明选取最后登记的 live link 的 consumer；若无 live link，任一 installed fiber 即可。它排除了这个状态下依赖守卫的死锁，不保证用户 future 完成，也不等于完整 Theorem 73。payload、effect history 和外层调度尚不属于内核状态，不能把 `wf` 直接称为整个 calculus 的 refinement。机器结果以当前源码的完整验证记录为准。

可执行入口还公开了局部使能性的充要条件：`begin` 在且仅在 `begin_enabled`（含 generation 容量边界）时成功，`begin_cleanup` 在且仅在 `cleanup_enabled` 时成功；后者将 `draining_can_progress` 的守卫见证接到真实调用。`StageProtocol::admit` 及资源／程序包装层也明确给出 pending 或新阶段目标匹配时的接纳条件，并由真实可执行客户端验证取消后的落地路径。`paper_coherence` 和 `paper_iteration_guard` 已将内核守卫与论文投影接通，`check_iteration`、`finish` 在且仅在 Loading/coherent 时成功，不再附加向量顺序／重复次数检查。固定 `ProgramEpisode` 的构造检查精确识别合法指令；真实执行循环推出逐步成功、递减终止和含最后一次终态调用的计数，`execute_and_recover` 再调用真实逆操作恢复输入资源。这不改变 Theorem 73 的部分完成状态；完整宿主捕获、动态 child／一般 continuation 以及整段宿主执行仍需连接。论文条目、代码路径和 `verus-tla` 的适用判断见[进展合同审查](progress-contracts.zh-CN.md)。

定义 53 的绑定投影现在由 `episode::binding_set` 和实际 `same_bindings` 比较接通，保留完整 `(key, realm, provider)` 身份，忽略完全相同绑定的顺序与重复次数。`Kernel::paper_captured_target` 在 `wf`、已登记 Loading actor、捕获集合等于 committed 的前提下，将真实 `target` 观测的匹配条件证明为论文控制投影的 coherence。`Driver::admit`、`ProgramDriver::admit` 在且仅在 actor 已登记且 Loading 时返回 `Ok`，其中布尔接纳值恰好为 pending 或 fresh、未取消且 coherent；`ChildEpisode::admit_current` 还检查捕获和 generation，旧 episode 不因绑定相同而复活。`begin_preserves_target` 还将成功 Begin 接到后态 iteration guard；两个已验证 driver 的 Begin 建立 fresh、未取消且 coherent 的 episode，`Driver::begin_and_admit` 顺序执行真实 Begin 与接纳，在且仅在有界 `begin_enabled` 下建立首个 pending 阶段，不要求调用者假设接纳成功，也不执行其效果。普通 `LifecycleDriver`、阻塞诊断及原生宿主的迭代／发布守卫复用相同比较，但外围异步代码与真实捕获值仍是测试边界。匹配采用同序 O(n) 快路径及非同序 O(nm) 双向成员扫描，不额外分配集合，不据此宣称性能改善；捕获向量、逆序日志及 child 顺序均不改写。

动态 child 注册的真实定义域也已连接：`Kernel::check_insert` 只读检查 `insert_enabled`，实际 `insert` 复用该检查并公开成功 iff。`refinement::insertion_domain` 与 `Kernel::paper_insert_domain` 将 O-Insert 的 parent 登记／provision 预留条件，与实现的有限身份容量、声明向量各自无重复分开说明；不要求 child dependency 已可用或 parent 活跃，退休但仍登记的节点仍预留 provision。规范谓词 `ChildEpisode::current_matches`、`land_enabled` 描述 pending、当前捕获／generation 与该插入域，实际校验由 `check_snapshot`、`check_child` 执行；自身及 `ChildDriver` 的 `check_child`、`land_child` 都有相同域下的成功充要条件。`ChildDriver::check_and_land_child` 在没有注册表操作插入的一次调用中执行真实预检查与落地，从检查通过推出实际落地成功，无需调用者假设返回成功。预检查既不预留端口也不绑定 generation，interleaving 后实际落地仍重新检查；失败保留 Kernel/control、逆操作前缀与 pending，但 detached generation 可能已捕获，wrapper cancellation 也可能被刷新。这只是注册域合同，不是任意 child body 的 Component membership 或总性证明；`guarded_child_domains` 的预留冲突反例、失败语义和原始完整 Component／context 义务不变。

同步闭合 `MixedDriver`／`FreshDriver` 还公开了真实单步的充分必要条件。`MixedDriver::insert` 在且仅在蓝图索引、所需蓝图库前缀与 Kernel 插入域有效时成功；`provider` 的成功等价于实际 primitive resolver 返回身份，`execute` 的成功等价于独立的 `primitive_enabled`。`ready` 检查已登记 Loading/coherent actor 及当前指令，`step_enabled` 再要求实际效果定义域与终态 `complete_after`。后者允许本次 Provide 补齐最后的值，不错误要求调用前就完整发布；`commit_landing` 使用落地后的实际表。Fresh 的 `selected_instruction` 以当前 `next_id` 实例化 Child，仍保留预留冲突与值域检查。公共 `step` 成功 iff `step_enabled`，错误通过副本事务保留完整 `same`；内部 `execute`／`step_inner` 的失败可能已修改副本，不具有无条件回滚合同。同一执行方法由 Cargo 编译并接受 Verus 检查。这补齐同步单步局部使能性；跨调用 admitted landing 的精确域在下文单列。两者都不是整段动态执行终止或原论文完整总性证明，第 57、73 条继续 partial。详见[进展合同审查](progress-contracts.zh-CN.md#真实-mixedfresh-解释器的精确单步定义域)。

`FreshDriver::run_until_blocked` 进一步执行真实的同步 step 循环，只要求 `wf()`，不传 fuel，也不假设下一步成功。它从实际前向 pc 导出 `code.len() - pc + 1` 的秩（位置缺失或无效为一），在终态 Finished／finished Child 或首个真实错误处有限返回。`RunReport.steps` 是 `u128`，只统计已提交调用并包含终态调用；错误尝试不计入，成功前缀保留而失败步通过原有事务回滚，零提交时完整机器满足 `same`。无错时当前 actor Active 且 current 为 None；错误时最终 `step_enabled` 为 false。新 child 保持 Inactive，不自动执行。报告的 `refines` 条件化地延伸输入机器已经表示的任意良构源配置，源序列由实际成功调用构造，公共 proof 方法 `RunReport::advance_source` 在已有 `refines`、输入 representation 与源良构条件下提取该执行供组合；它不从任意 `wf` 推出输入 representation 的存在，也不单独证明 empty 起源。ghost outcomes／源序列在运行时擦除。这是单 actor 的有限返回与前缀连接，不是全图静止、primitive 总性或整个定理 73。

[`run_from_empty`](../crates/cordis-kernel/src/fresh_bootstrap.rs) 则从真实 new/empty 构造机器，先调用 `run_script`，仅全部准备命令成功后才运行指定 actor。它无需输入机器、源表示、fuel 或未来成功假设。`FromEmptyReport::refines` 建立同一条从 empty 出发的源执行，在准备接缝与终点分别表示实际 prepared 和返回机器，并证明每态良构且 `resource_safe`；公共 `source_execution` 提取该见证。真实准备路径建立原有条件化 `RunReport` 的输入前提，两段在相同状态接缝处合并，不重复接缝或引入失败事件。

报告区分 `SetupFailed`、`Blocked` 与 `Finished`：准备失败立即停止，保留成功准备前缀，自主 `steps` 为零，不能推出所选 actor 不满足 `step_enabled`；只有全部准备成功后的自主阻塞才保证最终 `!step_enabled`。`setup: Vec<Transition>` 是真实成功准备调用的运行时记录，`steps` 只统计随后自主提交的步骤，包含终态调用但不含准备调用和失败尝试；prepared、自主 outcomes 与源轨迹是擦除的 ghost 数据。这个入口建立成功调用从 empty 出发的存在性，尚未覆盖多个 actor／动态 child 的自主调度、其余准备和恢复域与全局递减量；新 child 仍 Inactive，strict primitive 仍可阻塞，引理 57／定理 73 保持 partial。

[`fresh_preparation.rs`](../crates/cordis-kernel/src/fresh_preparation.rs) 的 `preparation_command` 选取 Insert/Begin/Step，`preparation_enabled` 分别复用 Fresh 的 `insertion_enabled`、`begin_enabled`、`step_enabled`。Insert 包含 Mixed 蓝图索引／合法 bank 前缀与 Kernel 插入检查；Begin 要求已登记、保留 journal 为空及 Kernel Begin 域，包括目标可用和 generation 容量；Step 保留 primitive 与终态发布域。真实 `apply` 对该范围满足成功 iff 调用前谓词，运行分支与错误顺序未改。`run_script` 的失败命令若在此范围，返回机器不满足该命令的谓词；`run_from_empty` 的 SetupFailed 同时对真实 prepared 与返回机器传播此结论。谓词在成功前缀之后的失败处求值，不要求全部命令在初始 empty 状态就使能，成功前缀也可以含其他命令。

Retire/Depart/Unload/Remove 仍受支持；`preparation_enabled` 对它们为 false 只表示不在该证明范围，受 `preparation_command` 限制的等价合同不会据此拒绝它们。Unload 的实际 `apply` 分支另有下文精确域，不改变该准备范围；其余命令和更广 dispatcher 的域、具体错误枚举的逐项对应仍未证明。这些 proof-only 谓词刻画实现域，保留蓝图合法性、有限容量和 strict 值可用性，不等于所有论文已使能准备命令均可被接纳。

Mixed/Fresh 公共 `unload` 现有精确成功合同：`unload_enabled = kernel.cleanup_enabled(actor) && restore_receipts(journal(actor), primitive_state).is_some()`。控制许可和实际完整逆日志的有定义性是独立条件，不能从 `wf()` 或 `!relied` 推出任意逆日志可恢复。`restore_receipts` 在当前 primitive 状态上按 LIFO 解释真实 receipts；内部 `undo_one` 成功 iff 对应 `mixed_grammar::undo` 有定义，成功结果与它相等，失败保持自己的输入，且保持全部 restoring 标志。真实循环在清理期间保持 actor restoring，以实际 journal 长度递减；成功后 `unload_inner` 的结果是完整模型恢复后释放 commitment、进入 Inactive，journal 与当前指令清空。公共包装层给出既有 Unload acknowledgement。

公共 Mixed/Fresh Unload 错误保持完整机器；内部 `unload_inner` 可能已进入清理并执行部分逆操作，不具备相同回滚合同。Child inverse 只退休捕获身份，不删除条目、自动执行 child 清理或回退分配器。`FreshDriver::same_unload_domain` 连接完整 `same` 与定义域相等。这补充引理 57 的实际 inverse 接线、推论 69 的恢复执行证据及定理 73 的局部有限清理；仍不建立一般 foreign replay 观察等价、任意资源物理恢复或动态全局终止。`preparation_command` 范围仍仅 Insert/Begin/Step；实际 `apply` 的 Unload 分支另行给出成功 iff `unload_enabled`。

`unit_child_recovery()` 进一步从真实执行已表示的良构历史，推出每个已登记 actor 的实际 journal 若仅含 `Inverse::Unit`／`Inverse::Child`，则完整 `restore_receipts` 有定义。源 accumulator 与真实 receipt 的对应及 `retained` 给出 captured child 当前仍 registered；这比 `history_sound` 只说明原始落地时 inverse 有定义更强。Unit 恒等操作与 Child 退休都不移除 registry 成员，所以后续 LIFO 位置继续有定义。Mixed/Fresh `run_script` 自动建立此性质，包括错误返回；`run_from_empty` 为 prepared 与最终机器建立它。不新增运行时历史缓冲或恢复实现，也不强化 `wf()`。

在此性质与 `unit_child_journal(actor)` 下，`unit_child_unload_domain` 证明 `unload_enabled(actor) == cleanup_permitted(actor)`，后者就是 Kernel 清理许可；真实公共 Unload 因此成功 iff 清理被允许。脚本若在此类 journal 的 Unload 处失败，返回机器不满足清理许可。该结论只涉及实际停止状态，不刻画具体错误枚举。Child 退休不等于 Remove，不运行 child 清理；父子所有权也不是隐式服务依赖。Provision/Xor 等非平凡 Table inverse 仍可能因 strict 状态检查失败；Unit 本身在源模型中表示为 `Table(Unit)`，分类依据是实际 receipt。这连接定义 52 的名称保留与受限 inverse 执行，补引理 57／定理 73 的局部义务，但不建立推论 69 的一般 foreign replay 方程、owner 表空或全局进展；partial 状态保持。

`lifecycle_ordering` 从实际九规则 trace 证明 episode 边界、固定 committed、provider 整个表域保持和严格 episode 排序；Loading 只占唯一初始区间，Iter／Finish 使用 opening committed。`grammar_ordering` 将值变化接到精确 key/provider 的实际 Operation 或 LIFO inverse，并可从空 history 回溯到先前 landing。`rule_frames` 证明冻结状态映射／字段修改分解及 metadata lifetime。`indexed_ordering` 和 `mixed_ordering` 进一步覆盖同一 arbitrary-index dependent／child 执行；观察版本不要求 primitive 字面恢复，真实 LIFO 保留 child retirement 的中间状态，并追到原始 operation landing。`observational_execution` 从真实 Begin／成功 Unload 推导观察恢复及 owner 空表，仍要求 identity-extended scalar generators 观察交换。这个接口与一般 strict-partial coeffect 的对应、可执行混合程序模拟及异步宿主仍须额外证明；有限前缀不保证最终发生 Unload。

`isolated_deletion` 构造受限 owner 的删减后生命周期前缀，保留注册条目、外部编排与真实 foreign journals；它不允许 owner 的 dependencies 或 Child landing，并要求声明接口分离。`strict_journal` 的严格 partial 事件恢复可以推导 inverse 成功域，但任意 foreign Unload 及实际 continuation 重演尚须另证。`causal_normalization` 保留完整外部输入并终止于没有可用局部交换的轨迹；名称或 captured-child 读取可能阻止前移，因此不主张编排优先顺序或一般 confluence。

## 实际使用的已验证 cleanup 栈

[effects.rs](../crates/cordis-kernel/src/effects.rs) 提供 `EffectStack`，其私有 `Vec<usize>` 与公开的 closed `view: Seq<usize>` 对应。它是 Rust 外层真实使用的 cleanup token 容器，不是另写一份仅供验证的模型。

- `new` 的后置条件是空序列。
- `push(token)` 精确得到旧序列追加 token，长度增加 1。
- 非空 `pop` 精确返回旧序列的最后一项，并将状态变为完整旧前缀，长度减少 1；空 `pop` 返回 None 且不改变状态。
- `len`、`is_empty` 的返回值与 spec 序列精确对应。

该模块单独使用锁定工具链的 `--no-cheating --compile` 检查得到 **5 verified, 0 errors**，没有 `assume`、`external_body` 或跳过的 callback 实现。集成验证以整个内核的最新运行结果为准。

Rust 外层把 callback 存为 `Vec<Option<CleanupAction>>`，每个效果组使用一个已验证 `StageProtocol`，内部以 `EffectStack` 登记 callback token；清理时按 pop 顺序取得 callback，等待当前 inverse 完成后才取组内下一个。独立效果组可以同时 Pending，恢复前先等该 episode 所有在途初始化 stage 落地。`StageProtocol` 证明新 stage 的 target admission、在途 stage 的落地资格和 inverse 入栈，以及 settled 前禁止 pop。token 到 callback 的映射、索引不重复以及 future 的 poll 是普通 Rust 协议，以外层测试检查。`EffectStack` 本身允许重复 token，保证的是每次 pop 取走最后一次登记的一项，不证明每个整数值只能出现一次。也不证明取出的 callback 是有效 inverse、一定完成或不会 panic。

## 可逆资源与效果代数

[resources.rs](../crates/cordis-kernel/src/resources.rs) 是实际可执行的 `Store`。每个整数单元记录 value、owner 和嵌套 depth；同一 owner 可继续写入，其他 owner 的冲突写入被拒绝。成功写入返回不可复制、字段私有的 `Inverse`；undo 必须匹配当前 post-state，恢复确切的 prior cell，保持所有其它单元不变。失败时原状态不变并返回 inverse，允许在正确顺序下重试。`round_trip` 同时执行并证明一次完整的 write/undo 恢复初态。`recovery` 证明恢复本单元时保留其它单元的变化，`independent_updates` 证明不同单元的写入与 inverse 可交换。

普通 Rust 的 `ReversibleStore/Transaction` 用 Mutex 和唯一 transaction owner 包装它，并通过 `Setup::reversible` 自动登记 LIFO rollback。这个资源后端的 primitive 是已验证实现；该 host transaction 的 journal 编排、锁和 adapter 仍通过测试检查。另提供已验证的独占 `history::Journal`，拥有自己的 store 与 witness 历史，证明部分及完整恢复；它不自动替代允许多个 transaction 共享 store 的宿主接口。独立 `Transaction` 需要显式 rollback，Drop 不自动恢复。原始 `Store::undo` 的契约基于匹配的 cell post-state；调用者应把 inverse 交回产生它的 Store，宿主包装层负责保留该 store。不能用这个受控整数存储的证明来推断磁盘、网络或任意 callback 的正确性。

[calculus.rs](../crates/cordis-kernel/src/calculus.rs) 对任意状态类型和显式提供的纯效果函数证明有限序列的组合规律：

| 证明 | 前提与结论 |
| --- | --- |
| `recover_sequence` | 给定观察等价关系、每个 forward/inverse witness，且 inverse 保持该关系，逆序恢复后的状态与初态等价 |
| `inverse_commutes_with_trace` / `recovery_with_interference` | inverse 与每个 foreign step 交换时，可以删除本 episode 而保留 foreign trace |
| `recover_interleaved` | 对每个 local stage 与 foreign stage 交错的有限序列，在 inverse witness 和交叉交换条件下，清理后恰好保留原顺序的 foreign trace |
| `independent_groups` | 两组有限效果逐对交换时，整组的先后执行结果相同 |

前提是接口要求，不是对 arbitrary Rust callback 使用 `assume`。这些定理验证恢复与交换的代数核心；它们没有自动把外部效果、iterator continuation、服务发布与整个异步 runtime 映射到论文历史。`iterator_independence` 已完整形式化 Definition 42 的 quotient continuation 与 inverse 稳定性，并证明 generator 判据；每个具体效果实现仍须提供满足这些条件的 witness。

## 当前没有声称的证明

| 结论 | 仍需建立的内容 |
| --- | --- |
| 任意 callback 都能恢复自己的外部副作用 | callback 的 inverse witness、异常/取消边界、资源是否全部经 context 登记 |
| 效果恢复等于物理世界完全回滚 | 论文只在 key operations 定义的观察等价下恢复；消息、磁盘外部状态、allocator 历史需各自边界 |
| Theorem 68 / Corollary 69 在完整宿主上的 recovery exactness | 已从真实 mixed grammar 的 Begin／Unload 推导恢复，无需 caller episode profile；仍要求显式 identity-extension scalar 交换，尚缺一般观察范围及宿主历史 refinement |
| Theorem 73 的完整进展和终止 | 已证明有 provider rank 的非静止控制状态存在下一步，并提升为完整规则的 landing witness；固定 registry 的实际轨迹已导出计数前提并可构造完整规则执行到 quiet；单 actor Fresh 循环已对含 child 注册的真实执行给出有限返回界；整个动态 child 图的自治进展、无限 orchestration、future 最终完成与 scheduler 契约仍在边界外 |
| Theorem 80 的完整 confluence | 已证明动态独立 family confluence、静止控制唯一及实际固定程序轨迹的完整终态唯一；已具备 full-rule name-renaming、fresh allocation 匹配及条件 suffix 删除；仍需一般动态 child lifecycle 的合法前缀删除、交换和观察 canonical form |
| JS Cordis 或完整 DeepSeek Harness 已验证 | 还需完整 API、宿主运行时、插件生态与应用逻辑的实现及证明 |

独立性不只是两个 forward 操作交换：Definition 42 同时约束 forward、inverse 的交换，以及彼此不改变 yielded inverse 和 continuation（pp27–28，text:1174–1192）。仅有 LIFO 栈不能推出这个条件。LIFO 负责单个效果序列的恢复顺序；跨组件可交换性是另一个证明义务。

cooperative async 表示外层可把清理推迟到未来的 poll/step 完成，内核在此期间保留绑定。它不自动意味着任意 Tokio future、并发执行、取消、panic 或永不完成的 callback 都已覆盖。Failure latch 对应 §4.4：初始化失败先恢复已有成功效果，失败状态抑制自动重试；显式 revision 用新 fiber 重试。带失败的执行不主张论文 confluence（p56，text:2647–2664）。
实际 `Runtime::restart` 另提供同 ID 的显式重试扩展。Cleanup callback 返回 Err 时，外层记录错误并继续余下 cleanup，最终释放注册的服务；Err 不能作为逆操作成功恢复物理资源的证据。`Runtime::get` 返回的宿主 Arc 不会自动建立 committed link，其外部持有者不受依赖守卫保护。证明保护的是框架内已记录绑定，并非所有可能持有服务值的外部代码。

基础 cleanup 注册构成一个 LIFO 组；每次 `ctx.effect` 创建独立的组，组间恢复允许并发。任意 callback 相互等待仍可能不终止。child 继承 parent 的 dependencies，并在内核中记录实际绑定；派生 realm 还增加相应的新端口绑定，不能只复制 payload 绕过 lifetime guard。可访问自身 provision 与显式/继承 dependency；Rust typed context 与 scope builder 不模拟 JS Proxy。

## 普通 Rust 事件、Timer 与 Loader

[events.rs](../crates/cordis/src/events.rs) 提供 typed `Event<T, R>`、`AsyncEvent`、同步/异步 waterfall、on/once/off/emit、parallel all-settled、serial、bail、prepend、自定义 filter，以及 Global 和按完整 `(key, realm)` 比较的 Relevant scope。subscription 的 dispose 可登记到 setup cleanup，令 listener 随 owner 生命周期撤销。Drop subscription 本身不会退订。

这些事件操作、Mutex/atomic 同步和 callback 均不在 Verus 证明边界中。行为测试检查注册顺序、snapshot 规则、重入与并发 once claim、bail 停止条件、scope 过滤和 owner cleanup。事件 dispatch 会先取得 snapshot，再解锁执行 callback；普通 listener 在 snapshot 后被移除，仍可执行这一次。once 在执行前 claim；bail 遇到第一个 Some 就停止，包括 Some(false)，不使用 JS truthiness。AsyncEvent 的 factory/poll panic 聚合为错误；同步 dispatch 和 waterfall 的用户 panic 传播。异步事件必须 await；丢弃 dispatch future 会丢弃其 pending listener futures。单纯退订不等待已经 snapshot 的 callback/future，其生命周期不能由 kernel provider guard 自动推导。

[timer.rs](../crates/cordis/src/timer.rs) 提供单工作线程或手动时钟、timeout/interval、sleep/ticks、debounce/throttle。owner 绑定在 setup 中登记 cleanup，外部 shutdown 等待在途 callback；同一 timer service 内的 callback 发起 shutdown 时只发出取消，避免彼此 join。interval 使用 fixed-delay，不补发过去的 tick。sleep/ticks 观察 owner 取消，使初始化等待 timer 时可以退出。

[loader.md](loader.md) 说明配置树、schema/default、metadata/interception、Include、文件 polling、factory revision 和原地更新。配置先验证再变更；替换用 fresh ID，提交前的失败/取消保留可恢复事务和旧 factory。原地更新先登记补偿计划，提交后的依赖传播错误通过 PostCommit 单独报告，不伪装为已恢复旧配置。动态服务通过有显式 owner anchor 依赖的子 provider 表达，服务检查是额外的宿主 activation 守卫；共享 payload 槽保持 committed provider 身份。[外部插件](process-plugins.md) 的 JSON-RPC、代码快照、文件 I/O、回滚编排和任意 callback 都属于普通 Rust，不能由内核证明替代。

## 保持语义的历史回收

`compact_bindings` 的后置条件保持 nodes/declarations、全部 live bindings 和 wf，并将 links 精确替换为原序列按 live 条件的稳定 filter。`compact_declarations` 精确保留仍注册 owner 的声明，同样保持节点、原绑定和全部注册接口。stable filter 保留相对顺序，不会改变 target/committed 构造顺序或先前已证明的严格依赖登记顺序。已删除 identity slot 不回收、不复用。

Runtime 自动维护、snapshot、shutdown、事件 owner drain 和 JSON persistence 的编排仍属于普通 Rust 宿主层；新增功能没有扩大任意 callback 和外部文件系统的 Verus 证明边界。详情见 [diagnostics.md](diagnostics.md)、[events.md](events.md)、[loader.md](loader.md)。

## 整篇覆盖与完成门槛

新增的代数、观察测试、最大 iterator bisimulation、key-local coeffect、full-rule preservation、名称双射、动态调度和固定程序执行的准确范围见 [refinement](refinement.md)。所有 81 个编号条目统一登记在 [覆盖表](paper-coverage.md)，完成检查使用 `scripts/check-paper-coverage.py --require-complete`。源码验证通过只说明被编码的契约成立；不能将该检查替换成整篇声明，或删除被反驳的原文条目来消除缺口。

`mixed_observational_transport` 已证明共享 Iter 交换之后的九规则有限后缀对应，实际 inverse 域和历史 token 关系由局部接口导出。`foreign_unload` 还从实际新建的操作 receipt 推导 foreign inverse 的局部反向见证及 owner 最终严格恢复；这不等于已经构造含 foreign Unload 的完整删后生命周期轨迹。`fresh_grammar` 形式化固定 fresh-child binder 及过去历史的名称支持，外部命令中对出生名称的引用需要同步运输。


`mixed_driver::fresh::admitted` 已把单个已准入阶段的跨调用协议接到真实落地：会话拥有
机器，捕获 generation／pc／模板，目标失配后仍执行原动作并登记 inverse，再线性化为
landing Divert。`admitted::script::run_script` 从 empty 构造同一程序的完整源历史，
明确区分 Call／Land 与 Admit／Release 元数据步骤，并证明事件完整性和输入顺序。
失败或旧准入不改变机器；这补齐该闭合语言的两阶段模拟，仍不证明任意 future 或
callback 的内部效果，也不替代普通 Rust Runtime 的多组异步 scheduler。

该协议还给出精确成功域：`FreshDriver::admit` 在且仅在 `admission_enabled = ready` 时成功；票据接纳不预留值或端口。成功接纳还保证返回票据的 `land_enabled` 等于调用前机器的 `step_enabled(actor)`，所以无中间操作的立即落地与同步 step 接纳域一致，但较弱的 `ready` 本身并不保证落地成功。`Admission::selected_instruction` 保持捕获模板，并在落地时以当前 `next_id` 实例化 Child。`land` 在且仅在 `land_enabled` 时成功：未消费、当前机器仍满足捕获身份的 `bound`、实际 primitive 域有效，且仅 coherent 终态需满足 `complete_after`。目标丢失时可在不完整发布的情况下执行真实 primitive、记录 inverse 并 Divert，但值缺失或 child 冲突仍会拒绝。成功结果的 `diverted` 恰好等于调用前不 coherent，返回 child 使用落地前的 next ID；`commit_divert` 在原前提下保证成功。错误保持完整机器、票据身份与 consumed，未消费票据可在解除冲突后重试；stale／重复落地仍被拒绝。这是跨调用的局部定义域证明，不是任意 Future 最终返回或整段动态执行终止。


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

后续 `internal_old_unload` 已处理固定 registry 中任意位置的旧／混合 Unit／Operation
回执卸载，并从真实交错步骤推导目标执行及最终 owner 恢复。另一个
`old_provision_journal` 定理处理末端含旧 Provision 的任意长度 Table 栈，证明删键
定义域和最后两端闭合。`generalized_table_deletion` 现已统一任意位置、任意年龄的
Table 清理及新 foreign Provision：其目标成功来自真实 source 与归纳 batch，
不是额外假设。它仍要求固定 registry、初始 owner Inactive／空表及私有 provision
分离；不含 Child、owner 消费者与内部 owner Unload，详见 refinement 的精确前提。

`interface_observation` 以实际 forward 和返回 inverse 的接口外 frame，将局部
表函数关系提升至全键关系，覆盖 total/strict partial 及完整 continuation/witness。
这不将 table 观察等同于控制字段相同，也不自动建立 Child 的强见证。
Definition 23 的 location heap realization 已形式化；宿主别名和回调仍有独立边界。


`dependent_independence` 已将完整 strict grammar independence 从 nat 示例推广至
任意、不相关的 I/J，并保留不同库的实际 outcome/continuation、所有 reach generators
和整个 monoid。它仍以 foreign 调用实际成功作为 yield 稳定性的守卫；没有用失败汇点
或 identity 补全替代原部分操作，也没有宣称原 total Theorem 47 无条件成立。


`dynamic_table_deletion` 已解除 Table 删除的固定注册表限制：真实 foreign
Insert/Remove、任意年龄 Table 清理和新 Provision 参与同一执行归纳。初始分离及
每次 Insert 的 dependency 条件导出逐前缀分离；目标步骤、实际 inverse 成功与
最后 owner Unload 都是结论。被移除 actor 的旧 entry 保留原始 input 和真实
receipt；示例覆盖其 +7、Unload、Remove 和最终 owner 恢复。owner Child、foreign
Child journal、owner 消费者与内部 owner Unload 仍不属于此 profile。


`strict_partial_quotient` 将真实 partial `run` / `restore` 用于九规则配置模拟，
允许不同 root/current 索引、history 和 inverse 栈长。实际调用与撤销域、目标执行
及每个前缀的良构性是结论；最小 dependent grammar 提供自相关，PER 证明不假设
全对象自反。其输入关系限制在 control 相同的合法注册状态和逐 provider 表域，
比原文纯 table 观察更强；当前只覆盖 Table 指令及 receipts，不声称完整 Lemma 60。


Definition 48 与 58 已有参数化原文定义：`paper_components` 保留最小且全域的
组件 witness 与安装范围；`paper_observations` 保留任意索引、实际 G→G 函数字段、
全 registry 观察、有限／无限执行与 episode。`formalized` 记录这些条件式定义，
不表示已构造递归 Γ 或证明所有严格解释器属于原文组件空间。55 的精确读域歧义、
56 的 total lift 含义、57／60 的完整实例证明仍单列。


Definition 52 的 typed 原语在给定 registry/editor 解释下已编码：完整 Component
输入门、fresh name、真实插入和捕获同名 retirement 均有契约。每键值域另由
`paper_typed_context` 约束所有上下文输入。严格的 missing-child 失败及未来 retention
与原全域 iterator witness 的差别继续保留；52 的状态不代表 57 已证明。


受限 episode deletion 现已组合 foreign Child 与任意年龄的混合 Table／Child
撤销栈，并保留动态 Insert／Remove。真实目标执行及最终 owner recovery 被构造
出来；owner 的 Table／私有提供项约束及原文 Component 表示缺口仍保留。
