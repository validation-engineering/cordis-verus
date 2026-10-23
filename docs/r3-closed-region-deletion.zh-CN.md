# R3：关联删除 Child 与 consumer 的执行

[English](r3-closed-region-deletion.md) · [私有 Episode 删除](r3-script-deletion.zh-CN.md) · [论文 refinement 里程碑](paper-refinement-roadmap.zh-CN.md)

native 中间截面的完整 publication／owner／pending 观察与恢复现见[第 2 包](r3-observation-recovery.zh-CN.md)。下文相关边界说明限定于本页较早的入口；普通宿主迁移已由第 3 包完成，完整效果上的一般合法删除仍未完成。

Mixed 和 Fresh 脚本报告现提供 `delete_closed_region` 证明查询，使用 Episode 恢复所用的
**同一份真实来源见证**构造合法剩余执行。当相关 Episode 和名称形成闭合区域时，允许
owner 创建 Child，也允许其 publication 被实际 Active consumer 使用。

这是有限执行上的有条件删除结果。R3 仍在进行中。

## 构造器做什么

`Region` 选择需要删除激活的所有者，以及需要消除注册的名称。后者包含被删除的 Child
出生，且必须属于前者。对仍保留注册的选中所有者，保留 Insert、Retire、Remove，省略
激活与清理步骤；投影状态是 Inactive，表和逆操作栈为空。被消除名称的全部步骤都省略。
未选中所有者的每一步都按来源顺序保留。

来源条件检查：

| 来源事实 | 必要原因 |
| --- | --- |
| 保留注册不引用被消除的 parent | 剩余插入仍有合法父节点 |
| 每个来源状态中，未选中所有者的依赖声明避开选中所有者的 provision | 剩余 Begin 和一致性检查不会失去 provider |
| 实际表操作收据捕获的 provider 与操作所有者位于区域同侧 | 删除内部操作不会改变外部调用的输入 |
| 选中所有者的 Child 收据捕获被消除名称，保留所有者的 Child 收据不捕获它 | 出生删除与逆操作保留必须一致 |
| 闭合观察时，选中且仍注册的所有者已 Inactive，被消除且仍注册的名称已 retired | 同一真实 provision 历史可推出其表为空 |

这些条件只检查原执行和捕获收据，不要求目标执行成功、期望堆相等或目标逆操作成功。
内部 consumer 可以读写 owner 的 publication；它们需要一并纳入选中区域。

## 与运行代码的连接

两个实际脚本运行器已有擦除的 `recovery_history_witness`。新查询使用该见证，构造目标，
并证明目标的每一步合法。检查错误返回也可以使用真实成功前缀；端点观察相等还需要满足
上述闭合条件。

保留调用使用自身的目标输入重新解释，证明其原始结果、续体和偏逆操作一致。历史索引
经过压缩，每份保留逆操作仍对应真实来源中的原收据。目标恢复成功由这些原语规律和
实际来源恢复推出，不是调用方提供的结论前提。

Fresh 保留**每次保留落地的实际分配选择**，以及 binder 返回的 root 和续体。证明只在
该次落地实例化节点，不把所有激活编码成同一个固定名称的 Mixed 程序。

语义见证仍在编译时擦除。下述可选命令准备 API 从现有报告分配有限名称映射及新命令计划；
不增加 Node 依赖，也不提供替代原语实现。

## 非空证明案例

案例使用实际 Mixed 驱动的值操作库：

1. Owner 0 发布服务，随后创建 Child 2。
2. 独立 provider 1 在 owner 的步骤之间发布另一项服务。
3. Child 2 提交对 owner 0 的依赖，并实际对其服务执行 XOR；外部 consumer 3 也提交
   对 owner 0 的依赖并进入 Active。
4. Owner 0 离开。证明 consumer 仍依赖它时 Unload 不合法；两个 consumer 分别卸载，
   Child 的原始逆操作恢复值。
5. Owner 0 卸载，退休 Child 并撤销 publication。Provider 1 使用自身原始逆操作卸载，
   然后 Child 2 被移除。

23 个来源转换构造出 **9 个合法剩余转换**。5 份来源收据压缩为 1 份保留收据：来源
索引 1 对应目标索引 0。目标保留 provider 1 的实际发布和 Unload。遗漏任一 consumer，
或者忘记处理被删除的 Child 出生，都会被来源条件正式拒绝。

## 可执行的名称映射

Fresh 报告现在还提供 `compact(keep)`。掩码按来源顺序选择成功转换；返回计划包含
双向名称映射、重命名后的转换及分配上界。`commands()` 生成已有 `fresh::run_script`
可以接收的命令：

```rust,ignore
let source = fresh::run_script(blueprints(), &commands);
let plan = source.compact(&keep)?;
let replay = fresh::run_script(blueprints(), &plan.commands());
```

来源和重放使用同一套 blueprint。由 `Region` 生成的掩码按上文规则保留
Insert／Retire／Remove，不能简单按 actor 全部删除。错误报告只处理实际成功前缀，
不隐式重试失败命令。

代码与证明连接了这些事实：

- 实际 Insert／Child 成功时分配原上界并将其加一。失败命令不消耗名称，Remove 不会
  重置上界。真实脚本在构造语义见证的同时建立这份分配历史。
- 每个来源 Insert 将真实 parent 和 blueprint 绑定到同一见证；只记录生命周期标签
  无法保留这两个命令参数。
- 可执行有限置换按来源顺序将保留出生映射到 `0, 1, ...`，同步重命名 actor、插入的
  parent 和 Child 结果。保留后又被 Remove 的名称仍然消耗 ID；原分配前缀之外的名称
  保持不变。构造时间和空间为 O(已分配名称数 + 转换数)，名称查询为常数时间。
- 合法剩余执行能推出每个命令都有更早的保留创建来源。因此闭合区域的来源条件足以
  保证**真实构造器成功**，不需要调用方另外假设目标轨迹或创建来源成立。错误的出生记录及
  缺少保留创建来源的引用会返回检查错误。
- `Plan::source_execution` 为**实际返回计划**构造合法轨迹，包含 Insert 参数、压缩后
  的 Child 选择及重命名后的原始逆收据。安装的 Fresh 程序族不变，服务键和值不变；
  满足收尾条件时保持同一服务表观察。

对满足闭合区域条件的来源，真实 `run_script` 现在能完整执行压缩命令，返回与计划
完全相同的记录，并逐步表示构造出的后继状态。`Plan::replay_result` 将实际结果连接到
原始来源；满足收尾条件时，服务表观察相同。原始 `compact` 只检查分配／引用一致性，
任意 keep 掩码返回 `Ok` 不等于满足语义上的闭合区域条件。该结果限于同步 Fresh
驱动；Mixed 固定 `expected` 数字的指令仍需代码迁移。

运行回归包含 owner／Child／consumer 清理、保留的 publication 与 Unload、parent
发生变化的后续 Insert、两次后续 Child 创建、保留后移除的名称，以及来源末尾的一次
检查失败。**39 个成功来源转换生成 25 个计划转换**，通过原公开驱动重放后，每条记录
都与计划一致，仍存活的服务值为 `99`。另一用例拒绝遗漏来源、掩码长度错误、重复出生
及越界出生，同时保持来源报告不变。这些用例检验实现，不替代一般证明。

## 从源规则到可执行命令

Fresh 分派器现在为**全部七类命令**公开精确输入域：`apply` 成功当且仅当调用前
`command_enabled` 成立。遇到检查错误时，`run_script` 保留真实成功前缀，并保证
返回机器中的下一条命令确实未使能。证明包含已有事务回滚行为，没有修改运行检查顺序。

源见证现在保留了仅靠论文轨迹合法性不能推出的实际运行信息：Active 服务表完整、
安装的 root 蓝图及其精确声明、合法代码前缀，以及没有重复项的声明数组。真实命令维护
这些事实，闭合区域删除与名称重命名在 `Plan::source_execution` 中保留它们。
这一区别很关键：一般论文关系允许某些不完整发布的 Finish，而当前可执行 profile
会拒绝这些调用。

`source_command_admission` 将已表示的合法源调用连接到真实 `apply` 输入域：

| 命令 | 与实际检查的对应 |
| --- | --- |
| Insert | 源 parent／预留守卫、安装的蓝图信息，以及有限分配容量 |
| Begin | 源目标可用性、Inactive 空日志，以及 generation 容量 |
| Step | 实际 Unit／Provide／Xor／Child 求值；保留的运行形状提供终态完整发布和 Child 声明去重事实 |
| Retire／Depart | 登记、phase 和目标 coherence 守卫 |
| Unload | 同一批原始逆操作、依赖守卫和空闲清理事务 |
| Remove | 已退休、Inactive、空表、没有已登记的所有权子对象，也没有保留的 Child 逆操作 |

Remove 的连接还使用实际不变式：Inactive 和已移除的行均没有逆操作日志。
`new`、各真实命令和脚本循环维护这个不变式，因此扫描历史行不会产生论文当前
accumulator 之外的隐藏引用。退休与从注册表移除仍然是不同动作。

单命令结果现已组合为**整段有限脚本完备性**。前提是从 empty 出发的源执行，保留
安装的运行形状、真实 Insert 参数、连续分配历史和同步离开分支。原来的 `run_script`
建立 `ScriptReport::replays`：满足上述条件且对应输入命令的源执行，其记录与最终状态
都与实际返回结果一致，报告没有检查错误。

这里补齐了三段连接：

- `exact_successor` 同时确定真实返回的转换及精确后继。源语义的 Divert 还允许已准入
  的在途效果落地；同步 `Depart` 则保持日志／历史不变。真实见证记录这一事实，删除与
  重命名保持它；独立的已准入落地 API 仍保留自己的合同。
- Kernel 合同跟踪真实 generation 和 restoring 字段，覆盖 Insert、Begin、原语执行
  及逆序清理。命令边界不遗留清理锁，每个 generation 不超过已执行命令数；下一步调用前，
  输入切片长度可推出 generation 和分配容量。不新增运行计数器。
- 原执行循环用擦除的证明状态保持精确目标前缀，因此合法的下一条源调用不能进入检查错误
  分支。证明不假设可执行重放成功，也不引入第二套解释器或运行时轨迹存储。

新增运行用例保留 Loading／Divert，恢复原 provider 的效果，移除旧 provider，然后在
Child 压缩后让同一个 consumer 绑定新 provider 重复激活。**26 个源转换压缩为 21 个**，
记录逐条一致，最终服务值保持为 `8`。

## 审查路径

| 义务 | 代码 |
| --- | --- |
| 来源闭包、原语读写范围、真实逆操作迁移 | [closed_region_deletion.rs](../crates/cordis-kernel/src/closed_region_deletion.rs)：`closed`、`local`、`run`、`restore` |
| 完整生命周期转换 | [closed_region_deletion/execution.rs](../crates/cordis-kernel/src/closed_region_deletion/execution.rs)：`step` |
| 执行构造及闭合观察 | [closed_region_deletion/trace.rs](../crates/cordis-kernel/src/closed_region_deletion/trace.rs)：`from_source`、`closing_observation` |
| Fresh 实际选择与轨迹构造 | [closed_region_deletion/fresh.rs](../crates/cordis-kernel/src/closed_region_deletion/fresh.rs)、[closed_region_deletion/fresh_trace.rs](../crates/cordis-kernel/src/closed_region_deletion/fresh_trace.rs) |
| 实际 Mixed／Fresh 报告查询 | [mixed_driver/deletion.rs](../crates/cordis-kernel/src/mixed_driver/deletion.rs)、[mixed_driver/fresh/deletion.rs](../crates/cordis-kernel/src/mixed_driver/fresh/deletion.rs)：`delete_closed_region` |
| 实际分配历史及 Insert 参数 | [mixed_driver/fresh/allocation.rs](../crates/cordis-kernel/src/mixed_driver/fresh/allocation.rs)、[mixed_driver/fresh.rs](../crates/cordis-kernel/src/mixed_driver/fresh.rs)：`run_script` |
| 可执行名称映射与命令准备 | [mixed_driver/fresh/names.rs](../crates/cordis-kernel/src/mixed_driver/fresh/names.rs)：`pair`；[mixed_driver/fresh/compaction.rs](../crates/cordis-kernel/src/mixed_driver/fresh/compaction.rs)：`compact`、`commands` |
| 从来源推出创建完整性及计划轨迹 | [mixed_driver/fresh/compaction/execution_origins.rs](../crates/cordis-kernel/src/mixed_driver/fresh/compaction/execution_origins.rs)：`from_region`；[mixed_driver/fresh/compaction/source.rs](../crates/cordis-kernel/src/mixed_driver/fresh/compaction/source.rs)：`source_execution` |
| 真实分派输入域与空闲日志 | [mixed_driver/fresh.rs](../crates/cordis-kernel/src/mixed_driver/fresh.rs)：`apply`、`run_script`；[mixed_driver/fresh/dispatch.rs](../crates/cordis-kernel/src/mixed_driver/fresh/dispatch.rs)：`command_enabled` |
| 源调用到实际准入 | [mixed_driver/fresh/dispatch/source.rs](../crates/cordis-kernel/src/mixed_driver/fresh/dispatch/source.rs)：`source_command_admission`；[mixed_driver/fresh/dispatch/forward.rs](../crates/cordis-kernel/src/mixed_driver/fresh/dispatch/forward.rs) |
| 真实运行形状及压缩保持 | [mixed_driver/fresh/dispatch/shape.rs](../crates/cordis-kernel/src/mixed_driver/fresh/dispatch/shape.rs)：`source_runtime_shape`、`deleted_trace`、`renamed_trace` |
| 精确后继与同步分支传递 | [mixed_driver/fresh/dispatch/exact.rs](../crates/cordis-kernel/src/mixed_driver/fresh/dispatch/exact.rs)：`unique`、`exact_successor`；[mixed_driver/fresh/dispatch/exact/transport.rs](../crates/cordis-kernel/src/mixed_driver/fresh/dispatch/exact/transport.rs) |
| 实际有限机器元数据 | [lib.rs](../crates/cordis-kernel/src/lib.rs)：`synchronous_metadata`；[mixed_driver/fresh/dispatch/metadata.rs](../crates/cordis-kernel/src/mixed_driver/fresh/dispatch/metadata.rs)：`metadata_progress`、`metadata_admission` |
| 真实整段脚本完备性与计划结果 | [mixed_driver/fresh/replay.rs](../crates/cordis-kernel/src/mixed_driver/fresh/replay.rs)：`source_call_at`、`unique_path`、`replays`；[mixed_driver/fresh/compaction/source.rs](../crates/cordis-kernel/src/mixed_driver/fresh/compaction/source.rs)：`replay_result` |
| 真实重放回归 | [mixed_driver/fresh/compaction.rs](../crates/cordis-kernel/tests/fresh_compaction.rs) |
| 非空客户端及不完整区域的拒绝 | [closed_region_deletion/example.rs](../crates/cordis-kernel/src/closed_region_deletion/example.rs)：`nonempty`、`source_guards` |

这是对应引理 79 的一类可接受构造。已有单 Episode 值恢复定理仍承担式 (55)/(56) 的
对应；删除闭合的一组 Episode 不能替代无条件的单 owner 删除定理，也不改变原论文
条目的 partial／refuted 审计结论。

## 剩余边界与验收

- 选中所有者在提供的空起点历史中保持固定。区域内允许重复 Episode；只选取复用身份的
  某一代，需要更细的 Episode 索引构造。
- 不允许跨区域写入。此前私有 Episode 删除支持的共享外部表效果，尚未与本构造组合。
- 上述同步 Fresh profile 的整段可执行重放已覆盖。Mixed 固定名称代码迁移与已准入异步
  落地迁移仍待完成；结果不包含公平调度或任意回调保证。
- 普通 Runtime／Node 接入、宿主自动产生完整历史覆盖，以及中间切点的一般
  publication／pending 恢复仍待完成。
- 运行验收包括上述三个 Fresh 压缩案例及 consumer 重复激活。仍待更广的 Mixed／Fresh
  集成、完整故障演示，以及错误保留 consumer、丢失 Child 来源、替换原逆操作、将普通
  Divert 换成落地分支或丢弃计数器／清理元数据连接的证明变异负控。

最终源码通过 **382 项定向 Verus 检查，0 个错误**，覆盖根内核、Mixed 驱动模块和
完整 Fresh 子模块树。使用固定验证器、`--no-cheating`，并编译被验证的可执行源码；
这不是整个 crate 或整篇论文的验收结果。

六组选定运行回归共 **60 项通过**，包含全部三个压缩重放案例。内核全目标／功能的
Clippy（警告视为错误）、格式、论文映射／覆盖／审查一致性及 **563 个本地文档链接**
检查通过。完整开发验收和完整负控仍为**未运行**；R3 按上述边界保持进行中。

```sh
source scripts/toolchain-env.sh
./scripts/verify.sh --verify-root --verify-only-module mixed_driver --verify-module mixed_driver::fresh \
  --num-threads 2 --triggers-mode silent --output-json
CARGO_INCREMENTAL=0 cargo test -p cordis-kernel --test fresh_driver --test fresh_compaction \
  --test fresh_bootstrap --test mixed_driver --test lifecycle --test ownership --locked --offline
CARGO_INCREMENTAL=0 cargo clippy -p cordis-kernel --all-targets --all-features \
  --locked --offline -- -D warnings
python3 scripts/check-paper-refinement.py
```

[原生 Episode 区间删除](r3-native-deletion.zh-CN.md)现支持实际 native 生命周期／publication／owner 投影的中间区间准确接合。它与本文 Mixed/Fresh 整 region 定理独立，不代表共享效果或可执行生产转换已完成。
