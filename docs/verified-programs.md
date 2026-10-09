# 固定程序执行与完整规则桥接

`cordis_kernel::program::ProgramDriver` 提供可执行且经过 Verus 验证的有限组件语言。构造时固定代码、初始 cells、owner、依赖和 provision 布局；之后每一步从代码与当前 cells 计算结果，调用者不能传入不同的写入值或 continuation。

```rust
use cordis_kernel::program::{Instruction, LandOutcome, ProgramDriver};
use cordis_kernel::{Phase, Port};

let mut driver = ProgramDriver::new();
let port = Port { key: 1, realm: 0 };
let id = driver.insert(
    None, vec![], vec![port],
    vec![Instruction::Set { index: 0, value: 42, next: 1 }],
    vec![7], 0,
).unwrap();

driver.begin(id).unwrap();
loop {
    assert!(driver.admit(id).unwrap());
    if driver.land(id).unwrap() == LandOutcome::Terminal { break; }
}
driver.finish(id).unwrap();
assert_eq!(driver.phase(id), Some(Phase::Active));
assert_eq!(driver.read(id, 0), Some(42));

driver.retire(id).unwrap();
driver.depart(id).unwrap();
driver.unload(id).unwrap();
assert_eq!(driver.read(id, 0), Some(7));
driver.remove(id).unwrap();
```

`Set` 写入固定值；`Copy` 读取另一个私有 cell；`BranchWrite` 根据入口 cell 选择值和下一条指令。continuation 必须严格向前且不超过代码长度；constructor 拒绝错误索引和回跳。实际执行契约等于 `interpret`，资源状态与 pc 始终等于同一程序的执行前缀 `prefix`。journal depth 只计入实际指令：depth 大于零时，前一个前缀尚未到达终点，不能把结束后的空轮询计成额外执行。

每个 cell 对应唯一 Port，provisions 数量必须等于初始 cells 数量。depth 为零的 cell 尚未进入抽象服务表。`finish` 检查每个声明 cell 都已经实际写入；若分支跳过某个 provision，返回 `IncompleteProvision`。`Terminal` 表示程序结束，仍须经过完整发布检查。

`admit` 读取真实 Kernel target。`land` 在一个独占可变借用内执行获准阶段并检查当前 target：保持一致时返回 `Advanced` 或 `Terminal`；发生变化时收集真实 inverse，直接进入 Unloading 并返回 `Diverted`。调用者看不到“已落地但尚未确认 diversion”的中间状态。`unload` 检查 provider guard，执行实际 journal 的逆序恢复，再释放 committed；仍有 installed consumer 时拒绝提前恢复。

## 证明连接

[program_refinement.rs](../crates/cordis-kernel/src/program_refinement.rs) 将真实 snapshot 投影为 `semantics::State<Cell>`。只有已经写入的 cells 进入服务表；模型解释同一 code/layout/initial，inverse token 编码 actor 和实际 stage index，undo 对应程序前缀。实现契约给出具体字段关系，桥接定理从这些关系推导完整规则。

| 成功的具体调用 | 完整规则关系 |
| --- | --- |
| insert / retire / remove | O-Insert / O-Retire / O-Remove |
| begin | L-Begin，保存真实 target |
| admit、land 返回 Terminal | 投影不变的行政步骤 |
| land 返回 Advanced | L-Iter，保留真实 continuation 与 inverse |
| land 返回 Diverted | 一次完整 landing L-Divert |
| finish | L-Finish，收集 terminal identity yield |
| depart | L-Leave 或相应 L-Divert 分支 |
| unload | 真实 guard、完整 LIFO restore、L-Unload |

[program_trace.rs](../crates/cordis-kernel/src/program_trace.rs) 的 `driver_trace_refinement` 将任意有限的上述成功调用序列转换为同一个固定 Model 下的合法完整规则 trace，擦除行政步骤并保留两端实际服务值。它从 snapshot 的实际 allocation watermark 推导名称不会复用、代码配置跨历史保持，再由历史构造 `history_catalog`；没有要求调用者预先提供完整 Model、相同历史或完整规则 step。

[program_normal_form.rs](../crates/cordis-kernel/src/program_normal_form.rs) 的 `driver_quiet_confluence` 进一步比较两条实际成功 API 历史。`orchestration` 从 ack 提取带完整配置的 Insert、Retire、Remove，`trace_inputs` 从这些输入计算终态配置；没有把“两个终态配置相同”当作额外前提。初始输入与提取的编排序列相同、两个终态 quiet、终态 provider precedence 有 rank 时，完整投影相等，包括控制 registry、发布的 Cell 值、iterator 和实际 inverse accumulator。证明先用控制正常形唯一性，再从固定代码及最小实际执行深度推导相同服务值和 journal；无需相同调度、相同中间历史或相同终态值前提。

这允许 provider replacement、一次轨迹中 consumer 已完成而另一次在途 diversion、以及无关组件的不同交错。回归 [program_normal_form.rs](../crates/cordis-kernel/tests/program_normal_form.rs) 同时覆盖这些情形和提前跳至程序末尾的分支。该结论属于固定私有 cell 语言，不是任意跨 provider 操作或动态 child 的一般 Theorem 80(2)。

范围是使用 `land` 的成功调用序列。底层公开的 `step` 仍保留以兼容分离式协议，但 target drift 后它需要调用者另行组合 `depart`，不属于这个 trace 定理。失败调用的整条 trace 擦除尚未证明。构造的 Model 只保证这条执行的模拟，不自动满足任意状态上的 `termination::ordinary_model`。语言使用 private provision cells，尚无跨 provider payload 或 child creation 指令；普通 Rust Runtime 的 callback/future 仍有独立证明义务。

回归见 [program.rs](../crates/cordis-kernel/tests/program.rs) 和 [program_trace.rs](../crates/cordis-kernel/tests/program_trace.rs)，覆盖分支、错误程序、在途取消、provider 漂移、原子 Divert、空 journal、未完整发布及移除后的新身份。整篇状态见 [paper-coverage.md](paper-coverage.md)。


## 可执行的混合组件程序

`cordis_kernel::mixed_driver` 提供独立的 `MixedDriver` 和 `run_script`。
它拥有真实 Kernel、全部服务表、不可变蓝图库，以及按发生次序记录的
Unit／Provision／Xor／Child receipt。Xor 沿 episode 的 committed provider
访问实际值；卸载逆序解释捕获的 provider、key 和 child identity。

`Blueprint::new(dependencies, provisions, code)` 构造蓝图数据。插入时的实际
检查要求端口声明正确、pc 向前且在范围内、子蓝图编号小于父蓝图编号。
因此有限 DAG 同时提供最小语法 membership 的归纳秩。代码可以使用：

| 指令 | 行为 | 逆操作 |
| --- | --- | --- |
| `Unit` | 不改服务值并结束 | 不改变状态 |
| `Provide { key, value, next }` | 写入自己的空 provision slot | 移除该值 |
| `Xor { key, mask, next }` | 沿真实 committed provider 修改已有 `u64` | 对捕获的 provider/key 再次 XOR |
| `Child { expected, blueprint, next }` | 创建对应蓝图的子组件并检查实际 fresh ID | 退休捕获的 child |

`Command` 支持 Insert、Begin、Step、Retire、Depart、Unload、Remove。
成功结果 `Transition` 使用对应的枚举变体：`Step { actor, outcome }`
必有实际返回值，`Depart { actor, departure }` 使用 `Departure::Divert`
或 `Departure::Leave`。`actor()` 与 `command()` 提供带验证契约的投影；
调用方可以直接匹配变体，不需要检查彼此独立的可选字段。
`run_script` 返回 `ScriptReport { machine, transitions, error }`；执行在首个
错误停止，`transitions` 只包含已经成功的命令。每次成功都模拟同一个蓝图
库下的实际 `mixed_grammar::step`，源 history 从 empty 构造，包含各次真实
输入、返回 inverse 和 continuation。整段合同无需调用者提供模型、源轨迹
或期望的恢复结果。失败保持完整机器，包括尚未落地的 pc、journal、蓝图和
Kernel generation。

Step 和 Unload 在机器副本上完成，全部检查成功才发布。因此失败中途创建的
child、写入的 payload 和消耗的 ID 都不会泄漏到原机器。这个原子性实现会
复制当前机器，时间和空间代价随已保存数据增长；它是可审查的验证执行路径，
当前没有生产吞吐量保证。

Mixed/Fresh 公共 `unload(actor)` 现在成功 iff `unload_enabled(actor)`：Kernel 的
清理守卫成立，且当前真实 journal 的整段 `restore_receipts` 有定义。清理守卫要求已
登记的 Unloading actor、尚未 restoring 且没有存活 committed dependent；它本身不
保证所有 inverse 都有效。真实代码执行 LIFO 逆操作并最终释放 commitment，循环以
journal 长度递减。`undo_one` 的实际成功域等于对应模型 undo 的定义域，并保持
restoring 标志。一次 inverse 失败保持它自己的输入，但整个内部草稿可能已经执行了
其他 inverses；只有公共事务错误保证完整机器不变。

该谓词只用于证明，不是新增一次运行时预检查。Child inverse 仍是退休捕获的 child，
不删除它或自动运行其清理。`FreshDriver::same_unload_domain` 证明完整 `same` 的机器
有相同定义域。实际 `apply` 的 Unload 分支另有成功 iff `unload_enabled` 的合同，
但没有扩大 `preparation_command` 的 Insert/Begin/Step 范围；也未证明任意良构日志
可恢复、全部历史的 foreign replay 观察等价或全局终止。详见[真实清理定义域](progress-contracts.zh-CN.md#真实-lifo-清理的精确定义域)。
对真实日志还有受限的 `unit_child_recovery()` 结论：每个已登记 actor 若满足
`unit_child_journal(actor)`，即全部 receipts 为 Unit 或 Child，其完整逆序列就有定义。
证明用已表示源状态的 `retained` 得到当前仍登记的 captured child，再利用 Unit 恒等与
Child 退休都保持 registry 成员递归完成。`history_sound` 只保证原始落地时 inverse
有定义，不能替代当前保留事实。Mixed/Fresh `run_script` 从真实成功前缀自动导出该
性质，即使随后命令返回错误也成立；`run_from_empty` 为 prepared 和最终机器建立它。
没有增加运行时 history buffer、恢复算法或 `wf()` 条件。

`unit_child_unload_domain` 在该性质与日志分类下，把 `unload_enabled` 化为
`cleanup_permitted`，即 Kernel 的实际清理守卫。真实 Unload 因而成功 iff 允许清理；
脚本在此类日志的 Unload 处失败，就意味着返回状态不允许清理。Child inverse 仍不
删除身份或执行 child 自身清理，所有权也不构成服务依赖。下述额外源不变式先覆盖
Provision，再覆盖 Xor inverse 的 strict 状态域；Unit 在模型中叫 `Table(Unit)`，范围按实际
receipt 分类。这是定义 52 及引理 57／定理 73 的受限连接，不补齐推论 69 的一般
foreign replay 方程、owner 表空或整个系统终止，相关 partial 状态不变。

进一步的 [`provision_recovery.rs`](../crates/cordis-kernel/src/provision_recovery.rs)
覆盖 `unit_child_provision_journal(actor)`，允许同一真实日志包含 Unit、Child 和
Provision。源 `live_provisions` 由从 empty 的 Mixed/Fresh 执行导出，说明保留的
Provision 对应仍有值的 owner 槽，且同一日志的 Provision key 互异；因此逆序删除
不会提前清空其他保留 receipt 需要的槽。外部 actor 可执行 Xor 修改值，但保持槽有值。
实际 `run_script` 和 `run_from_empty` 的 prepared／最终机器带有 `provision_recovery()`，
包括失败或阻塞返回。`provision_unload_domain` 将该范围内的 Unload 域化为 Kernel
清理守卫，脚本该类 Unload 失败则意味着停止状态不允许清理。证明数据在运行时擦除；
自身含 Xor 的日志由下述更强结论覆盖，一般 foreign replay 仍是独立义务；
Bootstrap 的 SetupFailed 诊断范围也未扩大。详见[Provision 恢复合同](progress-contracts.zh-CN.md#provision-值保留到真实-inverse-执行)。

完整的具体日志由 [`journal_recovery.rs`](../crates/cordis-kernel/src/journal_recovery.rs)
覆盖。源 [`operation_history.rs`](../crates/cordis-kernel/src/operation_history.rs)
导出的 `live_operations` 保证保留 operation 的 captured provider 仍可由 episode
commitment 解析、仍已登记且目标槽有值，并保证较后 Provision 不会删去较早 operation
所需的槽。Provider 退休或 target 漂移不改变捕获身份；依赖守卫阻止过早清理。
自身 Xor 的历史顺序保证先恢复 Xor，再撤销创建其值的 Provision。
`restore_all` 将这些事实与 Provision 唯一性、child retention 组合，证明 Unit、Child、
Provision、Xor 四种实际 receipt 的 LIFO 恢复有定义；具体 `u64` Xor inverse 为全函数。

所有实际 `run_script` 返回及 `run_from_empty` 的 prepared／最终机器都带有
`journal_recovery()`。`journal_unload_domain` 无须日志分类即可将 Unload 域化为
Kernel 清理守卫，脚本 Unload 失败则意味着真实停止状态不允许清理。已有两项更窄
恢复 API 保留；没有新增运行时日志或恢复实现，也没有强化 `wf()`。范围是同步的
具体指令语言，任意 plugin scalar、宿主 callback、一般 foreign replay 观察方程、
owner 表空与全局终止仍未由此证明。详见[Xor 恢复域](progress-contracts.zh-CN.md#xor-补齐具体日志的当前状态恢复域)。

当前蓝图明确使用固定的 `expected` child 名称。一次成功创建后，重新激活
同一个蓝图可能因单调分配器返回新 ID 而得到 `UnexpectedChild`；错误本身
经过原子性证明，尚未等同于论文的动态 fresh-name binder。测试覆盖这一
限制。发布也采用声明的全部 provision slot 已有值的同步策略。

跨 provider 的两个消费者、混合 Xor／Child／Xor 的真实恢复、保留 child
逆操作时禁止删除、目标漂移后 Divert，以及完整脚本在首个错误处停止，均有
可运行测试。该路径不把宿主的任意 async callback、事件、timer 或 loader
工厂自动纳入 Verus 证明。

同步 `MixedDriver::step` 现在以 `step_enabled` 精确刻画成功：actor 必须已登记、Loading 且 coherent，有当前指令，满足 `primitive_enabled`；终态还须满足执行本条指令后的 `complete_after`。Provide 可以在本次调用补齐最后一个空槽；Xor 既要求解析到 provider，也要求其表中实际已有值；Child 仍需 expected 身份与分配器一致、蓝图及插入域有效。公共 Step 的事务错误保持完整机器，但内部执行副本可能已发生变化。该合同排除使能状态下无故拒绝请求，未证明整个程序的动态执行必然结束，详见[进展合同](progress-contracts.zh-CN.md#真实-mixedfresh-解释器的精确单步定义域)。

## 自动 fresh child 的已验证驱动

`cordis_kernel::mixed_driver::fresh` 导出 `FreshDriver`、`Blueprint`、`Instruction`、`RunReport`、`run_script`，以及 `run_from_empty`、`FromEmptyReport`、`FromEmptyStatus`。Child 指令写为 `Instruction::Child { blueprint, next }`，每次成功 landing 从实际 allocator 获取新 ID，以 `Outcome::Child { child, finished }` 返回。跨 provider 的 Xor、Provision、Child 与 LIFO 恢复仍共用一条真实 journal；Blueprint 的 DAG、forward continuation 和完整发布要求与 MixedDriver 相同。

```rust
use cordis_kernel::mixed_driver::fresh::{Blueprint, FreshDriver, Instruction, Outcome};
let leaf = Blueprint::new(vec![], vec![], vec![Instruction::Unit]);
let parent = Blueprint::new(vec![], vec![], vec![
    Instruction::Child { blueprint: 0, next: None },
]);
let mut driver = FreshDriver::new(vec![leaf, parent]);
let owner = driver.insert(None, 1).unwrap();
driver.begin(owner).unwrap();
assert_eq!(driver.step(owner), Ok(Outcome::Child { child: 1, finished: true }));
```

`run_script` 接受相同 Command 序列，返回机器、成功 transitions 与首个错误。从 new/empty 到终点的源轨迹由验证器从实际调用构造，程序的结构 naturality 也已证明。[执行测试](../crates/cordis-kernel/tests/fresh_driver.rs) 覆盖两次激活之间的外部 allocation、provider replacement、真实 XOR/Child/XOR 恢复、retained child、错误后的 payload/journal/allocator 原子保持，以及非零 child blueprint。事务仍复制机器，成本随已保存数据增长；异步在途落地和开放 callback 不属于这一接口的证明范围。

`FreshDriver::selected_instruction` 以当前 `next_id` 实例化 Child 模板，其 `step_enabled` 使用相同的 primitive 与终态发布条件。实际 `step` 在且仅在该条件下成功；自动选取 fresh 身份不消除 provision 冲突或值缺失。此结论限定同步单步；下述跨调用已准入协议有单独的精确落地成功域合同。

## 将一个已开始的 Fresh 程序运行到终态或阻塞

`FreshDriver::run_until_blocked(actor)` 自行调用真实 `step`，直到终态或第一次错误。
调用者不传 fuel，也不用承诺各步成功。返回的 `RunReport.steps: u128` 只统计已提交
调用，包括终态调用；`error` 为第一条真实错误。错误保持已经提交的前缀，只撤销失败
那一步，之后仍可按已有协议处理、重试或恢复；零提交时完整机器满足 `same`。

```rust
use cordis_kernel::mixed_driver::fresh::{Blueprint, FreshDriver, Instruction, RunReport};
use cordis_kernel::{Phase, Port};
let output = Port { key: 91, realm: 0 };
let leaf = Blueprint::new(vec![], vec![], vec![Instruction::Unit]);
let parent = Blueprint::new(vec![], vec![output], vec![
    Instruction::Provide { key: output, value: 42, next: Some(1) },
    Instruction::Child { blueprint: 0, next: None },
]);
let mut driver = FreshDriver::new(vec![leaf, parent]);
let actor = driver.insert(None, 1).unwrap();
driver.begin(actor).unwrap();
let report: RunReport = driver.run_until_blocked(actor);
assert_eq!(report.steps, 2);
assert!(report.error.is_none());
assert_eq!(driver.phase(actor), Some(Phase::Active));
assert_eq!(driver.phase(1), Some(Phase::Inactive));
```

成功只代表当前 actor 已 Active、current 为空。示例中的 child 已登记，但不会自动
Begin 或执行。空程序仍计一次终态 Unit；跳到代码末尾也需该调用。对未知、Inactive
或已经 Active 的 actor 调用，会返回既有 `step` 错误，不能把第二次运行当作成功空操作。

有限界来自真实前向程序位置的 `run_budget`：有效位置为 `code.len() - pc + 1`，
无效或缺失位置为一。成功步数不超过输入预算；阻塞时连同失败尝试也不超过预算，且
最终不满足 `step_enabled`。报告的 `refines` 从真实调用延伸**输入已表示的任意良构
源状态**；公共 proof 方法 `RunReport::advance_source` 可在已有 representation 与
源良构前提下提取这一扩展。它不从任意 `wf()` 独立断言 source 存在；下述
`run_from_empty` 通过真实准备调用建立该输入路径。
ghost 历史在运行时擦除，不为报告分配真实 history 向量。此结果不保证全图 quiet、
阻塞最终解除或任意 Future 完成，详见[进展合同](progress-contracts.zh-CN.md#将单个-fresh-actor-运行到终态或首个错误)。

## 从 empty 完成准备并自主运行

`run_from_empty` 将真实准备脚本和单 actor 执行组合成一个入口，无需调用者先构造机器
或提供源表示证明。以下准备命令安装并 Begin 父程序；随后循环执行 Provide 和 Child。

```rust
use cordis_kernel::mixed_driver::fresh::{
    run_from_empty, Blueprint, Command, FromEmptyStatus, Instruction,
};
use cordis_kernel::{Phase, Port};
let output = Port { key: 91, realm: 0 };
let leaf = Blueprint::new(vec![], vec![], vec![Instruction::Unit]);
let parent = Blueprint::new(vec![], vec![output], vec![
    Instruction::Provide { key: output, value: 42, next: Some(1) },
    Instruction::Child { blueprint: 0, next: None },
]);
let setup = [
    Command::Insert { parent: None, blueprint: 1 },
    Command::Begin { actor: 0 },
];
let report = run_from_empty(vec![leaf, parent], &setup, 0);
assert_eq!(report.status, FromEmptyStatus::Finished);
assert_eq!(report.setup.len(), 2);
assert_eq!(report.steps, 2);
assert_eq!(report.machine.phase(0), Some(Phase::Active));
assert_eq!(report.machine.phase(1), Some(Phase::Inactive));
```

`setup` 保存成功准备调用的实际 `Vec<Transition>`；即使脚本包含 `Command::Step`，
也只记在准备部分。`steps` 仅计之后自主运行的已提交步数，包括终态调用，不计失败尝试。
`SetupFailed(error)` 传播第一次准备调用的真实错误并立即返回，不执行自主循环；此时
`steps == 0`，但所选 actor 可能已经可运行。全部准备成功后，`Blocked(error)` 才表示
自主 step 出错且最终不满足 `step_enabled`；`Finished` 表示本次自主执行到达终态。
准备期间已经完成的 actor，再交给自主循环仍会返回既有 step 错误。

`FromEmptyReport::refines` 无输入源前提，建立一条从 empty 出发的执行，同时表示
真实准备后的机器与返回机器，每态良构且资源安全；公共 proof 方法 `source_execution`
可提取该执行。它以真实准备路径满足 `RunReport` 原有条件化合同的前提，拼接不增加
失败事件。prepared、自主 outcomes 和源轨迹被擦除，准备记录向量仍在运行时存在。
准备调用的精确接纳现覆盖 `Insert`、`Begin`、`Step`，由 proof-only 的
`preparation_command` 限定，`preparation_enabled` 按当前机器分别调用
`insertion_enabled`、`begin_enabled`、`step_enabled`。Insert 检查所需蓝图库前缀和
Kernel 插入域；Begin 要求已登记、保留 journal 为空及 Kernel Begin 域，包括目标可用
和 generation 容量；Step 使用已有 primitive／完整终态发布域。真实 `apply` 在此范围
成功 iff 调用前谓词，运行分支和错误顺序不变。

`run_script` 出错且下一条命令在此范围时，该命令在返回机器中不满足谓词；
`run_from_empty` 的 SetupFailed 同时保证其在 `prepared` 与返回机器中不满足谓词。
这里的“下一条”是 `setup_commands[setup.len()]`，按成功前缀后的状态判断。不是在
初始 empty 状态一次性要求全部命令使能；前缀可包含 Retire 等其他成功命令。
Retire/Depart/Unload/Remove 仍可执行，只未纳入准备范围的这条精确域等价；
Unload 的实际 `apply` 分支另有上文的独立合同。准备谓词对它们返回 false 不能用作
拒绝结论。
合同尚未按输入谓词区分具体错误枚举值，也不保证全部论文已使能
命令都被接纳：蓝图合法性、容量和 strict 值可用性仍是实现域边界。新 child 仍需自行
Begin／执行；这不是全图静止或 strict primitive 总性。
详见[入口合同与边界](progress-contracts.zh-CN.md#从新机器经过真实准备与执行)。

## 已准入阶段的两阶段协议

`mixed_driver::fresh::admitted::Admission` 拥有整个 FreshDriver，并私有保存 actor、
episode generation、蓝图、pc 和指令模板。`FreshDriver::admit(self, actor)` 消费机器；
失败时 `Rejected` 原样返还机器，成功时生成一个不能换绑到其它机器的准入会话。
`apply` 允许其间执行其它已检查调用。`land` 再检查原身份和代码位置，执行捕获的
闭合动作，保存真实 inverse，并依据当前 target 返回正常 Iter/Finish 或 landing Divert。
已准入 Child 的名字仍在实际落地时分配。目标丢失后，落地使用原 committed providers。

`admit` 成功 iff `admission_enabled = ready`，只接纳当前已登记、Loading/coherent 且有指令的 actor，不预留服务值和 provision。`land` 成功 iff `land_enabled`：票据尚未消费、捕获的 generation／蓝图／pc／模板仍绑定当前机器，所选 primitive 的定义域有效，且 coherent 终态执行后能完整发布。`Admission::selected_instruction` 在调用时以当前 `next_id` 实例化 Child。目标丢失时会 Divert，不要求完整发布，但仍检查值可用与 child 注册域；成功返回的 `diverted` 恰好反映调用前不 coherent。

成功 `admit` 还保证返回票据的 `land_enabled()` 等于调用前机器的 `step_enabled(actor)`。无其它操作插入时，立即落地与同步 step 的成功条件相同；这不是结果等价或跨任意中间调用保留定义域的声明。

因此接纳成功并不保证下一次落地成功。值缺失、其它调用预留了 child provision 或 coherent 终态未完整发布，都可能使落地失败。失败保持同一票据未消费，可在通过已检查调用解除对应条件后重试；冲突条目只有退休还不够，须移除才释放预留端口。真实运行分支与错误顺序保持不变。这是局部成功合同，不是任意 Future 的终止承诺。

成功落地会消费准入资格，重复落地失败；同 actor 已前进或重新开始了 episode 时，
旧准入也失败。所有落地错误保持完整机器、准入身份和消费标志不变。
`into_driver` 消费会话并返还机器。当前支持单个 pending admission；它不允许持有
可换绑的 ticket，也不声称已验证任意 future 或 callback 的内部行为。Xor、Provision、
Child 和 Unit 本身仍在 `land` 内同步执行；证明覆盖跨 intervening calls 的两阶段协议。

`admitted::script::run_script` 从新机器开始执行 Call / Admit / Land / Release。
Call 和 Land 产生实际源步骤，Admit 与 Release 只改变会话元数据。公开契约保证成功
前缀中的每个实际调用或落地都有且仅有一个事件，`action_index` 严格递增，且全部事件
组合为同一安装程序的 `fresh_semantics` 历史。首个错误保留完整机器和已成功历史；
返回报告不保留 pending ticket。

```rust
use cordis_kernel::mixed_driver::fresh::{Blueprint, Command, Instruction};
use cordis_kernel::mixed_driver::fresh::admitted::script::{run_script, ScriptAction};
use cordis_kernel::Phase;

let report = run_script(
    vec![Blueprint::new(vec![], vec![], vec![Instruction::Unit])],
    &[
        ScriptAction::Call(Command::Insert { parent: None, blueprint: 0 }),
        ScriptAction::Call(Command::Begin { actor: 0 }),
        ScriptAction::Admit { actor: 0 },
        ScriptAction::Call(Command::Retire { actor: 0 }),
        ScriptAction::Land,
        ScriptAction::Release,
        ScriptAction::Call(Command::Unload { actor: 0 }),
    ],
);
assert_eq!(report.error, None);
assert_eq!(report.completed, 7);
assert_eq!(report.machine.phase(0), Some(Phase::Inactive));
```

真实执行测试覆盖 provider 离开后的共享值落地与精确撤销、动态 Child 的漂移落地、
旧 generation／pc 拒绝、失败原子性，以及脚本事件与成功输入前缀的完整对应。
见 [admission tests](../crates/cordis-kernel/tests/admitted_fresh_driver.rs)
和 [script tests](../crates/cordis-kernel/tests/admitted_script.rs)。
