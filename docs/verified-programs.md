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

当前蓝图明确使用固定的 `expected` child 名称。一次成功创建后，重新激活
同一个蓝图可能因单调分配器返回新 ID 而得到 `UnexpectedChild`；错误本身
经过原子性证明，尚未等同于论文的动态 fresh-name binder。测试覆盖这一
限制。发布也采用声明的全部 provision slot 已有值的同步策略。

跨 provider 的两个消费者、混合 Xor／Child／Xor 的真实恢复、保留 child
逆操作时禁止删除、目标漂移后 Divert，以及完整脚本在首个错误处停止，均有
可运行测试。该路径不把宿主的任意 async callback、事件、timer 或 loader
工厂自动纳入 Verus 证明。

## 自动 fresh child 的已验证驱动

`cordis_kernel::mixed_driver::fresh` 导出 `FreshDriver`、`Blueprint`、`Instruction` 与 `run_script`。Child 指令写为 `Instruction::Child { blueprint, next }`，每次成功 landing 从实际 allocator 获取新 ID，以 `Outcome::Child { child, finished }` 返回。跨 provider 的 Xor、Provision、Child 与 LIFO 恢复仍共用一条真实 journal；Blueprint 的 DAG、forward continuation 和完整发布要求与 MixedDriver 相同。

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

## 已准入阶段的两阶段协议

`mixed_driver::fresh::admitted::Admission` 拥有整个 FreshDriver，并私有保存 actor、
episode generation、蓝图、pc 和指令模板。`FreshDriver::admit(self, actor)` 消费机器；
失败时 `Rejected` 原样返还机器，成功时生成一个不能换绑到其它机器的准入会话。
`apply` 允许其间执行其它已检查调用。`land` 再检查原身份和代码位置，执行捕获的
闭合动作，保存真实 inverse，并依据当前 target 返回正常 Iter/Finish 或 landing Divert。
已准入 Child 的名字仍在实际落地时分配。目标丢失后，落地使用原 committed providers。

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
