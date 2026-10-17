# 具有混合效果的受验证函数

[English](managed-functions.md) · [Rust API](../rust-api.zh-CN.md) · [R2 函数语义](../r2-function-semantics.zh-CN.md)

存储在注册表中的原生函数可以修改可逆标量、替换强类型服务值，并根据实际结果选择
下一步。root 和 Child 程序体使用同一个受验证解释器。执行失败时，已经成功的操作
仍在所有者的真实清理队列中保留准确的逆操作。

这是 R2 第一包：**具有混合标量与强类型效果的有限托管函数体**。它将论文中的操作、
continuation 和 inverse 定律连接到用户实际执行的代码；整个宿主、Node 和配置
refinement 是后续独立工作包，不能由这一包代替。

## 运行示例

在当前源码目录中，使用项目的 Rust 工具链和已缓存依赖：

```sh
cargo run -p cordis-verus --example managed_function --offline
```

[示例](../../crates/cordis/examples/managed_function.rs) 会执行混合函数，引入冲突替换，
观察清理阻塞及 provider 保留，最后恢复后来的写入并成功重试。
运行时不需要 Node.js 或 Verus。

尚未发布的新 API 使用带类型的指令构造器：

```rust,ignore
use cordis::{ManagedInstruction as I, Plugin, ValueBranch, ValueOperation};

let finish = ValueBranch { matched: None, unmatched: None };
let plugin = Plugin::native_function("request policy", vec![
    I::scalar(budget, ValueOperation::CompareExchange { expected: 10, value: 13 },
        ValueBranch { matched: Some(1), unmatched: Some(2) }),
    I::replace(label, "selected".to_owned(), finish),
    I::replace(label, "unmatched".to_owned(), finish),
])?;
let id = runtime.mount(&context, None, plugin)?;
runtime.settle().await?;
```

其中 `budget` 是 `ServiceKey<ReversibleValue>`，`label` 是 `ServiceKey<String>`。
作为 Child 使用时，将同一个插件传给 `setup.mount(plugin)`。
`native_function` 从**全部**指令推导依赖，包括未选中的分支。
continuation 只能指向程序体内后面的指令，或用 `None` 结束；强类型替换选择 `matched`。
已有 provider 和普通回调 API 继续可用。该函数体要求原生运行时，静态宿主会明确报错。

## 用户保证与审查路径

| 用户保证 | 真实执行路径 | 论文／证明连接 |
| --- | --- | --- |
| 执行安装的函数及其实际键和参数 | `Function::bind`、`run_managed_root` | 检查真实配方、版本和 owner；签发 root 前解析全部声明键。直接调用也拒绝替换成另一个已声明键。 |
| 真实结果决定后续分支 | `Execution::run_function`、`execute_call` | `Step::interpretation` 将具体写入、结果和下一条指令连接到 Definition 29／公式 (31) 及 Definition 30。完整载体语法定理覆盖两种分支。 |
| 混合效果的完整成功前缀可以严格恢复 | 实际标量与强类型 inverse 登记 | `Report::interpret_queue` 在所有恢复堆上将真实队列后缀等同于严格语义逆序栈；实际正向状态能够衔接时，`recoverable` 推出往返恢复，不预设 inverse 成功。 |
| 不能跳过受阻 inverse 或提前释放 provider | 已有受验证清理派发和重试协议 | `next_inverse` 将真实 LIFO 选择连接到最后一个标量／强类型步骤；清理失败保留 inverse 和 committed 依赖。 |
| 本地／外部／本地调用之间保留真实因果关系 | `Journal::join_receipts`、实际加锁观察和写入 | 同 Journal 中此前的写入与 inverse 登记都早于后续写入，即使中间经过外部 Journal；`execution_interval` 再将这些凭据连接到实际函数返回。 |
| 返回真实失败，不丢失成功前缀 | 读取守卫、标量拒绝凭据及强类型加锁拒绝观察 | `Failure::explained` 区分类型／可用性、过期计算、容量及已退休载荷失败。标量拒绝保持完整记录状态和待登记义务。 |

可执行解释器在 [managed_function.rs](../../crates/cordis-kernel/src/managed_function.rs)，
通用操作／函数定律在 [managed_semantics.rs](../../crates/cordis-kernel/src/managed_semantics.rs)，
实际队列与轨迹连接在 [managed_trace.rs](../../crates/cordis-kernel/src/managed_trace.rs)。
[managed_root.rs](../../crates/cordis-kernel/src/managed_root.rs) 是普通 Rust 宿主经 driver
实际调用的入口。这些文件既是 Verus 输入，也是 Cargo 编译的生产代码，没有另设仅供证明的解释器。

## 准确的语义范围

原语载体由标量状态和强类型载荷状态组成。强类型替换跟踪实际 `Arc<T>` 身份、
可逆 head／depth 和严格 inverse；独立单调递增的读取版本防止恢复后旧检查重新生效。
任意 `T` 内部修改及析构行为不在这一解释范围中。

内核对受验证的 `ScalarEffect` 实现泛型化，并不限于宿主的 `ValueOperation` 枚举。
内核验收使用 `ScaleAdd` 与强类型替换组合。新增效果族需要提供正向／逆向定律，并连接
实际准入、存储和清理后才能加入解释器；普通 Rust trait 实现或任意回调不会自动获得证明。

`Function::member` 覆盖全部语义输入、两种分支，以及每个显式解析／新 head 安排。
`Function::component` 在声明范围前提下给出对应的名字端口 Component 定律。
实际报告使用真实捕获、返回和保留 inverse 实例化对象解释。
对象地址同时包含 **Journal 和对象编号**。

别名有明确含义：修改共享对象会影响所有选择它的名字，其他名字保持不变。
只有没有其他当前名字选择该地址时，`single_key_projection` 才能将真实写入提升到
论文字面的单名字修改规则。Rust 键类型不自动满足这个条件。
指令之间解析结果可以改变，每个 inverse 保留自己原来的对象；这里没有声称冲突别名
无条件满足原始载体上的独立性。

函数不是跨对象原子事务。认证历史保留交错，外部 Journal 保持独立；严格 inverse
可能被后来的冲突写入阻塞。恢复保证适用于能够衔接的正向历史，不承诺无视任意冲突修改。
成功返回与失败前缀均受合同约束，但不保证异步调度或清理最终完成。

证明凭据和历史会从运行产物擦除，运行报告只保留有限的具体结果数据，不增加持久执行日志。
动态 publication 和 Child 创建不是该函数语言的指令：Child 的**程序体**可以使用它，
外围注册／生命周期协议继续使用已有合同。

## 交付验收

集成场景在[内核测试](../../crates/cordis-kernel/tests/managed_function.rs)与
[宿主测试](../../crates/cordis/tests/managed_function.rs)中，覆盖混合 root／Child、
真实两种分支、别名、本地／外部／本地因果关系、新配方参数、未声明／替换键拒绝、
错误 owner、重复调用、退休存储、失败前缀恢复、清理冲突／重试及静态宿主拒绝。

新增四个规范负例挑战这条连接：实际返回时遗漏效果凭据；不执行选中的 continuation；
伪造 Episode 已关闭的读取错误；强类型写入遗漏前面的因果凭据。
每个负例都要求新的匹配正例、完整突变体编译，以及准确函数／错误类型／源码锚点拒绝。
编译失败、超时和求解器资源限制不作为通过依据。

[开发记录](../development-report.json) 保存源码指纹、全内核证明、工作区／Node 回归及
打包检查。使用 `python3 scripts/record-development.py --offline` 复现完整开发验收；
全量突变回归单独运行 `python3 scripts/check-negative.py`。
定向负例不等同于全量负例或发布验收。

R2 的剩余工作是完整宿主观察和别名到 Episode 的归属连接；完整 Node 对象／Fiber／HMR
及配置／源语义；整个宿主的步骤组合与最终联合验收。
任意回调效果需要明确的受验证合同。这些仍记录在[refinement 计划](../paper-refinement-plan.json)，
不会因为本次有限函数包完成就被标为已完成。
