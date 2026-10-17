# 存储函数与动态服务解析

[English](r2-function-semantics.md) · [R2 进度](r2-execution.zh-CN.md) · [Rust API](rust-api.zh-CN.md)

R2 第一函数包现在还支持通过 `Plugin::native_function` 组合**标量和强类型替换效果**。
存储的 root／Child 程序体具有完整载体上的函数解释，continuation 来自真实结果，
严格混合逆序栈与实际清理队列对应。见[完整交付范围、运行示例和证明边界](cases/managed-functions.zh-CN.md)。

原生运行时现在可以把完整的有限多服务函数直接存进注册表。
`Plugin::native_service_program` 可作为 root 或 Child 使用，并从全部指令自动生成依赖，
包括未被选中的分支。可执行 Verus 解释器运行实际存储的程序体，保留每个成功步骤的逆操作。
这是尚未发布的 R2 实现进展，还不是整个 R2 的验收完成。

```rust,ignore
let plugin = Plugin::native_service_program("adjust", vec![
    ServiceInstruction { key: left, operation: ValueOperation::Add(2),
        branch: ValueBranch { matched: Some(1), unmatched: Some(1) } },
    ServiceInstruction { key: right, operation: ValueOperation::Add(3),
        branch: ValueBranch { matched: None, unmatched: None } },
])?;
runtime.mount(&context, None, plugin)?;
```

每条指令从 Begin 绑定的服务槽捕获当时的实际对象。不同名字可以互为别名，槽位替换后，
后续指令也可以选中新对象；每个 inverse 保留自己原先的对象。其他调用可以交错，
所以整个程序体不是跨对象事务。静态宿主会明确拒绝这个仅适用于原生运行时的程序体。

## 生产代码审查路径

| 关注点 | 实际实现与合同 |
| --- | --- |
| 存储的函数身份 | [value_function.rs](../crates/cordis-kernel/src/value_function.rs) 的 `Body::Services(Function)` 直接保存程序体 |
| 声明与 realm 绑定 | [service_function.rs](../crates/cordis-kernel/src/service_function.rs) 的 `Function::bind` 从实际注册配方解析全部键，保持操作与分支；第一个登记匹配优先于继承别名 |
| 准入与完成 | `NativeRuntime::run_service_root` 检查真实 owner、生命周期准入与当前配方，使用真实执行结果结算 root 的成功或失败 |
| 实际调用 | [service_program.rs](../crates/cordis-kernel/src/service_program.rs) 的 `Execution::run_service_program` 逐条解析槽位、执行操作，登记 inverse 后才继续 |
| 完整有限函数解释 | [service_composition.rs](../crates/cordis-kernel/src/service_composition.rs) 对每种解析安排证明语法成员关系，再把真实成功／失败报告接入实际选择的安排 |
| 累积逆操作 | [service_stack.rs](../crates/cordis-kernel/src/service_stack.rs) 把语义逆序栈与真实清理队列后缀对应起来，覆盖失败前缀 |
| 用户入口 | [runtime.rs](../crates/cordis/src/runtime.rs) 的 `Plugin::native_service_program`、原生初始化及 Child 注册，经 [native.rs](../crates/cordis-driver/src/native.rs) 调用检查内核 |

缺少声明时，即使该指令不会被执行，也会在签发 root 前拒绝。错误 owner、已退役或已经
签发的 root 也不会执行。准入成功后仍可能出现执行失败；此时 root 按失败结算，
但完整保留实际成功前缀的 inverse 队列。普通回调中的 `run_service_program` 使用相同的
程序体合同，但这不会为周围任意回调代码自动产生证明。

## 与论文的对应及边界

Definition 29 的公式 (31) 描述单个上下文绑定上的操作、真实结果和 inverse；
Definition 30 组合由结果选择的 continuation。两个名字如果指向同一可变对象，
没有附加条件就不能满足字面的“只修改一个名字”。因此这里把解析作为显式输入，
在带完整身份的对象载体上解释效果。

`Address { journal, key }` 包含真实 Journal 身份，而不只有域内数值编号。
`resolved_member` 对每个有限函数的所有解析安排、所有载体输入证明最小语法成员关系。
`interpret_dynamic` 用真实捕获的绑定以及实际写入／拒绝凭据实例化该解释。通用定理覆盖
两种分支，实际返回结果决定本次 continuation。失败指令也绑定到真正拒绝的对象，
其操作在记录输入上返回空结果；该拒绝保持完整记录状态与待登记义务映射。

这是对完整有限程序体的参数化对象解释，不是动态别名在原论文名字载体上的无条件
Component 成员证明，也不推出固定声明端口之间独立。此前的唯一别名条件仍控制字面
单键特化。服务解析没有被偷偷当成跨执行、跨槽位替换保持不变的输入。

`interpret_queue` 在**所有**恢复堆上连接真实队列后缀与严格逆序栈。
`roundtrip` 进一步证明：如果记录的实际正向前后状态能从某个输入衔接，则逆序栈恢复该输入。
这里不假设 inverse 成功、不把阻塞当作成功，也不承诺在冲突的外部写入下仍能恢复。
共享别名和不同 Journal 都在栈中得到区分。生产入口还证明真实等待队列准确追加了
这些指令的 token。`CleanupDispatch::selected_from` 导出实际弹出规则：重试保留已选票据，
新恢复动作选择等待队尾。`next_queued_inverse` 将实际返回的派发动作连接到最后一个
真实前缀 inverse，从而组合存储、调度顺序和 payload 身份；没有假设一个额外的 LIFO 列表，
也没有承诺清理最终完成。

同一 Journal 内，已有 `source_trace`／`failed_trace` 保留全部交错事件。
跨 Journal 的调用保留独立历史和完整对象身份，不捏造共同原子快照或总顺序。
槽位选择、写入、inverse 登记和 root 完成仍是不同的实现步骤。

## 将真实效果接入实际调用返回

已登记的有限 Value 和 Service 函数现在会保留实际写入及逆操作登记的可信凭据。
Service 失败保留实际被拒绝的调用；Value 报告保留完整对象观察，其中包含最终被
拒绝的指令。`record_recipes_following` 在写入真实 `Call` 返回记录的同一个 Journal
写锁周期内，向权威历史核对这些凭据，并在返回报告中携带该提交的凭据。

`RegisteredReport::execution_interval` 将已有的操作与逆操作解释接到具体返回事件：

- 同 Journal 的每次写入和逆操作登记都严格早于返回。
- 同 Journal 的失败尝试或失败 Value 观察也早于返回；失败返回不会抹去成功前缀及其逆操作。
- 共同前缀保留其他调用穿插的事件，不要求这些步骤相邻。
- 外部值历史保留各自的 Journal 身份。即使正向写入属于外部 Journal，本地逆操作
  登记仍会被接入返回之前；这里不推导跨 Journal 的全局顺序。

凭据由实际解释器收集，不由普通宿主回调提供。它们是持久的证明资源，映射表及
Journal 引用都会从运行产物中擦除。实现复用已有的短 Journal 提交，不增加运行时效果日志。

审查入口是 [value_registration.rs](../crates/cordis-kernel/src/value_registration.rs) 的
`Evidence::retain`、[value_program.rs](../crates/cordis-kernel/src/value_program.rs) 和
[service_program.rs](../crates/cordis-kernel/src/service_program.rs) 的真实生产路径，以及
[native_runtime.rs](../crates/cordis-kernel/src/native_runtime.rs) 的 `record_recipes_following`。
两个已登记 root 入口传入实际报告，并导出返回区间定理。这加强了定义 29–30 与实现
之间的连接，不增加一般回调定律、原始载体上的 Component 定理或最终返回保证。

## 验证与剩余范围

新增两个可编译负例，在真实调用返回处丢弃 Value／Service 报告的实际效果凭据。
即使函数仍然计算并返回真实结果，这两个错误实现也会被返回合同拒绝。

集成场景覆盖实际存储 root／Child、显式 realm 优先于继承别名、两个名字共享对象、
另一个 provider 的外域对象、失败前缀恢复、配方更新版本、重复／退役／错误 owner 拒绝、
空程序、非法分支以及静态宿主拒绝。见[内核案例](../crates/cordis-kernel/tests/registered_value_function.rs)
和[宿主案例](../crates/cordis/tests/reversible_runtime.rs)。

所选可编译负向对照覆盖替换存储操作、丢失 Journal 身份、解释中的逆操作顺序错误、
从实际清理栈先取最早 token，以及丢弃成功前缀之后的最终失败。
操作绑定、实际清理栈和失败前缀突变修改运行代码；对象身份和解释中的逆序栈突变修改生产合同采用的语义解释。
[R2 进度](r2-execution.zh-CN.md) 记录绑定最终源码的验证结果与未运行范围。

混合函数包在已有标量路径上加入强类型替换及参数化的完整载体 Component 定律。
一般回调程序体、尚无受验证定律的新效果族、冲突别名在原始载体上的无条件组合、
Node 对象／版本和动态接口语义、配置展开、结构性组件动作／重建及持久化仍未完成。
实际原地更新与 inverse 所有权已有[受验证配置合同](r2-configuration-execution.zh-CN.md)，
其整树／联合观察仍未完成。
不能据此宣布整篇论文完成，或声称已经证明任意回调和 Future。

## 非标量替换原语

普通 root／Child 回调现在可以调用 `replace_service` 执行强类型替换，并把受验证
逆操作保留在真实清理组中。该原语具有完整语义载体上的操作／逆操作定律，以及
相互衔接的逆操作栈恢复定理。`Plugin::native_function` 现在把它与标量效果组合为
存储的、由结果选择后续步骤的函数体；Component 解释保留明确的解析／别名条件。
任意周围回调仍不在该函数体定理中。参见
[强类型替换及版本分离](r2-execution.zh-CN.md#可恢复的强类型载荷替换)。

真实强类型逆操作现在把请求、加锁观察、可选恢复写入和确认连接成同一认证协议。
区间保留全部交错，并排除已完成票据重新生效；见
[强类型清理区间](r2-execution.zh-CN.md#强类型清理的请求读取和确认)。
[混合函数包](cases/managed-functions.zh-CN.md) 现已将这些原语效果连接到真实登记调用的
返回。整个宿主的步骤组合与任意回调含义仍是独立的证明义务。
