# R2 第 4 包：生产轨迹组合

当前 R2 状态以[第 5 包统一验收](r2-acceptance.zh-CN.md)为准：managed-production/v1 范围已完成。下文保留各批次历史记录及其当时的验证范围。

[English](r2-production-composition.md) · [R2 合同](r2-execution.zh-CN.md) · [状态清单](r2-state-inventory.zh-CN.md)

本包将**实际生产快照**接入受验证状态上的完整步骤分类，组合前面的一般托管函数、
宿主引用和配置语义。[第 5 包](r2-acceptance.zh-CN.md)现已提供明确范围的统一验收；本包不代表整篇论文完成。

## 保证的含义

生命周期投影不变时，服务值、版本、清理义务、回调声明或配置仍可能变化。
这些步骤不能被称为完整记录状态上的内部停顿（stutter）。

对于原生 Journal 的每一次实际提交，生产解释保留全部 13 种记录及待登记 inverse，
构造从空图开始、包含全部交错步骤的连续控制轨迹。每一步对应论文控制规则、显式
Restart、完整记录确实不变，或带有准确记录合同的实现扩展。即使 Iter 的控制状态
不变，原生修订号也仍然可见。论文标签解释的是控制投影；函数／效果语义仍由
[第 1 包](r2-function-semantics.zh-CN.md)的真实执行与回执证明提供。

Node 解释覆盖完整协议观察：生命周期动作、publication 值／版本／lease、检查、
策略、Episode、回调作用域、恢复选择、待释放句柄和动态接口，并从实际步骤构造连续
控制历史。动态接口与 Restart 保持为显式扩展；只有不含扩展的控制投影进入严格论文闭包。

## 实际所有者如何组合

| 生产路径 | 组合合同与证据 |
| --- | --- |
| `Runtime::execution_snapshot`／`plugin_execution_snapshot` → 内核快照 | 类型化 publication、标量／payload、工作、清理和作用域证书对应同一 Journal 时点。`Snapshot::new` 与 `into_joint` 建立生产解释，调用方不提供预期轨迹。 |
| Node 诊断 → `Driver::execution_snapshot` → `NodeRuntime::snapshot` | 实际生产者对自身完整协议历史建立 `production::interpreted`。JSON 格式化仍是适配器边界。 |
| `Bridge::{issue, bind_fiber, unbind_fiber, begin_call, finish_call, remove}` | 每次成功修改实际引用表，都记录准确的擦除历史；拒绝保持所有者不变。涉及 Node 的守卫保留该次调用真实读取的协议截面。 |
| `Bridge::snapshot`／`HostSnapshot::production_trace` | 检查所有保留 publication／已登记 Fiber 的引用覆盖，将实际引用和当前协议配对，并推导对象发行及待处理票据声明的真实来源。 |
| `Loader::execution_snapshot` → 原生 `configuration_snapshot` | 原生、类型化配置和来源历史共享一个 Journal 快照。三者 key 不同，各自每次修改都有对应观察；每个来源动作都能定位到之前准确的已接受配置，包括版本相同的 refresh／recovery。 |
| Loader 实际挂载／重建 → `configuration_allocation` → `Tree::ready` | 每个启用的 root／group／Child 分配都指向真实 Insert 及其原始父节点。ready 推导完整、父节点正确、身份不重复的展开结果；现有运行检查仍拒绝失效分配。 |

内建原生 group 使用受验证的空服务程序，后代通过独立的 Insert／Begin／函数／Finish
步骤成为真实的所属注册。规划器的完整先序遍历和父节点实际返回的作用域决定其结构。
这是 group／include 的行政展开，不将整个 Loader 事务伪装为一个原子论文效果，也不
因此给任意 factory 代码赋予 Component 证明。

Bridge 记录的协议截面来自该次调用实际读取的 NodeRuntime 参数。生产 Driver 保留
bridge 与 core 的配对关系；引用历史和协议历史分别保持自身顺序。这些证书不会为独立
所有者捏造统一时钟，也不会从相同数字 domain 推断两个对象是同一个实例。

## 论文到代码的审查入口

| 论文连接 | 入口 |
| --- | --- |
| Definition 58／63，完整执行与控制步骤 | [native_production.rs](../crates/cordis-kernel/src/native_production.rs)、[node_production.rs](../crates/cordis-kernel/src/node_production.rs)：`production_step`、`production_trace` |
| Definition 29／式 (31)，真实值及 inverse 定义域 | [托管函数](r2-function-semantics.zh-CN.md)与现有类型化／标量证明继续关联真实回执；完整记录分类保留待登记义务。 |
| Begin、回调分派、引用保留 | [node_bridge_history.rs](../crates/cordis-kernel/src/node_bridge_history.rs)：`step`、`object_origin`、`claim_origin`；[node_bridge.rs](../crates/cordis-kernel/src/node_bridge.rs)：实际修改入口与快照 |
| Definition 81、group／Child 展开 | [configuration_runtime.rs](../crates/cordis-kernel/src/configuration_runtime.rs)：真实分配；[native_history.rs](../crates/cordis-kernel/src/native_history.rs)：`insertion_origin`；[configuration_tree.rs](../crates/cordis-kernel/src/configuration_tree.rs)：`elaboration` |
| 配置／来源事务组合 | [native_configuration.rs](../crates/cordis-kernel/src/native_configuration.rs)：`production_trace`、`covered`、`source_reviewed`；[第 3 包](r2-configuration-semantics.zh-CN.md)：实际数据、模块与来源语义 |

## 复现与验证边界

使用固定工具链，一次性运行开发验收：

```sh
python3 scripts/record-development.py --offline
python3 scripts/record-development.py --check
```

[开发记录](development-report.json)以源码指纹绑定整核证明、Rust／Node 回归、示例及
提取包检查；源码变化后旧记录失效。新增四个 canonical 反例分别针对：把原生控制停顿
冒充完整停顿、Node 的同类错误、结束尚未完成的回调声明、替换分配的 Insert 来源。
局部反例要求新鲜正例、完整变异源码可编译及指定合同准确拒绝，不等于完整反例回归。

历史与解释证明在普通 Rust 编译时擦除，不引入运行事件日志、旧 payload 保留、回调
重放或 Verus-TLA 依赖。Node Episode 更新拆成局部 payload 合同，再组合协议合同，
以便在现有求解器资源限制内完成验证。

受验证载体**不包含**任意 JS／Rust 对象内部变化、回调计算或用户析构。
JSON／URL／IEEE 转换、Node-API／JS／ALS、普通 Arc／Mutex、唤醒与错误汇总、
外部 I/O、静态嵌入的 lease 真实性保留明确边界；其可观察影响不被本包认证为停顿。
冲突命名端口别名继续保留既有语义条件。一般恢复、公平调度、全局终止及合流属于后续里程碑。

[第 5 包](r2-acceptance.zh-CN.md)现已冻结并审查组合范围，提供真实故障／重试路径和严格局部反例证据；其验收仍区别于发布和整篇论文完成。
