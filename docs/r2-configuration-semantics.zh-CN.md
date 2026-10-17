# R2 第 3 包：运行中的 Loader 配置语义

当前 R2 状态以[第 5 包统一验收](r2-acceptance.zh-CN.md)为准：managed-production/v1 范围已完成。下文保留各批次历史记录及其当时的验证范围。

[第 4 包](r2-production-composition.zh-CN.md)组合实际类型化配置／来源投影与原生 Insert 来源；R2 最终验收仍单独保留。

[English](r2-configuration-semantics.md) · [配置执行协议](r2-configuration-execution.zh-CN.md) · [论文映射](paper-refinement-map.md)

原生 JSON Loader 现在直接在验证内核中解释配置：选择实际注册的模块，应用继承的
intercept，使用该模块持有的 schema 完整规范化配置，并保存用于挂载、更新和恢复的
不可变配方。持久化使用受验证的三方合并；配置拆回源文件后，还必须经过真实 include
展开流程，完整还原当前配置树，才能成为保存计划。

本包闭合第 3 包的配置数据与绑定层。**R2 仍在进行中**：第 4 包负责全部生产步骤与
观察的统一组合，第 5 包负责 R2 总验收。通过 schema 校验不等于证明任意模块体满足
Component 定义。

## 实际路径上的保证

| 实际操作 | 验证合同 | 用户获得的保证 |
| --- | --- | --- |
| 注册工厂与 `Loader::prepare` | `Modules::prepare` 选择真实 `Definition`，执行 intercept 和其持有的 schema，返回满足 `Prepared::wf` 的配方。 | intercept 或默认值修改配置后，不能静默使用原始参数；重新注册工厂不会改写旧配方保留的引用。 |
| 父子配置作用域 | `Modules::extend` 完整保留未被覆盖的绑定；`data::apply` 执行递归对象覆盖。 | metadata 和 injection 按键继承；intercept 递归合并；数组、标量和 null 替换原值，null 不等于删除。父作用域不被修改。 |
| schema 校验 | `Schema::validate` 精确返回 `normalized`，或在其未定义时拒绝。 | 完整遍历数组和对象字段；默认值也需校验；检查必填项、未知字段和包含端点的数值范围。 |
| 挂载、配置更新、恢复 | 宿主解码同一份 `Prepared::config`，用保留的模块与作用域执行；既有更新和重建 owner 保留该配方。 | 执行时不会按可变名称重新选择工厂；注册时缓存编译后的 schema。 |
| 三方保存合并 | `MergeProof::valid` 递归覆盖基线、本地意图、磁盘内容中的全部键。 | 双方独立修改被保留；删除区别于 null；冲突在写入前拒绝整个计划。 |
| 子条目顺序 | `ordered` 要求顺序包含每个存活成员且恰好一次。 | 不能静默丢弃合并出的新条目或重复条目；普通 JSON 数组仍按整体处理。 |
| include 来源投影 | `RoundTrip::check` 比较完整目标树与待保存文件实际展开后的树。 | 相同 revision 或条目数不能掩盖嵌套字段变化、子树丢失或跨文件顺序变化；共享 include 的编辑必须一致。 |

保存报告仍区分文件替换与目录持久化。后续文件失败不会撤销前面已经完成的写入；
既有 source owner 只推进得到确认的本地检查点。新增数据合同与这些协议组合，不把
多文件保存描述为原子事务。合并保留的外部修改仍需后续 reload 才会应用到运行插件。

## 论文对应

定义 81 的六个字段仍分别保留：父节点内的稳定 ID、模块、isolate、intercept、原始
绑定配置，以及该条目自身的管理状态。`Prepared::entry` 解释解析后的模块与原始配置；
`Prepared::wf` 进一步连接原始配置、intercept、schema 与实际有效参数。注册名称通过
真实表解析，不会在缺少解析器时被冒充为外部 URL。原有 `Entry::as_paper_entry` 仍是
保守的、显式解析后的叶条目投影。

既有 checked planner 已建立完整前序、有效 enabled 状态和父节点内的归属。既有
expander 已证明每份 include 的实际读取来源、环和深度检查，并按“内联子条目在前、
include 子条目在后”的顺序挂在请求节点之下。本包补齐这些真实遍历周围的值解释与
保存回读检查。

原生 Loader 将 group 展开为**受验证的空服务程序**与既有结构插入协议管理的归属
子条目，不再为 group 安装不透明的空 Rust 回调。include 在规划前展开，不产生另一份
隐藏运行树。这是本 Loader 明确采用的转换方式，不表示任意 JavaScript group/include
插件的回调体已经获得相同证明。完整生产序列到论文步骤的对应由第 4 包完成；原论文
的全域 Component、终止和合流命题，以及 R1 已明确记录的语义修订，均未改变。

## 审查与信任边界

- `config_data.rs` 在 serde JSON 与 checked 结构值之间转换，保留编码后的标量值，区分 null
  与键缺失；输入对象键使用 serde 的规范顺序；即使拦截合并追加了键，enum／合并判断也按键比较对象字段。enum／合并比较中浮点正负零相等，但实际
  选中值保留符号；大整数身份不会因转成 `f64` 而合并。
- 适配层提供标量分类和浮点比较操作数的 IEEE-754 排序编码。JSON 解析、该编码、
  序列化、文件身份与 I/O 不属于内核证明。范围判断、默认值和递归验证由 checked
  解释器执行。`Schema::compile` 从公开 schema 构造器逐项转换到工厂持有的 checked
  schema，仍是需要审查的适配边界。
- 注册操作提供真实 Rust 工厂闭包与服务键。其外部效果、工厂结果的声明、任意清理逆
  操作、调度公平性与最终返回仍需各自合同。Node 的任意 JS 值、模块求值和自定义
  schema 回调只享有已经明确说明的宿主／派发边界保证。
- 来源回读保证针对审查时的结构化快照；后续保存继续使用已有重检。它不是文件系统
  CAS、多文件事务，也不证明最终收敛。

这些是明确的数据解释与外部系统边界，不是把未实现的合并或 schema 循环移入假设。
本轮没有新增 `assume`、`admit`、`external_body` 或跳过验证的替代实现。

## 证据与复现

核心实现位于
[`configuration_module.rs`](../crates/cordis-kernel/src/configuration_module.rs)、
[`configuration_binding.rs`](../crates/cordis-kernel/src/configuration_binding.rs)、
[`configuration_schema.rs`](../crates/cordis-kernel/src/configuration_schema.rs) 和
[`configuration_data.rs`](../crates/cordis-kernel/src/configuration_data.rs)。真实调用者是
`cordis` 宿主 crate 的 `loader.rs`、`config.rs`、`config_data.rs`、`persistence.rs`。

[开发记录](development-report.json) 将完整正向证明、Rust／Node 回归与打包检查绑定到
当前源码。`python3 scripts/record-development.py --check` 检查新鲜度；
`python3 scripts/record-development.py --offline` 复现完整开发验收。

集中案例覆盖旧工厂引用保留、intercept 与默认值、冲突与删除、完整来源等价、子条目
无遗漏、浮点零与大整数、合法特殊字段名的错误定位，以及原有 include 拓扑、取消恢复
和部分保存重试。四个 canonical 反例分别故意接受错误回读、丢失磁盘修改、跳过默认值、
忽略 intercept；局部拒绝证据要求对应正向通过、变体可编译、指定合同失败。它不等于
全量反例回归、发布验收或整篇论文验收。
