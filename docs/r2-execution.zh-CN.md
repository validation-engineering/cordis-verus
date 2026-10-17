# R2：生产执行路径的合同

当前 R2 状态以[第 5 包统一验收](r2-acceptance.zh-CN.md)为准：managed-production/v1 范围已完成。下文保留各批次历史记录及其当时的验证范围。

## 历史实施与验证记录

[第 4 包生产组合](r2-production-composition.zh-CN.md)已接入真实原生／Node 轨迹、引用表修改历史及类型化配置／来源投影；第 5 包仍负责 R2 统一验收。

[第 3 包配置语义](r2-configuration-semantics.zh-CN.md)已补齐原生配置数据／绑定与完整来源回读；R2 的受验证载体组合见第 4 包，仍需第 5 包总验收。

[English](r2-execution.md) · [论文里程碑](paper-refinement-roadmap.zh-CN.md)

R2 要把论文约束连接到实际的托管调用。**R2 仍在推进中。** 下列合同已经用于
Rust 和 Node 宿主，补齐了载荷、登记和结果传递的缺口；它们尚不构成整个宿主的语义
refinement，也没有证明任意插件回调满足 Component 合同。

[第 2 包：宿主／Node 组合](r2-host-composition.zh-CN.md) 已将实际 Node-API 弱引用、
Fiber 绑定与回调 claim 接入受验证所有者；静态强类型导入和共享 Episode 访问也检查
真实归属。配置语义与受验证载体的生产步骤组合分别见第 3、4 包。当前证据以链接开发记录的源码
指纹为准；下文历史检查点不自动覆盖改动后的源码。

R2 第一函数包将完整存储的**标量／强类型混合 root 或 Child 程序体**连接到完整载体上的
操作／continuation／inverse 定律、实际声明读写、失败来源、混合清理及真实调用返回。
包含 `Plugin::native_function`、可运行的冲突／重试示例、内核／宿主验收案例和四个新增规范负例。
见[交付范围与审查路径](cases/managed-functions.zh-CN.md)。

当前源码的开发验收由 [development-report.json](development-report.json) 及其源码指纹记录。
定向负例不等同于全量负例或发布验收。R2 三个部分完成项仍保持原状态：
本包不包含任意回调语义、别名的无条件独立性、完整 Node／配置含义或整个宿主的论文步骤组合。

下文各批次及其计数是历史检查点，过去的待验收项和通过结果不覆盖当前源码绑定的记录。

前一批次把真实强类型清理请求、读取／恢复和确认接入完整的中间执行历史，见
[强类型清理区间](#强类型清理的请求读取和确认)。

前一批次补齐非标量载荷替换与实际清理队列的组合，见[可恢复的强类型载荷替换](#可恢复的强类型载荷替换)。R2 仍在进行中。

## 当前收口状态

前一批次把真实非标量共享载荷存储、替换及可用性检查连接到同一原生执行，见
[共享强类型载荷](#真实执行中的共享强类型载荷)。

前一批次对真实已记录原生观察的每个提交分类，包含未登记 inverse 义务，并接入实际
快照和 root／Child 返回。见[完整记录分类](#已记录原生观察的完整分类)。

前一批次把状态归属连接到 61 个真实修改方法，并从实际创建认证完整共享状态历史。
见[状态连续性](#实际调用与交错中的状态连续性)。

前一批次把效果状态直接放入 `Execution` 的所有权不变式，真实初始化／退休不再需要
调用方提供条件式 Journal 归属前提。见[共享效果状态](#execution-直接拥有共享效果状态)。
R2 的三个部分完成项和原有退出条件保持不变。

上一原生身份批次通过 **9 项定向 Verus 检查、89 项 Rust 回归、805 项 Node／Loader
回归和 2 项严格负例**，以及格式和全工作区全部目标／特性的严格 Clippy。全部
**299 个规范锚点**通过预检，见[受验证分配](#受验证的原生身份分配)。此前切片计数
属于历史证据，不作为改动后源码的新通过结果。

上一 Node 捕获祖先路径切片通过 **179 项定向 Verus 检查、29 项 Rust 回归、
805 项 Node／Loader 回归和 2 项严格负例**，以及格式检查和全工作区全部目标的严格
Clippy。实际 JS 回调持有不透明原生路径；受验证构造器保持准确所选父前缀，等待查询
使用完整捕获路径，包括已完成条目之后仍存活的祖先。
见[祖先路径合同](r2-node-execution.zh-CN.md#捕获的回调祖先路径)。

每个负例要求新的匹配正例、完整突变体编译及准确函数／错误类型／源码锚点拒绝。
全部 **297 个规范锚点**通过预检。此前一次并行运行有五项超时取消；构建和证明完成后，
最终整套 Node 回归在断言、并发度和超时限制均不变的情况下通过。这次本地复跑本身
不确定这些延迟的原因。完整开发、全内核证明、全量负例、发布及 R2 语义验收仍待完成。

上一 Loader／原生归属切片的 **86／77／2／8**（证明／Rust 回归／文档测试／负例）
属于历史证据，不代表当前源码重新通过这些检查。配置工厂、RuntimeAccess 归属与联合
快照仍然保留，见[归属合同](r2-configuration-execution.zh-CN.md#loader-运行时归属与联合观察)。

前一源／配置批次的 **244／60／6**（证明／回归／负例）及更早配置 Journal 批次的
**171／56** 保留为历史证据，不累加为当前源码的验收结果。

此前源 checkpoint 批次通过 **68 项定向 Verus 检查、55 项 Rust 回归和 4 项严格负例**，
以及格式检查和全工作区全部目标的严格 Clippy。真实 Loader 的源 checkpoint 已由
受验证代码持有，更新来自已处理的保存文档，原始审查票据在 I/O 全程保持不变。
见[源 checkpoint 合同](r2-configuration-execution.zh-CN.md#从真实保存推导源-checkpoint)。
负例要求新的同范围正例、完整突变体编译和指定函数的准确合同失败。这是定向证据，
不是完整开发、全量负例、发布或 R2 语义验收。此前 Node 策略源码的 152／81／20／3
以及函数返回源码的 592／139／5 结果保留为历史证据。

真实有限 Value／Service 返回现在会在记录 Call 的同一个 Journal 提交中，核对实际
写入、逆操作登记和失败凭据。每条本地凭据都严格早于返回，外部历史保留各自身份。
详见[函数返回合同](r2-function-semantics.zh-CN.md#将真实效果接入实际调用返回)。
上一轮配方历史的 282／128／2 数字仅描述当时的源码。

真实登记配方现已接入值／工作／清理共用的 Journal。带类型的注册、替换、移除及
回调／Value／Service root 返回记录，将返回的调用与安装版本和真实 native Episode 对应；真实调用
路径同时具备完整投影和安装版本来源证明。见
[配方历史合同](r2-configuration-execution.zh-CN.md#共同执行历史中的真实登记配方)。
这推进了原生函数与历史的组合；任意 Component 含义及完整 native／Node／配置解释仍未关闭。

实际配置采用已进入受验证原生批次：完整预检、准确的新旧函数体和真实元数据返回，
保持活跃 Episode／发布值，拒绝时不留下部分修改。见
[批量采用合同](r2-configuration-execution.zh-CN.md#实际登记配方的完整批量采用)。
一般 Component 成员资格仍未关闭；配方记录已按上文接入 Journal。

从源条目到计划的实际遍历也已进入受验证内核。真实 Loader 使用完整的父先子后结果，
子条目使用其父级实际返回的上下文；回调、配方及失败结果均有准确来源。详见
[规划合同](r2-configuration-execution.zh-CN.md#从源条目到完整计划的实际遍历)。
schema／模块／上下文含义及完整 Component 组合仍未关闭。
上一轮采用批次源码通过 169 项配置范围定向证明及 2 项底层依赖合同、81 项 Rust 回归和全工作区严格 Clippy。完整开发、R2 语义验收和本批次负例验证仍待完成。

实际配置树、原生 allocation、结构阶段顺序和恢复结果提取已接入生产 Loader；
真实保存文档、I/O 阶段返回以及修订／运行域票据也已接入受验证所有者。见
[配置审查路径](r2-configuration-execution.zh-CN.md#结构性协调与原生-allocation-证据)。
当前配置身份／移除／重建批次采用定向证明与编译／lint，新增运行／负例和完整验收待集中执行。
见[准确合同范围](r2-configuration-execution.zh-CN.md#父级局部身份与完整结构派发)。
前一份[开发记录](development-report.json) 对应其中保存的源码指纹，不代表后续改变后的工作区。下文 961／226／5 等数字属于上一份源码的历史批次，
不能自动用于当前源码。历史百分比是工作量规划估计，不能用来推算剩余时间或论文证明覆盖率。

真实递归 group/include 展开已连接完整载荷／顺序及读取来源推导，文件加载与保存预检
使用同一实现；祖先链无环和总深度有界已检查，真实解析 checkpoint 在提交前保留。见
[源展开合同](r2-configuration-execution.zh-CN.md#具有读取来源的-group-与-include-展开)。
这尚未关闭分组组件效果函数或源文件保存语义。

R2 尚有三个实质性缺口：受验证标量／强类型有限函数以外的函数与效果解释、完整 Node 对象／Fiber／HMR 解释及其与
native／配置轨迹的组合，以及 group/include 与源投影／合并到配置语义的连接。全量检查通过也不自动关闭
这些义务；完成条件和四个集成义务保持不变。

生产 Node 协议已具有自己的连续受验证历史，连接生命周期、publication 句柄／版本、租约与
availability；实际请求、替换和回复序列证明 ABA 旧结果拒绝，动态控制变化保留明确分类。
保留的 admission、真实状态／错误载荷和旧回复拒绝也已接入同一历史，区间证明将保留与释放
关联到真实 Begin。见 [Node 审查路径](r2-node-execution.zh-CN.md)。剩余 Node 工作是 JS
对象／Fiber／函数／HMR、回调派发／祖先列表及与 native／配置历史的连接。
实际 callback scope、等待结果与撤回后的 publication 选择已进入同一历史；释放清单由真实
registry 构造，有限历史定理证明 publication／scope 来源及 scope 身份不复用。
真实回收队列与交付筛选也已进入同一历史：返回批次具有写入／释放来源、完整入队和当前
槽位无引用保证；JS map 的实际删除仍属于外部适配层。
实际 Node 读取也已进入历史：从执行推导保留租约仍有效，已提交／清理回读具有真实
Begin／捕获来源，返回句柄具有只读 context 解释；这不解释 JS 对象内部的操作。

实际 parent／接口状态和动态声明归属也已进入同一历史；发布准入及完整 provider 交接
循环使用受验证的真实参数／结果，包含释放受阻与部分失败。见
[接口审查路径](r2-node-execution.zh-CN.md#实际接口与动态-provider-交接)。
此代码／证明批次使用定向验证；上一份开发报告不覆盖改变后的源码。新增运行／负例证据
和完整集成验收仍待执行。

## 剩余交付工作包

下列工作包细化既有三项开放的执行义务，以及 `paper-refinement-plan.json` 中的
`configuration` 工作包。它们不替换已记录的六个 R2 工作项状态，也不改变里程碑退出条件。
这里列的是待完成的集成工作，不是已完成证明。

| 工作包 | 代码与证明交付物 | 关闭条件 |
| --- | --- | --- |
| R2-A · 可扩展效果 | 在受管效果入口连接实际参数、读写范围、结果和返回的 inverse | 新原语提供经过检查的效果／inverse 定律，并用于真实调用；调用方不提供预期结果 |
| R2-B · 函数字段 | 解释实际保存的根、continuation、Child 程序及累积 inverse | 实际代码和 receipt 在完整声明载体上具有对应含义，包含失败定义域 |
| R2-C · 共享生产状态 | 盘点字段、所有者、修改入口，组合 runtime、execution、共享 episode、服务槽、Child 和清理 | 每个相关观察都有解释，每次修改保持共同不变式，覆盖逃逸句柄和迟到回复 |
| R2-D · 宿主接入 | 组合原生／静态策略、Node 值句柄、publication 版本、租约、HMR 和动态接口 | 每个真实边界接入共同解释或明确扩展，保留参数／结果和版本来源 |
| R2-E · 逐步对应 | 覆盖每个受管入口的成功、拒绝、取消、失败和重试 | 每次转换对应论文步骤、保持完整相关观察，或满足明确扩展规则 |
| R2-F · 联合执行历史 | 组合交错执行中的控制、值、函数、Child、清理和版本历史 | 从真实初始状态及实际执行构造连续源轨迹，包括失败前缀 |
| R2-G · 运行与负向证据 | 实现期间记录场景，随后集中实现必要的集成回归和合同突变 | 故障案例走真实调用者，选定的可编译突变由指定合同拒绝 |
| R2-I · 配置工作流 | 将父作用域内的条目身份、group/include、模块／配置处理、更新、恢复及保存结果连接到生命周期动作 | 被接受的配置变化作用于准确的注册组件；失败／取消保留真实恢复输入，部分完成不误报为已提交 |
| R2-H · 集成验收 | 相关实现与证据齐备后，运行并记录完整开发检查 | 既有 R2 义务和配置集成都已关闭，且证据绑定同一份源码 |

配置工作包原本就分配给 R2。第 81 项的六字段记录已形式化，但 `Entry::as_paper_entry`
只投影模块已解析的命名叶子，拒绝 group、include 和带子节点的条目；这个局部投影不证明
整个 loader 事务。解析、模块执行及外部持久化结果保留明确边界合同。

按[实现批次流程](paper-refinement-roadmap.zh-CN.md#实现批次与集中验收)推进：先建立 C 的状态清单与
E 的入口清单，组合 A/B/C 及原生 E/F 路径，再接入 D/I 及其步骤／历史对应。
G/H 待验收时，R3/R4 可以使用已经建立的合同继续实现。待补场景记录调用者、用户保证和
预期故障即可；集成时集中补测试与故障演示，再执行完整检查。必要验收证据延后完成，
不能删去；G/H 在实际完成前保持待验收。

[生产状态清单](r2-state-inventory.zh-CN.md) 现记录原生所有者、修改入口、剩余语义边界
和待补集成场景。首个 A/B 实现将可扩展标量计算接入真实受管值路径，详见后文。
这是实现进展，还不是 R2 集成验收完成。

## 历史交付进度估算 — 2026-10-16

**此前工程估计为 82%（规划区间 78–88%）；保留作规划历史，不作为当前完成度。**
按退出条件审查，仍有三个工作项为 partial；不能由更多检查通过推算新的完成百分比。
上轮加权估计为 80%；
这里不是“已证明论文条目”的比例，也不改变六个正式工作项、四个开放集成义务
或 R2 的退出条件。下表按交付工作量作审查判断，不按证明数量计分；代码／证明占
90 分，验收占 10 分。

| 工作包 | 权重 | 当前计分 | 主要剩余交付物 |
| --- | ---: | ---: | --- |
| A · 可扩展效果 | 10 | 9 | 标量载体之外的一般效果与声明对象读写范围 |
| B · 函数字段 | 15 | 14 | 一般回调／异构效果程序体与原始载体上的完整 Component 组合 |
| C · 共享状态 | 15 | 14 | 静态上下文输入、Arc／Weak／mutex 关联、不透明槽内部及其余宿主观察 |
| D · 宿主接入 | 10 | 7 | JS 对象／版本关联、动态接口和 HMR 接入共同解释 |
| E · 逐步对应 | 15 | 14 | 剩余受管入口及失败分支在完整观察下的分类证明 |
| F · 联合历史 | 15 | 14 | 连接函数、Child、值、控制、清理与版本的单条连续轨迹 |
| I · 配置 | 10 | 6 | 条目展开、结构性生命周期动作、重建快照、持久化及配置联合历史 |
| G · 运行／负向证据 | 5 | 4 | 已记录的新场景和由命名合同拒绝的可编译突变 |
| H · 集成验收 | 5 | 0 | 全部义务关闭后，绑定最终源码的完整开发记录 |
| **合计** | **100** | **82** | **R2 仍在进行中** |

原生 publication／owner 历史现已接入实际共同轨迹，带有完整类型化索引和同一读取区间内
的 episode 观察（此前 C 增加 1 分）。槽位批次连接了实际受管 publication／import 槽与
捕获提交，之后的句柄／控制、上下文及 scope 批次接入实际状态、不可变 Begin 元数据、登记 realm 与回调作用域。
此前声明访问批次将真实标量调用及有限函数指令接到生产对象载体，B 增加 1 分；剩余工作包未关闭。
本轮多服务函数体补齐整段声明检查、实际跨服务分支和失败前缀历史，B 再增加 1 分。
本轮别名／效果批次连接原生声明准备、真实输入到提交的因果关系，并建立带条件的论文映射，A 增加 1 分。
本轮存储函数批次接通登记多服务 root／Child、完整有限动态解析解释和真实 inverse 队列，B 增加 2 分。
配置批次增加实际更新／Future 顺序、原生目标守卫和提交／恢复守卫，I 增加 2 分。
代码／证明部分为 **78/90，约 87%**。仍有 12 分实现工作，主要是一般函数／效果组合及
Node／配置集成；验收单独计算。此前天数是暂定规划预算，日历工期需要结合这些剩余路径重新估算。
当前最大的剩余风险是异构回调／效果解释、Node 对象／版本语义，以及配置身份与
实际动作之间的对应。继续增加原生标量局部合同，不能视作这些工作包已经关闭。
完整宿主观察组合和一般论文步骤组合仍需实现与最终验收。


## 实际配置更新与恢复协议

Loader 将真实更新计划放入受验证的 `Configuration`／`Batch`；`ConfigUpdatePlan`
用受验证的 `Reversible` 保存真实正向／逆向 Future。原生目标绑定运行域、组件 ID、
激活代次和配方版本；实际轮询结果驱动正向推进和逆序恢复，提交／恢复不能绕过待办工作。
详见[论文到代码的审查路径及剩余边界](r2-configuration-execution.zh-CN.md)。

上一批次源码通过 **961 项选定 Verus 检查，0 错误**，并完成整个内核 crate 编译；
**226 个 Rust 测试**通过，含 5 个新配置／目标案例。工作区全部目标／功能的 Clippy、
拒绝警告的 Rustdoc、格式与 diff 检查通过。5 个严格负向对照均通过匹配正例和整个突变体
编译，再由准确命名的运行合同拒绝。全部 **259** 个正式突变／诊断锚点通过预检；
49 个负控工具测试及论文分配／审查／覆盖检查通过。

当时**未运行**整个内核证明、完整开发／R2 验收、全部负控与校准、Node 运行测试、性能测试及
发布／平台检查。当前工作区验证以新的完整开发记录为准；R2 语义验收仍单独开放。这是绑定本批次最终源码的定向开发证据。

R2-I 仍为部分完成：条目展开、结构性生命周期动作、
重建语义、持久化及共同配置／Node 历史仍需组合。四个集成义务未关闭，也没有扩大全文证明声明。

## 存储多服务函数与完整有限程序体解释

`Plugin::native_service_program` 将完整程序体存入 `Body::Services`。
受验证的原生 root／Child 调度器读取实际配方版本，在签发 root 前核对全部登记键，
然后依据实际结果结算。每条操作捕获当时的 Begin 服务槽。
`service_composition` 对所有解析安排证明语法成员关系，并用带 Journal 的对象地址
解释完整的实际成功／失败前缀；`service_stack` 将严格逆序栈与真实保留队列对应。
详见[论文到代码的审查路径与边界](r2-function-semantics.zh-CN.md)。

有限登记路径的程序体组合现已接通；一般回调、异构效果、原始载体上的完整 Component、
剩余 Node 观察及配置流程仍未完成。正式 R2 状态与四个开放集成义务保持不变。

历史存储函数批次的定向验证通过 **921 项 Verus 检查，0 错误**，并完成整个内核 crate 编译；
**166 个 Rust 回归测试**通过，其中新增 5 个集成场景。交错执行示例、工作区
Clippy／Rustdoc、格式及 diff 检查通过。5 个严格负向对照均先通过相同选择范围的正向证明，
再完成整个突变 crate 编译，并得到准确命名合同的拒绝：替换存储操作、丢失 Journal 身份、
解释中的 inverse 顺序错误、实际清理栈 FIFO，以及丢弃最终失败。
全部 **254** 个正式突变／诊断锚点通过预检；这不是完整负向证明结果。

真实等待队列现在准确追加记录的指令 token。清理派发导出新恢复动作的 LIFO 选择和
已选重试票据的保持；`next_queued_inverse` 将实际派发连接到最后一个保留前缀 inverse。
失败结果传递被抽取为实际调用的 `Report::failed`，对应负向对照能准确拒绝丢失真实失败，
不用展开无关的轨迹不变式。

**未运行**整个内核证明、完整开发／R2 验收、全量负向与校准、Node 运行测试、性能测试以及
发布／平台验收。后文较早章节记录历史批次，其数量不会自动成为后续变更源码的验证证据；当前配置批次的结果见上方。

## 原生可扩展效果与别名感知的论文映射

原生 `update_reversible_with` 现在调用
`capture_native_effect → Capture::prepare → apply_native_effect`。第一个入口
从真实 Begin 声明解析 provider／槽位／对象，保留 root 或效果组身份。计算在宿主
和值锁外执行；落地时重新检查生命周期／work／队列身份、准入以及捕获的值／深度，
再登记真实 inverse。与确切共享 Episode 分配的关联仍由普通宿主维护；数值身份
不能单独认证彼此独立构造的宿主实例。

私有准备结果现在保留**实际输入读取**的证据。每次提交或拒绝都在该读取检查点之后；
本域读取还包含捕获槽位的选择提交。溢出、计算拒绝、输入过期在拒绝事件处保持
整个 Journal 记录状态和待登记 inverse 义务，其他写入仍可穿插。计算期间换槽
不会重定向这次计算或它的 inverse：二者仍指向最初捕获的对象。

| 论文约束 | 验证合同 | 真实实现连接 |
| --- | --- | --- |
| 定义 8：返回 inverse 恢复输入 | `effect::operation`、`managed_step` | 实际计算结果、前后态和清理队列持有的 inverse |
| 定义 29 式 (31)：单绑定操作 | `single_key_refinement`、`single_key_effect` | 实际写入检查点；条件是所选名称仍指向该对象，且被观察映射内没有另一个当前别名 |
| 定义 30：由结果选择后续步骤 | `terminal_member`、`general_semantics` | 内置与可扩展效果共用对象身份为键的 library，保留真实 continuation 和严格 inverse |
| 与定理 47 对应的 R1 严格独立性解释 | `allocation_independence`、`Write::disjoint_from` | 同一 Journal 内不同真实对象；包含前向／逆操作生成的序列及结果／continuation 稳定性 |

`targets` 从真实本域受管槽位提取解析关系；`production_value` 更新**全部当前别名**，
`production_replace` 解释独立的槽位解析变化。不透明和异域项仍在完整服务投影中
明确保留，但不进入这个本地标量映射。`operation_agrees` 将固定操作枚举接到同一
一般 `ScalarEffect` 模型。

这里存在实际兼容边界：式 (31) 保持其他键不变，而 `other_alias_changes` 证明
成功受管写入的另一个别名会违反该字面单键解释。别名感知投影是明确扩展；
`single_key_refinement` 在所列条件下恢复论文步骤，包括失败及任意一致恢复输入上的
inverse。没有增加运行时别名禁令，也没有假定虚假的独立性。这是实现解释的条件，
不是对满足自身前提的论文陈述的反驳。

受支持的可扩展标量族已连接原生声明／准备／提交。任意有副作用的回调、其他可变
值载体、完整 root／Child 后续函数成员资格、动态多次调用的组合，以及 Node／配置
集成仍属于 R2 剩余义务。同一对象上的两个操作尤其仍需各自的独立性凭据。

本轮最终源码的定向验证：**890 项选定 Verus 检查**、0 错误、完整 crate 编译，
**161 项 Rust 回归**、交错示例、禁止警告的工作区 Clippy／Rustdoc 与格式／diff 检查通过。
3 个新增贯通回归覆盖换槽后保留旧目标、错误 owner／输入过期／关闭拒绝，以及真实 Child
的别名、条件双分支、同宿主重入、溢出、panic 与 inverse 清理。
**5 个严格负例**通过同源正例、完整突变编译和精确命名合同拒绝：别名单绑定条件、
实际输入读取的因果关系、owner 准入、过期错误分类、丢弃 inverse。前两者修改证明
信息，后三者修改运行行为。全部 **251 个**规范突变／诊断锚点与 **49 项**检验框架
回归通过。**未运行**整内核证明、完整开发／R2 验收、全量负例与校准、Node 运行回归、
性能或发版／平台验收。下文此前批次的结果是历史证据。

审查：[`native_effect.rs`](../crates/cordis-kernel/src/native_effect.rs)、
[`value_alias.rs`](../crates/cordis-kernel/src/value_alias.rs)、
[`scalar_effect.rs`](../crates/cordis-kernel/src/scalar_effect.rs)、
[`value_access.rs`](../crates/cordis-kernel/src/value_access.rs)。

## 多服务原生函数体与动态访问范围

`Setup` 和 `AsyncSetup::run_service_program` 可以执行多服务有限函数体：每条指令
包含带类型的服务键、标量操作，以及由实际结果选择的 continuation。宿主用实际
context 解析键；验证内核在第一次写入前，检查**整个函数体**是否符合真实 Begin
所有者的声明，包括本次不会走到的分支。向后或越界跳转会被拒绝。普通 root、Child
回调和动态效果组共用 `Execution::run_service_program`。

每条指令重新捕获当前槽位，执行真实操作，并在进入下一条指令之前把 inverse
登记到实际接收队列。后续溢出或服务读取失败会返回实际程序位置，保留成功前缀的
全部 inverse、连续 token，以及调用前已有的队列前缀。计算拒绝还携带被擦除的
真实捕获对象和拒绝事件证据。槽位替换后，清理仍恢复当时捕获的对象。

同一 Journal 的连续调用携带上一条完成收据；当清理队列也在该 Journal 内时，
收据包含 inverse 登记。`join_causes` 在真实 Journal 读锁下确认该收据和当前槽位
选择收据。`source_trace`、`failed_trace` 将成功调用及最终被拒绝的计算放入实际
连续历史，保留调用之间的分配、槽位替换、其他写入和生命周期事件。拒绝保持
记录中的状态与待登记义务。这些证明信息会被擦除，并非运行时审计日志。因果连接
增加一次 Journal 读锁获取；本轮不声称带来性能提升。不同 Journal 的服务仍可使用，
但保留各自历史，不虚构跨域全序。

`Report::production` 从实际对象分配映射解释每一步。`successful_footprint`
记录捕获槽位／对象的读取及成功写入；被拒绝的计算另有捕获和收据证据。
`affected` 从**各次实际写入位置的全部当前别名**推导影响范围的并集，`frame`
证明本函数体的这些写入保持范围外的服务观察。它不保证整个期间没有其他并发
写入。这个有效别名范围是证明投影，不是新增的运行时权限。

关键边界是：声明的服务名授权调用，但别名可能把影响暴露到另一个名称下。
执行器不会拒绝已有的别名插件，也不会默认为不同声明名称彼此独立。
`Program::component` 证明有限函数体在既有 R1 有限标量、独立端口载体上的性质；`interpreted`
解释真实分配对象上的调用。上文别名／效果部分现已给出明确扩展和带条件的单键映射。
完整多次调用／root 组合、任意回调／Future、其他值载体、不透明对象以及
Node／配置组合仍未关闭。新多服务 API 仅支持原生宿主；已有单服务 API 的静态
宿主路径保留。已登记的单服务 root 函数体继续可用；新增有限子函数体由实际普通
回调调用。

审查入口：[`service_program.rs`](../crates/cordis-kernel/src/service_program.rs)、
[`value_access.rs`](../crates/cordis-kernel/src/value_access.rs)、
[effects](paper-refinement-map.md#effects)、[components](paper-refinement-map.md#components)。
B 工作包从 11/15 推进到 12/15，没有正式集成义务因此关闭。

别名／效果修改前的多服务批次历史证据：**832 项选定 Verus 检查**、0 错误、完整 crate 编译，
**158 项 Rust 回归**、交错示例、禁止警告的工作区 Clippy／Rustdoc，以及格式／diff
检查均通过。4 个新增贯通场景覆盖跨 provider 分支与溢出、未选分支／realm 声明检查、
真实效果组队列，以及 Child 的别名、槽位替换、外部 Journal 和失败前缀清理。
**5 个严格可编译负例**通过同源正例、完整突变编译及命名合同拒绝：4 个新增声明／
前缀／因果／累计范围控制，以及修正旧函数定位后的既有 continuation 控制。
其中因果与累计范围突变改变被擦除的证明信息，不改变运行行为。全部 **248 个**
正式突变／诊断锚点及 **49 项**检验框架回归通过。**未运行**整内核证明、完整开发／
R2 验收、全量负例与校准、Node 运行回归、性能或发版／平台验收。
该批次 R2 工程估计为 **77%（73–83%）**，未改变正式论文或集成状态。

## 声明访问与生产函数步骤

`AsyncSetup`／`Setup::update_reversible` 和 `run_value_program` 的原生路径现调用
`Execution::apply_native_value` 与 `run_native_value_program`。内核直接读取真实
Begin 中的 owned／imported 服务，核对声明端口并保留实际选中的对象。普通 root／Child
回调、动态效果组共用这些入口；已登记有限 root／Child 也委托同一程序入口。
新增 `observe_reversible` 通过受验证服务选择返回真实标量快照与 Journal 检查点。

`access::Footprint` 分别记录所选槽位的读取、保留对象的读取和对象写入。Cordis 声明
授权服务访问，这里没有新增独立的只读权限系统。`access::Write` 连接声明所选对象、
真实 forward 事件、实际结果与入队 inverse；`Report::production_steps` 对有限程序
每条成功指令建立同样联系，包括失败程序保留的成功前缀和实际接收 inverse 的清理组。

输入状态直接取自写入位置的**真实 Journal 记录**，由 `access::objects` 提取。
`interpret` 推出完整本域对象映射上的 dependent-grammar 操作，不再由调用方提供
“一致初始表”。`primitive_theory` 在完整标量分配载体上证明操作／inverse 定律。
`project_value_step` 再把每次写入提升到真实 owned／imported 服务映射：该对象的所有
当前别名一起改变，其他观察保持。交错写入、槽位替换及生命周期事件仍留在共同历史中，
没有把整个回调区间说成原子操作或没有干扰。

真实快照获取和受管写入传递擦除的槽位选择凭据：同域读取包含捕获时的槽位提交；
成功写入严格发生在该提交之后，并保留它的真实历史前缀。程序指令在登记实际 inverse
前保持同样的因果联系。替换可以改变当前槽选择，但已捕获对象与 inverse 不改目标。
跨 Journal 引用保持明确边界，不虚构共同因果顺序。普通构建会擦除这些凭据和历史。

**剩余不确定性：**两个端口互为同一对象的别名时，只声明其中一个，不能推出另一个
不受影响。`declared_frame` 明确要求建议的端口写入集合覆盖真实别名闭包；这个条件
尚未从插件声明自动推出。上面的多服务执行器会逐步推导实际别名影响范围；将其映射到
固定声明端口载体时，仍需这一条件及动态解析语义。原生 `update_reversible_with` 现已
连接声明捕获、实际输入准备与受检查落地，详见上文；完整函数组合和其他效果／值载体仍待完成。上述调用没有证明任意回调／Future
程序体、不透明载荷内部、静态宿主输入或普通指针／mutex 关联。

审查入口：[效果](paper-refinement-map.md#effects)、[观察](paper-refinement-map.md#observations)、
[组件](paper-refinement-map.md#components)、
[`value_access.rs`](../crates/cordis-kernel/src/value_access.rs)、
[`value_function.rs`](../crates/cordis-kernel/src/value_function.rs)、
[`native_slot_observation.rs`](../crates/cordis-kernel/src/native_slot_observation.rs)。
该较早批次把函数字段工作包从 10/15 推进到 11/15；没有正式集成义务因此关闭。
该批次的历史 R2 工程估计为 **76%（72–82%）**。

此前声明访问批次的历史定向证据：**796 项选定 Verus 检查**、0 错误、完整 crate 编译、
**154 项针对性 Rust 回归**、交错示例、禁止警告的 workspace Clippy／Rustdoc、
格式与差异检查均通过。三个新增集成场景覆盖声明读取／拒绝与失败程序前缀、真实
动态清理组，以及普通 Child 中的别名、替换和旧对象恢复。**8 个严格可编译突变**
均通过新鲜正例、完整突变编译和命名合同拒绝核对，包括 3 个新增的访问／因果／别名
控制及 5 个迁移到实际实现函数的控制。因果凭据突变只修改擦除的证明记录，不改变
运行时行为。全部 **244** 个正式突变／诊断锚点通过预检。
**未运行**整核证明、完整开发验收、全量负向回归及校准、Node 运行回归、基准测试或
发版／平台验收。后文历史证据对应各自较早的源码。

## 本域对象引用与实际服务观察

共同轨迹现在具有更强的不变式：凡是选择本域对象的槽位记录，在同一状态中都有对应
的对象记录。这个条件从真实创建／替换提交推出，不再要求调用方先提供一致对象堆。
`Snapshot::trajectory` 从空映射开始，导出每个前缀的引用完整性，覆盖并发写入、
槽替换、生命周期和清理／重试交错。

`ReversibleValue::reference` 在真实对象读锁下取得持久凭据；`Slot::new` 与
`Slot::replace` 把准确目标的凭据交给 Journal。权威历史核对来源，
`object_retained` 证明后续步骤保持分配身份和记录种类。域身份采用权威历史的资源
身份，不是宿主填写的整数。其他创建／修改入口也保持同一不变式。
替换入口先短暂读取对象，释放读锁后才进入槽写锁与 Journal；持有 Journal 锁时
不会反向获取对象／槽锁或调用用户代码。凭据和历史会被擦除，证明保留历史记录不表示
运行时继续保留相应分配。

真实 publication 与 Episode 服务表现在能在生产检查点形成完整观察。每个实际键
明确对应不透明载荷、外域槽、外域对象选择或本域对象状态。在凭据收集后发生并发
替换的本域槽，解析的是共同读取时刻的**当前对象**。外域状态不会被猜测，不透明
载荷也不会自动获得标量语义。`service_snapshot`、`service_episode_snapshot`
及 controlled/scoped 入口将这些观察与生命周期、work、清理、上下文和轮询状态组合。

`aliases` 与 `value_observation_step` 证明实际写入／恢复影响选择同一分配的所有
本域别名，其他选择保持不变。`Capture::execution_snapshot` 还保证替换后原来捕获
的本域对象仍能解析，不会把旧捕获或 inverse 改指向新对象。这些结果补齐论文值观察
及 frame 推理所需的实现前提（[审查路径](paper-refinement-map.md#observations)），
推进 R2-C/E/F；它们没有证明任意函数的声明读写范围、完整 R1 载体，也不意味着
端口名字不同就独立。

槽位／引用批次对应源码的历史证据：**774 项 Verus 检查**、0 错误、完整 crate 编译、
**151 项针对性 Rust 回归**、交错示例及禁止警告的 workspace Clippy／Rustdoc 均通过。
三个新增场景覆盖跨线程替换后的别名／旧对象清理、外域目标往返，以及混合 publication／
imports 观察；既有并发生产检查点回归也通过。**七个严格可编译突变**均被指定合同
拒绝，包括三个新的引用控制。替换对象偷换反例同时要求成功与拒绝载荷两条诊断。
全部 **241** 个正式突变／诊断锚点通过预检。尚未运行整核证明、完整开发验收、
完整负向回归／校准、Node 运行回归、性能测试或发版／平台验收。后文旧计数仅对应
各自原始源码批次。

该批次工程估计为 **75%（71–81%）**。本域引用闭包与实际服务投影已建立；一般函数／Child
解释、普通宿主指针／mutex 关联、Node／配置组合及完整 R2 验收仍开放。
不按证明数量提高完成比例。

审查入口：[`value_references.rs`](../crates/cordis-kernel/src/value_references.rs)、
[`joint_execution.rs`](../crates/cordis-kernel/src/joint_execution.rs)、
[`value_slot.rs`](../crates/cordis-kernel/src/value_slot.rs)、
[`native_slot_observation.rs`](../crates/cordis-kernel/src/native_slot_observation.rs)
及 [`native_slot_runtime.rs`](../crates/cordis-kernel/src/native_slot_runtime.rs)。


## 从真实写入连接到真实逆操作登记

每个 `Inverse` 现在携带擦除的持久 `joint::Receipt`，在真实值的 Journal 提交后、
释放值锁前取得。`Inverse::recorded` 将其绑定到原对象身份、准确的前向事件及前／后态。
凭证由权威成员产生；调用方另传一个事件序号，不能替代这份来源证据。

私有强类型入口 `Execution::register_inverse` 使用**即将存入队列的那个 inverse**
携带的凭证。`Member::update_following` 在清理队列实际使用的 Journal 锁内验证旧前缀。
当两个 owner 使用同一个 Journal 时，轨迹记录 `Change::RegisterInverse { write }`；
`joint::valid` 要求这个位置指向真实且更早的成功前向操作。登记事件仍严格执行清理转换：
追加一个有载荷的槽位及其等待 token，其他条目保持不变。

| 生产路径 | 合同导出的证据 |
| --- | --- |
| `Execution::apply_value` | `ValueAdmission::registration` 连接实际返回结果、队列内 inverse、队列身份／域及 token。 |
| `Execution::apply_prepared_effect` | 同样的连接使用真实受验证计算的事件和捕获输入；拒绝或过期的准备结果不登记 inverse。 |
| `Execution::run_value_program` | `ProgramReport::registered` 与 `registrations` 将每条成功前缀指令连接到自己的写入位置和真实队列槽位，包括后续指令失败的情况。 |
| `Execution::advance_value_program` | 游标保留最近一次成功登记及其准确 checkpoint 位置；拒绝或执行结束时保留之前的凭证。 |
| 已保存的有限 root／Child | `Function::run`、`Report::appended`、`RegisteredReport::certified` 将这些凭证从真实注册分派入口导出。 |

`Evidence::microsteps` 给出包含两端及中间交错的连续 Journal 前缀。
`Evidence::paper_write` 在既有标量载体及 key 表前提下，通过 dependent grammar
解释写入端及其严格逆函数。这些性质来自实际受管调用，不依赖另一份调用方拼装的日志。
凭证、位置及关联全部擦除；这次修改不增加运行时事件日志、事件计数器、Journal 克隆
或额外加锁。

独立对象和 standalone execution 继续可用。异域对象保留本地写入证据及 owner 的真实
登记证据，但**没有同域关联或共同顺序定理**；未接入 Journal 的队列没有联合登记凭证。
合同明确区分三种情况，不把不同历史里相同的数字位置当成同一次执行。

**这两个操作仍然可以分别被观察。** 真实写入提交现在同时生成可擦除的
`joint::Pending` 线性凭据，并在同一 Journal 的权威 pending 映射中登记责任。
`Applied::pending` 持有该凭据；有限解释器把每份凭据保留在实际 `Batch::items`
中，包括程序失败前已成功的前缀。只有实际清理队列与值属于同一 Journal 时，
受管入口才启用这份合同。

强类型登记入口把真实 inverse 放入队列，并在记录队列追加的**同一次 Journal 提交**
中消费凭据。`Evidence::pending_interval` 证明每一个中间轨迹状态都保留该次写入、
该个对象的责任，且登记后移除。凭据不能复制，也不能在消费后再次移交。
`Snapshot::pending` 与 `pending_trajectory` 在对象／work／清理轨迹之外导出
这一投影。映射和凭据均擦除，不增加运行时计数器、日志、加锁或堆分配。

这证明了上述四类受管标量路径中**已获得真实登记证据的调用区间**，包括有限
registered root／Child 结果及失败程序前缀；尚不能把两个操作宣称为论文中的原子步骤，
也不是任意 Rust 值的存活清单。原始 `ReversibleValue::apply`、异域值及未接入
Journal 的队列不生成这类受管责任。

### 由真实执行产生的返回合同

此前审查发现，`Execution::apply_value` 在成功后丢弃 `Applied`、返回 `Overflow`，
定向证明仍能通过。owner 字段相等没有描述共享值内部写入，而 tracked 资源允许被丢弃。
生产代码没有该分支。**同一个可编译错误变体现在已被实际返回合同拒绝。**

`Execution::attempts` 保存擦除的 `attempt::Ledger`。标量生产者在仍持有值锁时，
从真实提交取得凭证并追加；prepared effect 的成功、输入过期和计算拒绝也如此处理。
该生产者直接借用 owner 的可变证明记录，不接收调用方拼装的预期结果。
已准入调用必须恰好追加一条凭证：成功关联实际入队 inverse 与登记；错误必须对应
真实拒绝事件和具体错误原因。准入关闭保留整个 owner；其他错误保留所有运行时 owner
字段，同时追加擦除的拒绝凭证。work、清理、原生生命周期及有限 root/Child 合同均保留
这份历史。

| 受管入口 | 返回时的义务 |
| --- | --- |
| `apply_value` | 溢出或深度耗尽必须来自真实被拒绝输入；成功写入必须有实际入队 inverse 和登记。 |
| `apply_prepared_effect` | 通过真实凭证和准备输入／代码区分输入过期、深度耗尽、计算拒绝；成功登记对应 inverse。 |
| `advance_value_program` | 非准入错误必须对应真实 checkpoint 中被拒绝的指令；程序结束保留 owner 和上次登记。 |
| `run_value_program` | 只有准入关闭返回外层 `Err`；已准入程序失败时，登记全部成功前缀 inverse 后返回认证报告。 |

`Ledger::rejection_step` 进一步证明：真实拒绝提交的那一步保持**该凭证所属 Journal 的整个联合状态映射和
pending 责任映射**，不产生新的待登记写入，也不结算已有责任。因此该提交可解释为
保持观察不变的实现步骤。其他调用仍可在其前后交错，不能把它理解为整个函数期间冻结
共享状态。新记录不增加运行时日志、分配或加锁。

此前的生产者返回批次已拒绝“成功后丢弃并报错”的变体，其返回合同仍在本轮正向证明范围内。
这些合同限定四类受管标量入口；原始写入、外部回调副作用、panic／abort 恢复及全局终止不在保证内。
本轮证据与剩余清理义务见下文。

审查入口：[`value_attempt.rs`](../crates/cordis-kernel/src/value_attempt.rs)、
[`value_registration.rs`](../crates/cordis-kernel/src/value_registration.rs)、
[`joint_execution.rs`](../crates/cordis-kernel/src/joint_execution.rs)、
[`value_program.rs`](../crates/cordis-kernel/src/value_program.rs)、
[`value_function.rs`](../crates/cordis-kernel/src/value_function.rs)。
[混合 native episode 回归](../crates/cordis-kernel/tests/registered_value_function.rs)
组合保存的 root、直接写入、受验证计算、游标、异域对象和失败程序前缀，最后按清理顺序
恢复两个真实对象。`r2-register-inverse-omits-edge` 检查擦除的因果记录；既有 inverse
丢失反例修改实际运行时归属。`r2-managed-write-omits-pending` 和
`r2-registration-drops-pending-capability` 检查遗漏生产证明记录的实现，并要求命名合同
拒绝；不把它们描述为运行时故障。完整 R2 及全量负向回归验收仍未关闭。

## 从已派发 inverse 到实际恢复与确认

生产入口 `CleanupQueue::dispatch` 现在为每次标量清理返回擦除的
`restoration::Evidence`。它从实际选中槽取出 inverse，在受验证强类型路径内执行守卫恢复，
再确认真实结果。`CleanupGroups::dispatch` 和 `Execution::dispatch_cleanup` 同样导出身份与轨迹合同。
[`Runtime::poll_cleanup`](../crates/cordis/src/runtime.rs) 与
[静态宿主](../crates/cordis/src/runtime/static_host.rs) 都消费该派发结果，标量 inverse 在受验证调用内执行。
普通宿主诊断标志与外部回调仍需各自的语义解释。

| 实际边界 | 必须提供的证据 |
| --- | --- |
| 队列 `pop` | 真实派发凭证标明选中票据和已空出的槽；派发 inverse 等于原槽里的实际载荷。 |
| `Inverse::restore_following` | 凭证来自锁内真实 `Restore` 或 `Blocked` 提交，关联准确对象、inverse 和状态；成功快照对应同一来源及历史位置，失败返回原 inverse。 |
| 强类型确认 | 凭证关联相同票据与真实结果；成功清空槽，失败保留准确的原 inverse，并选中失败 attempt。 |
| `dispatch_cleanup` 返回 | 值报告携带上述凭证；错误或“没有动作”必须保留存活队列及其轨迹，其他队列保持不变。 |

队列和值在同一 Journal 时，`Evidence::microsteps` 在一条真实连续历史中证明
`派发 < 恢复／受阻 < 确认`，包含其间其他提交。`Evidence::paper_attempt` 将实际恢复
解释为标量操作的严格 inverse，受阻步骤保持解释后的服务表不变。既有 `retry` 合同保留
载荷并递增 attempt，后续派发取得新的凭证。新增证据被擦除，复用既有 Journal 锁，
不增加运行日志或加锁次数。

强类型标量路径现在进一步要求下述区间保证。完整宿主资源清单、共享宿主字段与一般论文步骤组合仍待完成。异域对象保留各自的真实历史；
未关联队列没有共同 Journal 中的队列区间。一般宿主回调、Node／配置组合与全局终止仍是明确边界。

## 注册 realm 与回调作用域

实际 `Context` 现在使用受验证的不可变 `RealmContext`。解析遵循登记的 key 到 realm
映射（默认 realm 为零）；`with_realm` 仅修改一个条目，`share` 选择来源上下文的
realm 并保持其他 key 不变，克隆共享不可变表。`RegisteredPlugin` 同时保留这张表与
anchor，注册／Child／Begin 合同将两者传到 `Capture` 和 `NativeContext`。
原生 `Runtime::start` 从 Begin 所有者取得上下文与 anchor，可变 `Mounted` 记账
不能另选映射。既有 publication 联合投影也纳入 realm／anchor 元数据，其保留定理
因而覆盖这些字段，直到对应 Unload。

`AsyncSetup` 现在持有受验证的 `SetupScope`，取代宿主直接填写的 group 编号。
`root_scope` 标识实际根队列；`admit_scoped_effect` 准入真实 iterator，并一并签发
origin／work／group／队列身份。`EffectRun::call_scoped` 在交给适配层闭包之前检查
iterator 身份，再传递该 scope 和真实载荷。错误 scope 原样返回 runner、参数和闭包，
不会调用它们。宿主在登记资源前检查 scope 是否属于当前 Execution。只要队列仍存活，
scope 就可用于合同允许的操作，包含允许的清理登记；队列移除后保留的历史记录不再
赋予使用权限。

生产 `plugin_execution_snapshot` 改为调用 `scoped_service_episode_snapshot`。
`SetupScope::observed` 证明这个实际 scope 指向与控制、work、服务槽同一读取时刻的
存活成员及队列，复用既有 Journal 读锁。回调仍在释放宿主 mutex 后、Journal 锁外执行。

轮询准入失败**不统一等于状态不变**：目标绑定消失或变化时，受验证协议可取消／结束
队列；被拒绝的 iterator 保持不变，且不签发回调 scope。效果请求登记
`enqueue_native_effect` 则保留独立的“拒绝时执行与载荷不变”合同。区分这两类失败，
才能让证明对应实际取消语义。

这些连接细化已有上下文、已提交依赖和 group 作用域效果义务。新 realm／域标识分配、
普通 Arc／Weak／Mutex 关联仍由宿主承担；静态嵌入输入、任意回调与槽内部、剩余
Node／配置解释及一般论文步骤组合仍未关闭。数值 scope 不认证独立构造、身份碰撞的
任意宿主。该批次工程估计保持 **75%（71–81%）**：它降低了 C／E／F 的不确定性，
不据此声称这些工作包或 R2 已完成验收。

前一版 realm／scope 源码的历史证据：**755 项 Verus 检查**、0 错误、完整 crate 编译、
**134 项针对性 Rust 回归**、交错示例及禁止警告的 workspace Clippy／Rustdoc 均通过。
新增四个贯通场景，覆盖输入修改与替换后的登记映射／anchor、宿主记账被修改后的真实
Begin、跨 Episode 的同编号 group scope，以及退休后的作用域失效。
**7 个严格可编译突变**在命名合同处被拒绝，包括四个新增 realm／anchor／scope 反例，
以及三个受影响的注册／捕获反例。全部 **238** 个正式突变／诊断锚点通过预检。
**未运行**整个内核证明、完整开发验收、全量负向回归／校准、Node 运行回归、性能测试
及发版／平台验收。下方旧证据保留为历史记录，不能替代当前源码检查。

审查入口：[`realm_context.rs`](../crates/cordis-kernel/src/realm_context.rs)、
[`plugin_registration.rs`](../crates/cordis-kernel/src/plugin_registration.rs)、
[`native_values.rs`](../crates/cordis-kernel/src/native_values.rs)、
[`setup_context.rs`](../crates/cordis-kernel/src/setup_context.rs)、
[`effect_work.rs`](../crates/cordis-kernel/src/effect_work.rs)、
[`native_slot_runtime.rs`](../crates/cordis-kernel/src/native_slot_runtime.rs)、
[`runtime.rs`](../crates/cordis/src/runtime.rs)。

## 共享 Begin 上下文与效果准入

`NativeEpisode` 现在持有 `Arc<NativeContext>`，保存真实 Begin 票据、work 域、
服务声明和已提交绑定（上面的后续批次加入登记 realm 与 anchor）。受验证的 `setup_context`／`native_context` 返回这份不可变
元数据，并保证它与既有 `Capture` 完全对应；其中没有槽位或用户载荷引用。
Episode 关闭时仍能释放槽位，逃逸的元数据继续描述旧 Begin，即使之后出现替代 provider。
元数据不代表获取资源的权限，实际 Execution 仍检查自身阶段和来源 group 的准入状态。

生产 `AsyncSetup` 持有 scope（此前为 group 编号）与 `Arc<SharedEpisode>`。同一分配里包含不可变
宿主上下文和 mutex 保护的执行状态；克隆或创建效果作用域都共享该所有者，不再向
每个句柄复制 realm 表、owner、bindings 和声明。原生归属及声明来自内核生成的
上下文；静态嵌入仍明确使用宿主提供的 `External` 元数据。

原生 `AsyncSetup::effect` 调用 `Execution::enqueue_native_effect`。调用方只传入
来源 group、新队列域和 iterator 载荷，内核自行读取 **Begin 的已提交绑定**。
成功合同标识实际新队列及原始载荷、保留全部已有队列，并保证新队列绑定与捕获完全
一致；拒绝则原样返回载荷并保留执行状态。通用 `enqueue_effect` 仍供自行提供
绑定合同的调用方使用，原生适配层不再走这个入口。

生产服务检查点现在还导出 `context_observed`。`context_correspondence` 将捕获的
Begin／work 身份连接到同一受认证时刻的实际 work 和清理成员；
`effect_context_correspondence` 将新队列的已提交 provider 连接到真实历史记录，
`committed_between` 证明后续队列、值写入、失败与重试交错保持这些绑定。
保留历史记录不表示退休 group 仍存活。这些连接细化已有定义 58／63 的已提交依赖
与迭代器合同，没有替代一般论文步骤组合。

实际 `retry_controlled_execution` 还向上导出：成功返回的生命周期清理票据可接受
回复，且不存在仍标记失败的清理队列；拒绝时不仅保留控制，还保留实际执行和生命
周期状态。这些保证来自已有受验证重试实现的合同组合。

上面的后续批次现已连接登记 realm／anchor 与回调作用域。剩余上下文边界包括
普通宿主分配／Mutex／Weak 关联、诊断及其余身份命名空间，以及静态宿主输入；五个生产分配器已接入下述受验证分配。放入同一所有者
消除了独立复制的上下文字段，但不等于增加指针身份公理，也不证明任意回调执行。
该批次 R2 工程估计仍为 **75%（71–81%）**；该批次单独不关闭正式证明义务。

该前一版源码的历史证据为：**735 项定向 Verus 检查**、0 错误及完整 crate 编译，
**87 项针对性 Rust 回归**、交错示例、禁止警告的 workspace Clippy／Rustdoc 均通过。
覆盖原生 Begin／替换、嵌套与逃逸 setup、清理重试、静态嵌入、waiter 和可逆效果。
新增 2 个场景，并扩展已有完整失败／重试／替换案例，检查保留元数据时槽位仍可释放。
7 个可编译突变在准确合同处被拒绝，包括错误上下文 owner、替换效果绑定，以及受影响
的捕获／发布／重试边界；全部 **234** 个正式锚点通过预检。
此前 kernel／driver／host 的 684 项测试通过后，只增加了最终 lint 标注；该批结果
单独保留，不借用为最终源码验收。**未运行**整个内核证明、完整开发验收、最终源码的
完整 Rust 测试集、全量负向回归／校准、Node 运行回归及发版／平台验收。

审查入口：[`native_values.rs`](../crates/cordis-kernel/src/native_values.rs)、
[`setup_context.rs`](../crates/cordis-kernel/src/setup_context.rs)、
[`cleanup_interval.rs`](../crates/cordis-kernel/src/cleanup_interval.rs)、
[`native_slot_runtime.rs`](../crates/cordis-kernel/src/native_slot_runtime.rs)、
[`runtime.rs`](../crates/cordis/src/runtime.rs)。

## Episode 归属与真实轮询控制

`Mounted` 不再独立保存 `failed`、`cleanup_failure` 和 `restart`。
`PollControl<CallbackError>` 持有真实首个错误载荷、重启意图和当前 Begin 身份，
修改以 `Control` 事件进入对象、槽位、原生生命周期、work 和清理共用的 Journal。
driver 从这个所有者读取 `poll_flags()`；availability 仍是单独的宿主输入。

生产适配层使用以下组合内核入口：

| 入口 | 对真实执行的保证 |
| --- | --- |
| `begin_controlled_execution` | 拒绝已有失败、已绑定或插件不匹配的控制；绑定实际返回的 Begin 票据、work 域与清理成员记录。共同守卫在同一时刻核对 native owner 与成员记录。 |
| `request_restart` | 检查真实注册阶段与退休状态；只清除 setup 失败，保留清理失败、当前 Episode 与保留载荷。重启请求不代表清理完成。 |
| `retry_controlled_execution` | 先准入真实清理重试；拒绝时完整保留控制，成功才清除清理失败，并返回新票据。其 action 对应实际分配器此前的计数。 |
| `release_controlled_execution` | 先释放匹配的真实 Episode；成功 Unload 才解除绑定、清除 restart，失败保留控制及错误。 |

`control::begin_binds_actual_members` 从受认证轨迹推出 native／清理归属关系。
`Runtime::plugin_execution_snapshot` 现在在同一次读锁内核对实际控制状态、native
owner、work、清理和受管理槽位。这些实现事件接到已有生命周期规则和定义 58／63；
没有增加论文公理，也未证明一般步骤组合。错误报告保留不透明回调结果，不证明任意
回调或外部资源真的满足其报告。

原生句柄还携带真实 Begin／work 身份。在该历史批次中，初始化和退休入口拒绝
外来来源，但数字身份相同时，准确的 Journal／成员关联仍是条件式 API 前提。
[Execution 直接拥有状态](#execution-直接拥有共享效果状态)现已在真实入口消除这个前提。普通宿主的效果轮询路径另持有**指向准确共享 Episode 分配的 Weak 引用**，
在轮询、取消或转发错误前拒绝关联不符的句柄。克隆保持关联，逃逸的旧句柄不能绑定
新分配；Weak 不保活 Episode 载荷，也不通过 group 的 handle 形成引用环。
回归分别破坏来源与共享分配，独立检查两层保护。

剩余不确定性已经明确：固定的 Verus 标准库尚未提供 `Arc`／`Weak` 指针身份比较
合同。宿主身份检查是实际 Rust 代码并有回归，**不是任意 mutex 别名关系的 Verus
证明**；没有为此添加未经证明的身份公理。构造器、不可变来源、受验证转换及当前
状态投影在明确前提下成立。完整 `AsyncSetup` 上下文解释、通用载荷／槽位内部、
回调语义、调度以及 Node／配置组合仍未闭合。该批次 R2 仍为 **75%（规划区间 71–81%）**，
这是 C／E／F 内部的工程进展，不表示额外工作包关闭或论文证明覆盖率。

此前 Episode／控制批次的源码通过 **723 项定向 Verus 检查**、0 错误及完整 crate 编译；kernel、driver
和 Rust 宿主启用全部 feature 后的 **682 项单元／集成／文档测试**通过，其中新增
5 个场景。交错示例、禁止警告的 workspace Clippy／Rustdoc 和格式检查通过。
4 个可编译突变在指定合同被拒绝：重启清除清理失败、绑定其他清理成员、拒绝重试
时清除失败、接受外来句柄来源。全部 **232** 个正式突变／诊断锚点通过预检。
**未运行**整个内核证明、全量负向回归／校准、完整开发验收、Node 运行回归及
发版／平台验收。这些是该批次源码的历史结果；当前上下文批次的证据见上节。

审查入口：[`poll_control.rs`](../crates/cordis-kernel/src/poll_control.rs)、
[`control_execution.rs`](../crates/cordis-kernel/src/control_execution.rs)、
[`host_status.rs`](../crates/cordis-kernel/src/host_status.rs)、
[`native_slot_runtime.rs`](../crates/cordis-kernel/src/native_slot_runtime.rs)、
[`runtime.rs`](../crates/cordis/src/runtime.rs)。

## 真实共享句柄状态接入执行轨迹

`EffectHandle` 和 `ServiceHandle` 现在从
`host_status::HostStatus<CallbackError>` 读取**真实语义字段**。共享受验证单元持有
取消／初始化／完成标志，独占载荷所有者持有实际错误向量、首个终止错误和外部 Child
身份；擦除的线性权限连接两者。每次接受的修改都向原生
episode 既有 Journal 提交 `Host` 记录，没有另建一份影子状态表。共同记录投影错误数量／
终止错误是否存在；类型化所有者证明实际错误的追加和保留，不解释外部错误内容是否真实。

`Execution::effect_status` 将句柄绑定到已经存在的真实效果清理组。普通宿主在 Episode
mutex 下安装该所有者，随后才返回句柄。取消只记录请求，仍需调度器取消实际队列，
不能直接宣告初始化或清理完成。`initialize_effect_status` 检查真实队列已经 settled
且没有在途轮询。`retire_observed_effect` 与 `retire_effect` 通过共同的
`retire_with_status` 消费真实借出 runner，随后提交完成状态。在途工作、保留的 inverse 失败、组／domain 不匹配均原样保留 runner
和状态。成功合同还包含同一历史中更早发生的该组移除；`host::checked_completion`
证明退休组在此后的所有交错事件中持续缺席。

这里的完成是按队列清理策略退休。`RetainFailure` 要等失败解除才能退休；
`DrainConsumed` 可以在一次性回调已消费但失败后退休，同时保留错误，所以 `finished()`
不保证 `join()` 成功，也不证明外部资源已经释放。这把句柄观察接到已有的定义 58／63
迭代器／清理控制投影。新的宿主状态事件属于实现扩展，不是添加论文公理：effect
初始化不等于 owner 的 L-Finish，effect 退休不等于 owner 的 L-Unload；一般论文步骤
组合仍待完成。

服务子插件的初始化／移除和终止错误仍明确标为**宿主报告**，与受验证效果完成分开。
终止报告不设置 `finished`，保留首个终止错误，并拒绝之后的服务完成报告。服务完成接口
不能结束 effect。`EffectHandle::execution_snapshot` 和
`ServiceHandle::execution_snapshot` 核对所属域中的真实状态；静态／外部服务状态使用
独立域，原生状态与对象、槽位、生命周期、work、清理共用历史。证明历史会擦除，
不是运行时持续保留的审计日志。

效果组合操作采用 Episode mutex → status mutex → 受验证单元 → Journal 的锁顺序；
句柄独立操作采用 status → 受验证单元 → Journal。持有 Journal 时不反向获取宿主锁；唤醒、用户回调和被拒绝错误
值的析构在解锁后发生。waiter ID／waker、driver／notify 回调、普通 `Arc<Mutex<_>>`
关联、其余宿主字段和任意 root／Child 函数体保留上文 Episode／控制一节列明的边界。
准确的效果状态 Journal／成员关联现由 Execution 不变式提供；整个 Episode 的
普通共享分配关系和调度公平仍未证明。

贯通场景覆盖在途效果取消和迟到 inverse、克隆句柄的并发观察、错误组拒绝、保留失败
后的旧／新回复、真实标量干扰后重试，以及服务终止失败。**上一轮句柄状态批次**
在其自身源码快照上通过 **699 项定向
Verus 检查**、0 错误及完整 crate 编译；**198 个运行回归**（本轮新增 4 个）；交错示例；
禁止警告的 workspace Clippy／Rustdoc；格式检查。两个严格负例分别拒绝取消时直接
写入完成，以及跳过真实退休后写入完成；均要求新鲜对应正例、完整突变编译、指定合同
拒绝。全部 **228** 个正式突变／诊断锚点通过预检。**未运行**整个内核证明、全量负向
回归、完整开发验收或发版／平台验收；此前计数属于各自原始源码。该批次 R2 仍估算为
**75%（规划区间 71–81%）**，没有额外工作包被标为关闭。

审查入口：[`host_status.rs`](../crates/cordis-kernel/src/host_status.rs)、
[`host_execution.rs`](../crates/cordis-kernel/src/host_execution.rs)、
[`runtime.rs`](../crates/cordis/src/runtime.rs)、
[`static_host.rs`](../crates/cordis/src/runtime/static_host.rs)。

## 真实 publication 槽位与捕获提交

强类型服务路径现在把**实际 publication／import 表、共享槽、选中版本及选中对象**
接到共同执行历史。`Cell::capture` 在持有槽锁时，从真实 Journal 成员取得凭据。
`Capture::wf` 要求凭据中的槽 key、来源、版本和对象与实际捕获的 `Arc` 一致；
即使是来自另一个槽的真实凭据，也不能满足这个合同。

`Capture::execution_snapshot` 将准确的选中提交包含在真实 Journal 前缀中。
即使换成外域对象，它仍使用槽所属的域。`slot::retained` 证明每个中间事件都保持
槽身份，版本只增不减。刷新槽或重新发布相同对象不会改写旧捕获。
Begin 固定共享槽引用，不是此后每个版本的槽内值。

`NativeServices::collect_slots` 遍历全部保留的 publication，包括恢复期间已隐藏的项。
episode 对应操作遍历实际 owned 与 imports。完整性由真实表推出，不接受调用方提供
的槽清单。`read_reversible` 同时导出捕获的 provider 来源与源槽。
`NativeRuntime::service_snapshot` 与 `service_episode_snapshot` 先收集擦除的槽凭据，
再在同一个 Journal 读锁区间与 native 历史、work、清理一起核对。
宿主两个 `Runtime` 执行快照入口已使用这些生产者。

每个槽锁都在 Journal 读取前释放；Journal 读锁内不等待槽锁，保持写入路径的
“槽锁 → Journal 锁”顺序。别名使用同一槽记录，最终 Journal 确定当前版本。
证据不创建可执行影子表或载荷所有者；读取检查点仍会遍历真实表并短暂取得槽读锁。
这是观察操作，不是每次插件读写新增的遍历。锁内不调用回调，也不析构不透明载荷。

此前槽位批次通过 **672 项定向 Verus 检查**、0 错误及完整 crate 编译，**194 个运行回归**、
交错示例、禁止警告的 workspace Clippy／Rustdoc 及格式检查。三个严格反例均通过：
借用另一个槽的提交、遗漏已发布槽的证据、遗漏 Begin imports。每项都有同范围的新鲜
正例、完整突变编译及命名合同拒绝。**226** 个正式突变／诊断锚点通过预检。
运行案例覆盖别名、外域槽与换值、不透明载荷寿命、隐藏 publication、失败／重试／旧回复
以及真实宿主并发检查点。本轮**未运行**整个内核证明、全量负向回归、R2 开发验收或
发版／平台验收；后文旧计数只描述历史批次，不复用为当前源码验收。

保证范围是同域受管槽。外域槽仍是明确的引用；本域槽选择外域对象，不意味着外域
对象的写入已经在本域证明。不透明 `Any` 载荷、一般效果／声明读写范围、共享宿主
标志／逃逸句柄关联、Node／配置组合、一般论文步骤组合仍未关闭，也没有证明调度公平。
剩余 R2 工作包尚未关闭，该批次工程估算保持 **75%（71–81%）**。

审查入口：[`value_slot.rs`](../crates/cordis-kernel/src/value_slot.rs)、
[`native_slot_observation.rs`](../crates/cordis-kernel/src/native_slot_observation.rs)、
[`native_slot_runtime.rs`](../crates/cordis-kernel/src/native_slot_runtime.rs)、
[`joint_execution.rs`](../crates/cordis-kernel/src/joint_execution.rs)。

## 原生 publication 与完整类型化历史

`NativeRuntime::transition` 现在用一个 `Record::Native` 同时提交真实控制状态、episode
owner、已发布端口集合、Begin 工作域、捕获的绑定／import key 及 provider 来源。Begin
只增加该 owner；Finish 只增加该 publication；Unload 移除二者。其他规则，包括 Restart
和 Retire，都保持这些归属。它们与对象写入、槽位替换、work 和清理共用同一个 Journal 顺序。

泛型 `History<V>` 继续记录完整的 `NativePublication<V>`，包括真实 `Arc<V>` 和完整 Begin
capture。擦除的位置索引把每个类型化观察对应到真实共同提交。`project_step` 检查投影；
`History::interval` 排除索引之间漏记的 native 转换。擦除的 revision 在每次 native 转换时
递增，即使控制状态不变也递增。`Snapshot::complete_projection` 证明：**该 native 成员的
每个事件**都有索引，包括初次分配和检查点尾部。调用方不能提供预期历史或 publication。

`publication_has_finish` 把每个保留的类型化 publication 追溯到实际成功的 Finish。
`publication_retained` 证明完整表与 capture 一直保留到其 provider 成功 Unload。
`native::retained` 进一步覆盖中间所有共同 Journal 事件，保证 owner／端口／来源不被
其他对象写入、清理失败或重试移除。恢复期间不可见的 publication 仍然保留，不等于释放。

`NativeRuntime::publication_snapshot` 导出类型化证据。`episode_snapshot` 在**同一次
Journal 读锁区间**核对真实 native 成员、work owner 和全部存活清理组，同时检查当前
episode owner；同域前提来自 native Begin 及受管接口的 frame 合同。普通宿主的
`Runtime::plugin_execution_snapshot(id)` 在既有 mutex 下读取当前 mounted episode，
在 Begin 前或 Unload 后返回 `None`。`Runtime::execution_snapshot` 也改用加强后的
publication 检查点。Journal 读锁内不运行回调、析构，也不获取值或槽位锁。

类型化历史、位置、revision 和历史 Arc 引用都会擦除，不产生运行日志，也不保留旧服务值。
新增原生回归在 Unload 后保留全部快照，仍能确认最后一个服务 Arc 已销毁；实际宿主回归
通过新入口观察清理失败、依赖保留、重试和最终移除。本批绑定源码的检查结果如下。

此前 publication／owner 批次通过 **648 项定向 Verus 检查**、0 错误及完整 crate 编译，**192 个运行回归**、
交错示例、禁止警告的 workspace Clippy／Rustdoc 和格式检查。三个严格开发反例均通过：
遗漏 native 提交、记录错误的共同位置、遗漏真实 episode 清理观察。每个反例都要求
对应正例通过、突变完整编译，再由指定合同拒绝；资源超限不计为通过。全部 **223** 个
正式突变／诊断锚点在当时源码上通过预检。该批**未运行**整个内核证明、全量负向回归、完整 R2 开发
验收或发版／平台验收。后文旧计数对应各自原始批次，不表示当前源码重新通过那些验收。

这里完成的是原生 publication／owner 历史合并，尚未完成整个宿主的共同解释。共同记录
投影泛型载荷，完整类型化引用仍留在有索引的历史中；没有解释任意 Arc 内部修改。
受管槽的专用连接已按上文建立。共享宿主标志、普通 mutex 关联、任意回调、Node
版本／动态接口、配置事务及一般论文步骤组合仍是剩余义务。Finish／Unload 的前提继续
由已有受验证执行协议建立；新读取检查点没有替代全局排空协议。

审查入口：[`native_execution.rs`](../crates/cordis-kernel/src/native_execution.rs)、
[`native_history.rs`](../crates/cordis-kernel/src/native_history.rs)、
[`native_runtime.rs`](../crates/cordis-kernel/src/native_runtime.rs)、
[`execution.rs`](../crates/cordis-kernel/src/execution.rs)。

## 存活清理组与受守卫约束的移除

`CleanupGroups` 现在除了持有各队列，还持有一个私有 Journal 成员。其记录包含实际
生命周期来源、存活组 ID 与队列 key/domain、分配高水位、封闭状态，以及不可清除的
已消费失败标记。成员映射直接从真实 `entries` 得到，调用方不能提交一个少列了组的清单。
`Execution::observe_execution` 在同一读锁内核对这份记录、work 与全部存活队列，
并证明它们使用不同的记录 key。

实际 `add_iterator`、`remove`、`seal` 和已消费失败更新都会维护该记录。私有 `take`
临时取出队列时不会移除成员关系；`put` 必须归还同一队列身份。这一合同继续覆盖标量派发、
异步结果、重试与 iterator 调用。

移除和封闭使用一次有明确结束点的 Journal 写锁区间，在提交成员变化前，直接核对所持队列
与权威映射。转换守卫要求：没有等待项、没有选中或已派发动作、没有 pending stage、
continuation 已结算，且所有载荷槽为空。封闭会检查**每个存活组**，不能用宿主报告的
排空标志或旧快照代替。写锁在队列／runner 载荷可能析构前显式释放；锁内不运行插件回调，
也不获取值或槽位锁。

`groups::checked_removal`、`checked_seal` 从实际认证历史提取这些守卫，并证明：已移除的
组 ID 在后续每个状态中保持缺席；已封闭所有者始终封闭且成员为空。队列记录继续保留作历史，
因此“历史中存在该记录”不再等同于“仍然持有该队列”。已消费失败标记在移除与封闭后仍保留。
这里把既有生产排空／释放条件接入共同轨迹，没有添加新的论文规则，也没有证明任意回调的
效果可逆。

此前成员关系批次通过 616 项定向 Verus 检查、0 错误及完整 crate 编译，165 个运行回归、交错 native
例子、禁止警告的 workspace Clippy／Rustdoc 及格式检查。新增原生案例覆盖已准入 stage
取消、移除被阻止、清理失败、新票据重试、成功或已消费完成、组退休及最终 publication
释放，并在步骤间观察同一 Journal。在当时源码上，221 个正式突变／诊断锚点通过预检；这不是新一轮
负向证明。待补反例包括遗漏成员提交、封闭时漏掉存活队列、复用已退休 ID。整个内核、
全量负向回归、R2 集成和发版验收仍未完成。

成员证据会被擦除，但这项改动确实增加一个 Journal 引用，并在成员／失败标记变化时增加
写锁区间，封闭时增加一次元数据遍历；这里不宣称性能提升。原生 publication／
owner 历史现已按上文合并；剩余包括共享宿主标志、一般回调／读写范围解释、Node 和配置路径。

审查入口：[`group_execution.rs`](../crates/cordis-kernel/src/group_execution.rs)、
[`cleanup_groups.rs`](../crates/cordis-kernel/src/cleanup_groups.rs)、
[`joint_execution.rs`](../crates/cordis-kernel/src/joint_execution.rs)、
[`execution.rs`](../crates/cordis-kernel/src/execution.rs)。

## 每个中间状态中的已派发清理责任

实际 `restore_value` 生产者在返回前调用 `Evidence::establish_interval`。既有返回合同现在
包含 `interval::holds`，并一直导出到 `Execution::dispatch_cleanup`。它证明：从实际派发提交后
到确认提交前的每一个状态中：

- 同一队列域、选中票据及已分配 attempt 始终有效且处于派发状态，选中载荷槽持续为空。
- 中间提交不能再次派发、重试或确认该队列的选中动作；其他对象及独立队列字段仍可变化。
- 最后的确认是该派发动作的首次完成；失败把准确的原 inverse 放回选中槽。

载荷身份来自真实 `pop` 和强类型返回合同，区间描述的是它尚未确认的**清理责任**。
恢复成功时，Rust inverse 在确认前已经被消费；定理不会把这段状态误写成 inverse 对象仍然存活。

`completed_attempt_stays_closed` 继续检查任意扩展了实际确认历史的认证快照，证明该 attempt
在后续每个状态中均不再有效，也不能获得第二次合法确认，包括同一槽已经重试的情况。
`interval::retired_at` 可从全称结论取出某一状态或提交。失败 attempt 同样已经关闭；
重试保留载荷，但必须分配新的 attempt 身份。

证明使用生产 `cleanup_step` 规则与真实 `CleanupJournal::next` 单调计数器；既有提交合同
把这些规则连接到可执行队列，不增加第二份队列、运行历史、分配或加锁。
`Snapshot::valid_history` 导出跨模块组合所需的快照封闭不变式。结果适用于任意长度的有限
真实历史，不承诺回调终止，也不承诺调度器最终会触发重试。

上一批标量清理区间工作记录了 597 个定向 Verus 证明、0 个错误，164 个既有运行回归、交错 native 例子、
禁止警告的 workspace Clippy 和 Rustdoc、格式检查及 96 个负向测试工具自检。
7 个定向控制均要求相同范围的正向证明、完整变体编译及命名位置处的精确失败：
3 个新增区间／新鲜性控制，以及 4 个既有生产者／实际写入／空动作控制。
新增控制分别在恢复前确认成功、在真实 retry 中复用旧 attempt、以及在共用协议关系中
允许旧票据复活。最后一项检查规范变更，不表示生产代码存在该 bug。
221 个正式突变／诊断锚点全部通过预检；这些负向记录不作为成员关系改动后的源码验收依据。
该批未跑整个内核、全量负向回归、R2 集成或发版验收。

审查入口：[`cleanup_interval.rs`](../crates/cordis-kernel/src/cleanup_interval.rs)、
[`value_restoration.rs`](../crates/cordis-kernel/src/value_restoration.rs)、
[`cleanup_completion.rs`](../crates/cordis-kernel/src/cleanup_completion.rs)、
[`cleanup_journal.rs`](../crates/cordis-kernel/src/cleanup_journal.rs)、
[`joint_execution.rs`](../crates/cordis-kernel/src/joint_execution.rs)。

## work 与清理接入同一轨迹

原生 Begin 在返回执行对象前，把实际 `SetupWork` 与根清理队列绑定到运行时的
Journal；之后动态创建的 iterator 队列继承同一个 Journal。每次受验证修改后，
私有成员必须与实际字段一致；遗漏联合提交将破坏 `wf`。

`WorkState` 记录生命周期来源、域、分配计数、root 状态与失败、Child／group
排队票据、已派发请求，以及接收和关闭标志。`CleanupState` 记录提交绑定、
pending／settled／cancelled 阶段、等待栈、当前票据与 attempt 计数、失败、
派发状态和真实槽位是否持有 payload。`work_step`、`cleanup_step` 描述精确变化；
payload 身份及其效果含义继续由既有强类型合同约束。inverse 失败保留原槽位，
重试递增 attempt，旧回复或重复确认不能完成当前动作。

`Execution::observe_execution` 持有**同一次 journal 读锁**核对 work 与全部
存活队列，再释放锁返回。`observe_execution_after` 还证明它延续此前同域
程序／值快照的历史。`observation_ownership` 证明 work 和每个存活清理组使用
不同记录，无需调用方拼出一个“假定一致”的快照。独立／静态执行仍明确未连接，
返回 `None`。

存活清理组的成员关系／移除和原生 publication／owner 投影现已接入上述联合合同；
完整 capture 通过类型化历史索引关联，任意 runner payload 的含义与共享宿主标志仍待解释。work／清理规则是实现规则，
仍需与完整论文上下文组合守卫。尤其是值写入和逆操作登记目前是两个有序微步骤，
尚未证明它们在所有并发观察下合成一个论文步骤。移除后保留的历史记录不代表
资源仍存活，也不证明物理释放；快照不证明任意回调终止或调度公平。

审查入口：[`episode_execution.rs`](../crates/cordis-kernel/src/episode_execution.rs)、
[`setup_work.rs`](../crates/cordis-kernel/src/setup_work.rs)、
[`cleanup_queue.rs`](../crates/cordis-kernel/src/cleanup_queue.rs)、
[`execution.rs`](../crates/cordis-kernel/src/execution.rs)。
[贯通回归](../crates/cordis-kernel/tests/registered_value_function.rs) 连接动态 iterator
分配／退休、真实 inverse 干扰失败、保留、新票据重试、旧回复拒绝和成功恢复。
`r2-joint-work-omits-commit`、`r2-joint-cleanup-omits-commit` 使用可编译突变检查
两个提交义务。完整 R2 验收仍未关闭。

## 同一原生执行域的统一轨迹

`Runtime::reversible_value(initial)` 在该运行时生命周期所属的执行域中创建
真实受验证对象。强类型槽位继承初始对象的域。对象写入和逆操作、成功的槽位替换、
原生生命周期转换，现在通过同一个 `Journal` 提交：真实锁确定顺序，擦除的
映射和持久证据提供证明。`Snapshot::trajectory` 从空映射构造连续的分类轨迹，
不再要求调用方提供一致的初始对象堆。

| 实际修改 | 联合观察及其解释 |
| --- | --- |
| `Cell::record` | 实际操作／结果／分支、拒绝、严格逆操作及阻塞恢复更新原对象条目；其他条目不变。 |
| `Slot::replace` | 同一槽位递增一次版本，选择实际传入对象的域／key；旧捕获和逆操作保持原对象。 |
| `NativeRuntime::transition` | 控制、episode owner 与 publication 投影在同一受验证 native 转换中提交；完整类型化历史具有完备索引，`Restart` 仍为明确扩展。 |

共同状态是**投影**，没有复制一份可变服务存储。Rust 句柄销毁后，逻辑成员
记录仍保留；这不是活跃分配的清单，也不能据此证明内存已回收。权威成员令牌连接日志条目与
真实锁内字段。值快照现在携带联合快照，后者的对象条目等于实际 value/depth；
游标推进和观察同时保持局部与联合历史的前缀。程序报告也携带实际目标对象的联合快照。
`Runtime::execution_snapshot` 在同域中观察真实 publication／控制条目。刷新保留实际 Journal
引用，不会仅凭域标识相等就替换历史权威来源。

`Plugin::native_value_program(name, key, program)` 现在把 `Body::Value(Function)`
直接保存进真实注册表，root 与 Child 共用此路径，不再靠不透明闭包关联有限程序与插件身份。
`NativeRuntime::run_value_root` 读取实际函数体和版本，重新检查有限代码，从**已登记的依赖**
选择首个匹配端口，再验证 Begin 分配的 owner 并准入真实 root 票据。显式依赖先于继承别名，
因此隔离 Child 使用自己的 realm；调用方不能另传替代程序、预期结果或本次调用的端口。

`Function::run` 读取该 episode 已提交的强类型槽位，将每个成功前缀的真实逆操作登记到
group 0。内核根据实际计算结果结算 root，溢出不能被确认成功。`RegisteredReport` 把结果
绑定到真实生命周期／工作票据、注册版本、代码和端口，并在现有有限标量载体及实际注册声明上
推出 root 的 Component 成员关系。普通回调保留独立的版本检查分派路径。

`Member` 现在保留最近一次真实联合提交的持久证据。`Snapshot::projection` 将每个对象的
局部事件映射到同一执行域历史中的有序位置。`ProgramReport::joint_steps` 对应实际指令、
结果与 continuation，`joint_rejection` 对应真实失败指令；`Cursor::joint_steps` 对应
交错执行的步骤。结合注册报告，得到**登记 actor／函数体 → 实际操作／结果／逆操作 → 联合轨迹**
的审查路径。位置和凭据全部擦除，不增加运行时事件计数器或日志。

这仍不代表任意 Rust／JS 回调具有 Component 成员关系，也未把完整宿主／资源含义
放进联合解释，或证明任意别名端口满足论文的声明对象读写范围与 frame 条件。调用报告能够
标识自身步骤，但还不是每个联合事件都有已证明的登记 actor。数值域分配及共享宿主 mutex
关联仍保留原有边界合同。

[交错案例](../crates/cordis/examples/interleaved_program.rs) 已使用同域对象工厂和
真实有限 root/Child，继续覆盖槽位替换、旧对象清理失败、依赖保留及重试。
新增回归覆盖部分失败回收、同域并发、错误／重复 owner、旧注册版本、Child 隔离域选择、
有限程序热更新以及静态宿主的明确拒绝。

**剩余不确定性：**解释共享 Episode 标志、泛型槽内部状态及宿主资源归属，随后组合
Node 多版本／动态接口和 loader 事务。当前联合映射包含原生控制／owner／publication
投影、对象、槽位选择、work 票据／状态、存活清理组及队列观察；完整泛型 capture 通过
类型化历史关联，其余宿主字段尚未纳入。旧 `Cursor::object_trace` 仍是保留视图定理，保留原有一致视图前提。

独立的 `ReversibleValue::new` 仍创建独立域。槽位仍可接收其他域的对象；联合观察
记录这个外部引用，`resolve` 返回 `None`，不会虚构其状态。因此本次贯通范围需要使用
新工厂，不会自动迁移旧对象，也不会自动包含另一运行时的生命周期。新原生 root
构造器的范围不包括静态和 Node 宿主。

Journal 确实增加了同步操作。锁顺序为对象／槽位，再到 Journal；Journal 不获取
对象／槽位锁，也不调用插件。历史及证明令牌均擦除，不保留运行时审计日志。
本轮没有据此证明吞吐量、竞争开销、调度公平或全局终止。定向检查也不等于整个内核、
完整 R2 或发布验收。

审查路径：[`joint_execution.rs`](../crates/cordis-kernel/src/joint_execution.rs)
→ [`native_runtime.rs`](../crates/cordis-kernel/src/native_runtime.rs)
→ [`value_function.rs`](../crates/cordis-kernel/src/value_function.rs)
→ [`runtime.rs`](../crates/cordis/src/runtime.rs) 中的
`Plugin::native_value_program` / `Runtime::reversible_value`。


定向回归源码为
[`registered_value_function.rs`](../crates/cordis-kernel/tests/registered_value_function.rs)
与 [`reversible_runtime.rs`](../crates/cordis/tests/reversible_runtime.rs)。
所选负控分别替换登记函数体、错误确认失败结果、伪造联合位置或遗漏对象／控制提交；
每项都要求新鲜正向验证、错误实现可编译，并由命名合同拒绝。
全量负控及 R2 验收单独进行。


## 优先验证高风险连接：交错 continuation 与恢复

这里首先要回答：其他插件可以在两次调用之间运行时，分别验证的方法能否
对应同一次真实执行。一个快照具有合法历史，并不能单独证明下一个快照延续了
它。生产 `ReversibleValue` 的锁内现在保留只追加的权威 ghost 历史，每个快照
携带同一对象的持久证据。带着旧检查点再次获取锁，就能证明历史前缀关系；
另一个内容相同的对象或调用方编造的日志不能替代它。历史及证明令牌在普通
Rust 执行中全部擦除。

真实 `Setup` / `AsyncSetup` API 创建的 `ValueProgramCursor` 保留实际校验过的
代码、目标对象、下一条指令和 episode/group 身份。`advance_value_program`
先检查原始所属身份与当前资源获取许可，再执行一条存储的指令。真实结果选择
后续分支，真实逆操作在返回前进入同一 episode 的清理队列。溢出保留当前指令，
可以显式重试；其他 owner 或已关闭的 owner 不能推进。丢弃游标也不会丢弃
已登记的逆操作。`observe` 可以观察后续清理尝试，但不会重新授予写权限。

`Cursor::component` 从实际存储的有限程序推出整个声明载体上的 Component
成员关系。`Cursor::interpreted_trace` 构造连续的标量表轨迹，包含其他调用者的
写入、拒绝的操作、阻塞的恢复和成功恢复。游标自身的各步出现在同一历史中
严格递增的位置，并保留真实结果选择的 continuation；这里没有拼接无关日志，
也没有假定相邻两次游标调用是一个原子操作。

运行生产贯通案例：

```sh
cargo run -p cordis-verus --example interleaved_program --offline
```

案例挂载真实父插件及 Child：Child 程序先运行一步，另一个插件写入，随后比较
选择 unmatched 分支。Child 清理撤销后续步骤，在较早的逆操作处阻塞并保留
provider；另一个插件撤销写入后，显式重试完成清理。案例同时检查其他 owner
和撤离后的 owner 不能推进游标。这是 Child/控制流程接入的运行证据，**不是
任意 Child 回调或整个宿主联合轨迹的证明**。

这个案例暴露的别名缺口由下文的强类型槽位／对象连接继续处理。原先的
单端口标量定理仍只是该投影，不能作为别名端口在完整观察中的 frame 定理。

审查路径：[`shared_value_history.rs`](../crates/cordis-kernel/src/shared_value_history.rs)
→ `Snapshot::extends` / `ReversibleValue::snapshot_after` →
[`value_cursor.rs`](../crates/cordis-kernel/src/value_cursor.rs) →
`AsyncSetup::{start_value_program, advance_value_program}` →
[`interleaved_program.rs`](../crates/cordis/examples/interleaved_program.rs)。
新增标准负控分别移除 owner 检查、跳过实际 continuation、漏登记逆操作。
开发探测要求错误实现能够编译，并在指定合同处失败；它与全量负控验收分开记录。


## 真实槽位版本与共享对象身份

生产原生服务表现在存储受验证的 `ServiceSlot` 枚举。其中 `ReversibleValue`
分支在验证过的锁内持有实际强类型槽位；非标量载荷现在使用
[受验证共享 owner](#真实执行中的共享强类型载荷)。
Rust 适配层的 `Any` downcast 根据真实载荷选择一次存储分支，没有并行的
对象影子表、重复可变值或新增的运行时身份计数器。这个 downcast 和普通
episode mutex 仍属于宿主边界。

`NativeEpisode::read_reversible` 从实际已提交 provider 读取真实槽位。
`Execution::begin_native_value_program` 在同一 owner 中组合这次读取与资源
获取许可检查，将实际代码、端口、provider、槽位版本和对象绑定到游标。
调用者不能向这个入口提供“预期 provider/版本”。之后每次推进仍登记该捕获
对象的真实逆操作。`Setup` / `AsyncSetup::capture_reversible` 暴露同样的保留
选择；版本用于诊断及溯源，不代表新增生命周期租约。

槽位中的权威 ghost 历史记录实际载荷替换，编译后擦除。`Capture::refresh`
使用自身持有的槽位并证明前缀延伸，旧版本继续对应原对象。`check_result`
只有在观察到的当前版本仍等于捕获版本时才接受回调结果；A 换成 B 再换回 A
也不会让旧回调重新有效。槽位版本记录替换，不记录对象内部写入；predicate
的真值及任意副作用仍属于外部义务。普通读取、动态 `ServiceHandle` 替换和静态 typed
slot 使用对应的受验证存储。用户 predicate 与任意载荷析构在存储锁外运行；
替换将旧 Arc 交还调用者。

`value_heap.rs` 区分端口选择与按分配身份索引的对象堆。解释由生产快照的
认证历史推出，对象身份来自这个真实快照。写入或恢复影响所有选择该对象的
端口，其他对象保持不变。槽位替换推进所有指向同一槽位的当前选择；另一个
槽位可以继续选择旧对象。此前的捕获、游标目标及逆操作不会改指新对象。
`alias_changes` 还明确证明：两个端口暴露同一被修改对象时，端口名不同
不足以支持原来的单端口 frame 结论。

这里得到的是处理别名的**保留视图轨迹**，尚不是整个宿主的统一实时观察。
`Cursor::object_trace` 仍以一致的绑定／对象堆观察为前提；它不会把不同时刻
读取的多个对象当成原子快照。上文新增的原生域轨迹通过自己的共同锁连接实际
对象／槽位／控制提交，并未改变这个旧定理的前提。因此，不能直接将按端口划分的 R1 Component／不干扰定理
套用于任意别名。R2 的共同解释仍需将声明端口映射到实际对象读写范围，并
从完整执行中推出这些绑定。任意 root/Child 函数体、不透明／JS 内部状态及
共享 episode 仍是其他开放义务。

贯通案例已增加运行中替换：实时槽位换成值 1000，Child 游标和另一个端口
继续保留旧对象。游标推进到 23，清理在 22 阻塞，重试后恢复到 10、depth 0；
新对象始终保持 1000。动态 publication 替换和换回相同对象另有集成回归。
新增标准负控分别错误接受过期捕获、替换成错误载荷、读取错误 realm。
所选开发探测要求新鲜的正向验证、可编译错误实现及指定合同拒绝；它们与
全量负控和完整 R2 验收分开记录。

审查路径：[`value_slot.rs`](../crates/cordis-kernel/src/value_slot.rs)
→ `NativeEpisode::read_reversible` → [`value_cursor.rs`](../crates/cordis-kernel/src/value_cursor.rs)
中的 `Execution::begin_native_value_program`
→ [`value_heap.rs`](../crates/cordis-kernel/src/value_heap.rs)
→ [`interleaved_program.rs`](../crates/cordis/examples/interleaved_program.rs)。

## Node 准入与保留至清理的资源

真实 `Driver::ready` 和 `NodeDriver::begin_checked` 现在调用
[`node_admission.rs`](../crates/cordis-kernel/src/node_admission.rs)。验证操作读取
真实生命周期 target、provider generation、publication 身份和已接受的检查缓存。
ready 合同是充要条件，不能用“一律不可用”来满足；Begin 也有包含实际依赖数量和
容量的精确成功条件。

获取租约所需的容量在 Begin 前检查；Begin 成功后，选中的 publication 租约分配
被证明必能成功。拒绝保持控制、动作归属、载荷、版本及 publication／lease 注册表，
不会遗留部分获取的租约。成功返回 `Admission`，其私有资源清单对应本次 Begin
实际提交的 provider，活跃租约绑定返回 setup 票据的 owner／generation。擦除后的
capture 保留真实来源值、版本和选择事实。

`NodeRuntime` 现在用私有 admission map 保留这个 owner。真实 Driver 只读资源切片，
受管释放从保存的清单构造租约列表，并检查原 domain／generation；拒绝保持资源，只有
成功释放才移除 owner。同一历史还包含 preparation、seal、失败、重启、实际完成与重试状态，
保留实际错误文本，并证明 Begin 来源、释放前保留及旧回复拒绝时的状态不变。
见 [Node 审查路径](r2-node-execution.zh-CN.md)。

控制投影证明 L-Begin／L-Unload；generation-zero preparation／adoption、checked 集合
及动态接口已显式记录。JS predicate 真值、对象内部状态、Fiber／函数／HMR 效果、其余
适配层缓存与跨运行时解释仍未闭合，因此不宣称整个 Node refinement。
缓存维持既有显式 notify 策略；准入不声称值变化后 predicate 仍然为真。

审查路径：`Kernel::{target, complete_target_facts}` →
`Availability::{ready, begin_setup}` → `Admission::{wf, value_provenance, finish}`
→ 真实 `Driver::{drive, complete}`。历史控制记录属于证明数据；capture 及其来源
值不会增加运行时历史拷贝。

## Begin 分配的 episode 归属与延迟根调用

生产 `NativeRuntime` 现在保存 Begin 实际分配的 setup 票据和工作域。不变式要求
Loading、Active、Unloading 插件恰有一个当前归属记录，Inactive 或已移除插件
没有记录，发布值必须属于该记录。根调用准入与执行、Finish、撤销、工作结算、
失败、重试和 Unload 都检查传入的 execution 或 invocation。修改不透明宿主字段
不能替换该记录；只有成功 Unload 才删除它，失败与重试保留它。

`RegisteredInvocation` 还保留准入时的生命周期票据。`NativeHost::call` 在真正调用
保存的回调之前，重新检查待完成 setup 动作、当前 generation、Loading 阶段与
退休标记，并保留原有 owner／domain／回调版本检查。因此，尚未开始执行的根调用
在撤销或退休后会被拒绝；即使复用工作域，它也不能在下一 episode 执行。本地工作
撤销同样关闭新的根调用准入。已经执行中的回调及其异步结果仍通过已有完成协议落地；
这里没有实现抢占回调。

原生连续历史现在同时观察实际归属记录、控制状态与发布值。`owner_has_begin`
证明保留的记录来自一次成功 Begin；`owner_retained` 证明在该插件成功 Unload 前
不能替换它。归属变更附随已有 Begin／Unload 控制步，准入检查和拒绝保持该观察。
这是生产执行投影的加强，不改变 R1 解释，也没有把它宣称为完整 context 对应。

审查入口为 [`native_owner.rs`](../crates/cordis-kernel/src/native_owner.rs)、
[`native_runtime.rs`](../crates/cordis-kernel/src/native_runtime.rs)、
[`plugin_registration.rs`](../crates/cordis-kernel/src/plugin_registration.rs)、
[`native_host.rs`](../crates/cordis-kernel/src/native_host.rs) 的实际检查，以及
[`native_history.rs`](../crates/cordis-kernel/src/native_history.rs) 的归纳证明。
`native_host` 与 `native_runtime` 集成测试覆盖延迟调用、退休、工作域复用、外来
execution 与成功释放；命名负向控制删除相应守卫或归属更新。

使用固定工具链复现这些运行案例：

```sh
cargo test -p cordis-kernel --test native_host --test native_runtime --offline
```

共享 `Arc<Mutex<Episode>>` 仍由普通 adapter 持有。这些检查将其提交的数字身份
对应到当前注册表，不证明锁的调度、不透明参数的含义，也不认证刻意复用**全部**
身份编号的独立原始宿主对象。共享 driver 已采用受验证的同域分配；共同命名空间的选择与普通共享归属仍依赖宿主连接。任意函数字段、
服务槽内部状态和 Node／native 联合 context 仍需对应到 R1，因此 R2 保持进行中。

## 从 Begin 保留至发布和释放的来源

每个原生 episode 现保存一个不可变、编译时擦除的 `Capture`：Begin 捕获依赖时
实际的控制状态、声明、committed bindings、provider 代次和发布槽。
`Capture::wf` 证明捕获的双向对应：某个 import 存在，当且仅当 committed binding
在当时的来源表中有可用槽，且其中保存的就是那个实际槽。
快照由生产构造器直接产生，不要求调用者提供“预期值”。

`Execution::capture_correspondence` 把这个 Begin 观察连接到当前工作与原生值 owner。
可执行修改保持同一份 capture，包括 Child／effect 准入、poll 落地、取消、清理、
重试和可逆值程序。episode 未关闭时，imports 始终等于最初捕获的 imports。
Finish 将同一份 capture 带入实际 publication，因而进入原生联合历史。
Unload 返还最初捕获的 imports，并清空已关闭 owner；清理不会按当前 target 重新抓取依赖。

值 owner 还保存实际 cleanup／work domain。发布和释放先检查它是否与传入的工作队列
一致，再改变状态。因此，即使原始嵌入刻意复用生命周期域、插件 ID 和代次，也不能
换用另一个工作域的队列。这补齐了工作域替换守卫，但没有把数字 domain 变成分配对象
身份凭据。共享 driver 与原生清理域已采用受验证分配；共享 episode mutex 关联及独立命名空间仍是明确边界。
完整 R1 解释还需要组合这些共享 owner、函数含义与 Node 发布版本。

快照是 ghost 数据，不增加运行时表复制、历史分配或额外 `Arc` 引用。
跨线程回归保留逃逸上下文，经历 provider 撤下、清理失败和重试，再检查替换与新一轮
执行，同时核对准确的 `Arc` 引用数以及旧上下文关闭后的拒绝行为。
另一个回归分别在 Finish 和 Unload 检查工作域替换被拒绝。

审查路径：`native_capture.rs::Capture` → `LifecycleState::capture_native_values`
→ `NativeEpisode::wf` → `Execution::capture_correspondence`
→ `NativeRuntime::{begin_managed_execution,finish_managed_execution,release_managed_execution}`。
这加强了 committed dependency 与式 (46) 原生发布视图的实际对应，未缩小 R2 原有验收条件。
负向控制分别移除工作域检查、丢失 Begin 来源、把 publication 的 Begin 控制快照换成
Finish 时的状态；每项都必须编译成功，并由指定合同拒绝。定向检查不代表完整负向回归验收。

## 原生注册表与发布表的联合历史

生产 Rust `Runtime` 现通过 `NativeDriver` 持有
`NativeRuntime<R, H, V>`。注册图与 `NativeServices` 位于同一个受验证 owner
内部，Begin、Finish、查询和 Unload 的调用者不再单独传入服务表。
真实入口保持同一个联合不变量：

- 每个 Active 注册实例都有完整的用户端口发布表，对应当前 episode 代次和真实共享槽。
- 每个保留的发布表都属于仍注册的 Active 或 Unloading provider。单独退休保留发布；
  撤下时停止新查询，但为 committed consumer 和恢复保留原值。
- Finish 先检查真实 episode 的声明是否与存储的 recipe 一致，再发布。
  Release 通过实际工作与清理守卫后，只删除本实例的表。
  失败、重试、压缩、recipe 更新和共享 Child 操作都保留其他实例的发布。

`NativeEpisode::matches_provisions` 还会拒绝编号与代次碰巧相同、声明序列却不同的
值 owner。这是可执行守卫，不是加在普通 Rust 调用方上的假设。
普通宿主的全局 domain 分配器仍负责区分不同 runtime 实例。

`NativeRuntime::history_correspondence` 证明了从空状态到当前观察的连续联合历史，
包含**真实控制状态与保留的发布表**。独立关系 `native_history::step` 规定：
Finish 只增加该 provider 的表，Unload 只移除该表，其他控制步骤保留全部表。
不改变这个观察的调用保留原历史。显式 Restart 仍属于扩展；不含 Restart 的历史
具有严格论文控制投影。ghost 历史在 Cargo 编译中擦除。

这在注册表／共享槽边界连接了式 (46) 的原生发布视图与 L-Finish、L-Leave、L-Unload。
它仍未把 `Arc` 内部值、任意回调函数体、共享 episode mutex 状态、Node 发布版本
共同解释成完整 R1 context。R2 的剩余验收条件没有缩小。

审查路径：`native_runtime.rs::{linked,wf,finish_managed_execution,
release_managed_execution,history_correspondence}` → `native_history.rs::step`
→ `cordis-driver/src/native.rs` → `Runtime::poll_settle`。
聚合 owner 回归覆盖完整发布、冲突声明、provider／consumer 失败重试、
其他实例的值、旧／外部 episode、recipe／宿主记录更新、退休、压缩以及具有空发布表的共享 Child。
三个负向控制分别移除声明守卫、丢弃其他实例发布和遗漏联合历史步骤；
每项都要求突变体能编译，且指定合同确实拒绝它。


## 已用于实际运行的合同

| 用户可观察的行为 | 可执行合同 | 生产调用者 |
| --- | --- | --- |
| publication 持有 owner 实际传入的值 | `PublicationStore::publish_checked` 检查真实生命周期域、代次和准入，再保存泛型载荷 | `Driver::publish` → `LifecycleDriver::publish_value` |
| 替换保留 publication 身份并返回真实旧值 | `replace_checked` 和 `ValueCell::replace`；拒绝时原样返还新值 | `Driver::set`、Rust `ServiceSlot::replace` |
| 旧清理租约仍读取自己保留的值 | `leased_value` 从真实租约记录中取得 publication 身份与载荷 | `Driver::read` |
| 只有生命周期和完整资源清单检查通过，才能转移实际载荷 | `finish_resources` 将已有票据／租约协议与载荷转移组合；拒绝时三者均保持原状 | `LifecycleDriver::finish_cleanup_values` |
| 在轮询 Future 前，用实际参数调用工厂 | `RegisteredPlugin::call` 直接调用保存的原生 `FnMut`；`invoke_future` 保留清理工厂实际返回的 Future | Rust `Runtime::start`、`initialize_cleanup`、`Runtime::poll_groups` |
| 异步清理消费其 Future 实际返回的结果 | `Awaiting::complete`／`await_completion` 用 Verus 原生 Future 语义保存来源与实际结果；`complete_future` 据此判定成功、失败或消耗 | Rust `initialize_cleanup`、`Runtime::finish_reply`、`StaticCleanupFuture::complete_reply` |
| 先保存实际返回的 inverse，再决定是否继续 | `CleanupQueue::land_result` 自行分配 token、保存实际 inverse，并根据结果和取消状态选择后续动作 | `Runtime::poll_groups` |
| 不能因为一个组为空就关闭仍有其他工作的 episode | `CleanupGroups` 持有全部清理队列；`remove`、`seal` 检查未落地 stage、已交付凭据、保留失败和实际载荷，然后关闭注册入口 | `Runtime::poll_groups`、`Runtime::poll_settle`、`StaticCleanupFuture::poll` |
| 整体重试遇到不可重试失败时，不能先推进其他组 | `retry_execution` 先检查绑定的工作状态和全部队列，再一起推进生命周期与 inverse 的重试票据 | `Runtime::retry_cleanup` |
| 只有实际准入的原生 episode 能完成或释放其生命周期 | `begin_execution` 创建两个绑定的 owner；`finish_execution` 与 `release_execution` 检查原始票据和当前代次 | `Runtime::start`、`Runtime::poll_settle` |
| 移除一个组不能把已消耗的失败变成恢复成功 | `CleanupGroups` 保留已接受的 `Drained` 记录；`release_execution` 从它推导最终结果 | `Runtime::finish_reply`、`Runtime::poll_settle` |
| Child 在 realm 隔离后仍保留父插件的实际依赖 | `register_plugin` 解析声明的键，同时继承原始端口和子 realm 端口，并排除子插件自己提供的端口 | `Runtime::mount_inner` |
| 热更新不能让已经准入的调用误用新回调 | `admit_registered_root` 绑定真实工作与登记对象；`call` 检查域、owner、回调版本，再直接调用保存的 `FnMut` | `Runtime::start` |
| 原生 Child inverse 不能删除另一 runtime 中数字 ID 相同的插件 | `ChildIdentity` 来自真实登记；`retire_child` 验证其域和父插件 | `Runtime::poll_cleanup` → `dispose_child` |

原生 Rust 服务值还通过 `begin_native_execution`、`NativeEpisode::provide/read`、
`finish_native_execution`、`release_native_execution` 接入 `Runtime::poll_settle`、
`AsyncSetup` 和 `NativeDriver`，见下文原生服务值一节。

Node 容器保存的是实际的 `u64` JavaScript 值句柄；Rust 值单元保存的是实际的
`Arc<dyn Any + Send + Sync>`。这些合同不解释 JavaScript 对象的可变字段，也
不解释 Rust 值的内部可变状态。载荷无需实现 `Clone`、`Copy`、`Debug` 或相等比较。租约固定的是 publication
身份，而非不可变快照：替换该 publication 会改变其租约读到的值；新 publication
则使用另一个身份。

清理适配保留既有策略：可重试工厂失败后继续保留；普通 Rust 的一次性清理失败
可以报告为已消耗的 `Drained`，静态宿主采用 `RetainFailure` 并保持阻塞。
两者都不会被自动报告为成功恢复。待丢弃的工厂和被拒绝的载荷在记账互斥锁释放后
才析构，以便用户 `Drop` 安全地重新调用宿主。

## 与论文的对应

`publication_projection.rs` 把真实容器解释为键值查找表。
`publish`、`replace`、`revoke` 在自己的函数体中使用相应证明：

- 发布向当前不可见的键插入实际传入值。
- 替换只更新该键，并返回它真实的旧值。
- 撤销只移除该 publication 的可见性。重复撤销不能隐藏同键的新 publication。
- 改变租约元数据、回收已撤销的值不改变当前查找表；保留租约观察是另一个观察，可能改变。

这里解释的是注册表的可见性投影。宿主 phase、依赖和可用性检查仍会对服务查找
施加额外条件；单独这张表不是整个宿主观察。

这些是 §3.4 键局部更新的实际实例，对应 `coeffects::put`。它们不等于证明
多版本宿主注册表与 R1 的整个 reified context 相同。写回返回的旧值能够恢复单次
替换，也不能据此推导插件在干扰下的完整 inverse law。

`LifecycleState` 现在向上层传播插入时实际的 parent／dependencies／provisions，
Begin 时的 committed bindings，以及 Finish、Retire、Remove、Unload 的已有
控制步骤关系。记录压缩保持控制观察；显式重启和动态接口改变保留各自的扩展合同。

`land_result` 同时证明真实载荷更新，以及 Iter、Finish 或延迟 diversion 的
累加器投影。这一投影不解释不透明 inverse 函数的外部效果。论文没有对应守卫的
失败或显式效果组取消，仍属于宿主扩展。

## 异步证明的边界

对于传入 `await_completion` 的 Future，Verus 证明：如果完成值返回，其中保存
的就是该 Future 的真实输出，以及包装时传入的来源。这不证明它最终一定返回，
也不证明调度公平。`Completion` 的字段不能由接收者替换，但它不是外部 I/O 的
真实性凭证：调用者仍可以包装一个立即完成的 Future。

`invoke` 通过实际调用建立
`callback.ensures((actual_argument,), actual_result)`；`invoke_future` 立即调用
工厂并保留其实际返回的 Future，不会把工厂副作用或 panic 捕获推迟到第一次轮询。
原生 setup 现通过 `RegisteredPlugin::call` 直接调用保存的 `FnMut`；cleanup 工厂
使用 `invoke_future`。迭代器入口现使用下文的 `EffectRun::call` 及其私有轮询收据，
适配层不传入预期结果。
经过检查的 `witnessed_invocation` 与 `witnessed_completion` 用真实代码实例化
了这条数据传递路径。

受验证的调用者仍需建立 callback 的 `requires`，受验证的插件仍需证明自己的
效果律。普通 Rust／JavaScript 插件体仍在这个证明之外。原生登记与调用现已按
下文连接，但这仍不证明插件的 inverse law、完整宿主解释或任意外部 I/O 的真实性。

## 已由内核持有的组合状态

`CleanupGroups<T>` 替代了宿主原来持有多个独立队列的可变 map。字段是私有的，
也不向外借出可变队列。修改一个组保持其他组。移除的队列退出活跃 map，仅保留
递增的身份计数，因此存储和排空扫描随活跃组数量增长，不扫描历史空槽；移除后
也不能复用旧域冒充另一个组。
关闭时检查全部队列，因此根队列为空不能掩盖其他组的未落地 stage 或已交付清理。
已取消 stage 必须落地后才能移除其组，实际返回的 inverse 继续保留。
整体重试的预检查失败不修改任何组。关闭成功证明全部已持有队列都没有保留载荷、
已交付回调或未落地 stage，并关闭该容器后续的注册入口。

轮询 Rust Runtime 和静态适配器都使用这一组合。下面的 `SetupWork` 进一步
连接根 setup 的交付凭据和待处理请求。原生生命周期准入与释放现已接入这些
owner，见下节；原生 publication 值以及 Child 请求／inverse 的配对和同步现已有
下述合同。完整宿主观察仍需联合语义不变式，这些局部组合不能关闭整个生产状态的验收义务。

## setup 与请求也参与排空

`SetupWork<C, G>` 持有真实的 Child／效果组请求，跟踪根 setup 和已经交给宿主
执行的请求。`WorkItem`、`PendingWork`、`WorkReceipt` 的载荷与身份字段都是
私有的：实际请求经过 `run` 调用后产生结果凭据；异步工厂经过 `start` 后保留
实际 Future，只有该 Future 返回才产生其完成结果。派发队列为空而已交付请求
尚未返回时，整个 episode 仍未排空。队列采用 `VecDeque`，不会在每次派发时
搬移剩余请求；已完成票据退出活跃 map。

原生 Child 请求由 `enqueue_native_child` 同时构造申请与 inverse；通用
`enqueue_owned_child` 继续用于外部宿主提供的成对载荷。拒绝时原样返回，
由宿主在释放锁后析构。最终 `seal` 检查根 setup、排队与已派发
请求以及全部清理队列，并检查二者属于同一清理域。Rust Runtime 和静态宿主都
使用该守卫；普通 Runtime 的初始化完成也使用同一组实际状态。

尚未开始轮询的根 Future 可以在撤回后取消。已经开始的 Future 必须返回，或
保留为未确认的放弃状态；它不能走“尚未运行”的取消路径。异步完成保留实际
`Result`，失败不能使初始化成功。下文的受验证转换保留传入的真实 poll 结果，
并只能把捕获到的 panic 转为失败；执行轮询和捕获 panic 仍由普通 Rust 负责。调用关系也不能
替代插件的效果律，或 Child 请求、共享句柄与 inverse 之间的完整语义关系。

## 登记的回调与原生 Child 操作

`Runtime::mount_inner` 通过 `NativeHost::register`／`register_child` 调用
`LifecycleState::register_plugin`／`register_child_slot`，包括动态 Child 的真实分配。它消费实际的 `PluginDefinition`，读取父插件在内核中的权威声明，
根据传入的 realm map 解析键，并执行真实插入。返回的 `RegisteredPlugin` 持有
实际回调、解析后的接口和保留的 anchor；`NativeHost` 将它与真实 `Mounted`
载荷一同持有，普通宿主代码不再另行向注册 map 插入登记对象。

合同同时证明精确的成功条件与产生的接口：继承的依赖保留原始端口和子 realm 中的
端口，不引入重复端口，也不继承子插件自己提供的端口。重复声明和冲突的保留会被
拒绝。登记不要求依赖已经可用，可用性仍在 Begin 时检查。失败保持生命周期状态，
并返回原始定义和回调。更严格的父插件条件、realm 映射和合成 anchor，是围绕论文
Insert 控制规则的明确宿主约定。

`admit_registered_root` 检查实际未完成的 setup 动作、当前代次、登记域与 owner，
然后签发包含实际参数和回调版本的私有调用对象。`RegisteredPlugin::call` 检查
这些身份，直接调用保存的 `FnMut`，不接收替换回调或预期结果。Verus 原生调用
合同把登记的函数及实际参数，与返回的 `WorkReceipt` 关联起来。

`WorkReceipt::dispatch` 区分工厂实际返回的 `Ready` 结果和 `Pending` Future，
两条路径都保留签发的根任务身份。工厂仍立即运行，仅其返回的 Future 延后轮询。
同步完成和有条件的异步完成接入已有根任务／排空协议；捕获到的 panic 走只能
报告失败的入口。原生 Runtime 使用这条路径，静态适配器复用结果分派合同，但
保留自身的外部登记边界。

替换回调保留插件身份，并推进经过溢出检查的版本。替换前已准入的调用会被拒绝，
不会执行旧回调或新回调；已经开始的 Future 仍保留原来的完成身份。批量配置更新
在修改前检查每个回调所需的全部版本增量，安装结束后再析构旧捕获值。

Child 登记成功还会生成私有 `ChildIdentity`，携带实际 runtime 域、父插件和
分配出的 ID。原生清理保存它并调用 `retire_child`，合同证明对该 Child 执行
Retire 控制步骤。Child 移除后的重复调用保持状态，不会退休后续替代插件，也
不会操作另一 runtime 中数字 ID 相同的插件。退休是请求 Child 撤回，不等于
证明其资源已恢复；已有清理和移除守卫仍然必要。

原生共享句柄现在保存私有 `ChildSlot`，其来源从实际 `SetupWork` 生命周期动作
构造。`register_child_slot` 检查 runtime 域、父插件代次、存活阶段和 Pending 状态，执行
真实登记，再写入该次登记实际返回的 Child 身份；它不接受宿主另行报告的成功 ID。
重复、失败、已取消或旧 episode 的请求不会分配节点，并返回原始回调。分配失败
保持 Pending，宿主用 `reject` 记录实际错误；这个只能报告失败的入口不能覆盖
成功分配。

`retire_child_slot` 自行读取已分配的身份。若 inverse 在分配前就被消费，它将
Pending 槽改为 Cancelled，迟到的请求便不能创建失去清理者的子插件。失败和
取消的槽没有需要退休的 Child；重复退休保留原身份，移除后也不会指向替代节点。
原生 Runtime 现通过下述 `SharedChild` 调用这些操作，其配对和同步也进入证明。
拒绝后的回调捕获值析构和后续宿主退休回调均放在释放锁后。静态适配器仍使用
明确的外部分配确认协议。

这些合同已连接真实分配和登记函数调用；下述共享 Child 协议进一步减少了普通
宿主的连接假设。但 publication／context 观察、回调／panic 适配和具体插件的
效果／inverse 定律仍需完整语义组合。登记存储与生命周期成员关系已有后文的
联合不变式。域与服务键分配器的全局唯一性仍是宿主边界。

## 真实请求与 inverse 共享同一个 Child

[`shared_child.rs`](../crates/cordis-kernel/src/shared_child.rs) 补齐了原生 Child
请求／inverse 的别名对应与同步合同：

- `enqueue_native_child` 只接收真实请求载荷，从实际 setup 动作构造一个
  `SharedChild`，将同一句柄放入排队的 `NativeChildRequest` 与保留的
  `ChildCleanup::Native`，再返回观察句柄。准入有精确成功条件；拒绝时原样
  返回载荷，两个队列均保持不变。这个原生入口不接受调用方选择的 inverse 句柄。
- 私有 `vstd::rwlock::RwLock` 持有实际 `ChildSlot<()>`，锁不变式将槽绑定到
  runtime、父插件和 episode。登记、拒绝与退休使用独占访问；观察使用共享访问。
  `register_shared_child` 证明成功**当且仅当**锁内观察到的状态和真实注册表
  满足分配守卫。
- 每次终态决定生成持久的 `GhostMapAuth`／points-to 凭据，凭据对应实际槽
  修改，不是另建一份预期日志。`ChildSnapshot::terminal_agrees` 证明同一槽的
  两个终态观察不能矛盾。`cancellation_precludes_assignment` 将真实 Cancelled
  观察与之后的观察组合，后者不能为 Assigned。再结合真实登记结果合同，可以
  跨越多次锁获取，排除 Pending inverse 完成后的成功分配。
- 每个操作返回实际前后观察，返回前释放锁。Runtime 的动态 Child 使用这一
  入口；已经登记的原生子插件通过 `from_identity` 接入，保持真实身份。
  Retire 仍不同于 Remove，也不同于资源已排空。

它将论文 Child 分配／Retire inverse，以及 Definition 58／63 的控制步骤投影，
连接到真实队列载荷和共享状态；这不是新增论文规则，也不是完整 R1 Child 解释。
不能由此宣称任意插件效果、完整宿主观察或 Theorem 64 已证明。

同步证明使用固定 vstd 的锁／资源合同和标准 `Arc` 克隆合同，内核检查不重新验证
vstd 或 Rust 标准库。该锁使用自旋，不证明公平性、无饥饿或全局无死锁。临界区
不调用用户回调。锁内只有标量生命周期状态：vstd 锁要求显式释放，且不会自动
析构内部载荷，因此错误文本与回调捕获值保留在锁外。诊断文本、panic 适配和其他
Runtime 锁仍在这份共享槽证明的边界之外。本轮未新增依赖，也未改变工具链版本。

## 从生命周期准入到实际释放

`LifecycleState::begin_execution` 执行真实 Begin，并用该 setup 动作的域、owner、
代次和动作身份创建 `SetupWork` 与 `CleanupGroups`。来源字段私有且不可更改。
即使另建一个数字清理域相同的空容器，也不能代替已经准入的清理组。
全局域的唯一性仍由普通 `LifecycleDriver` 的原子分配器提供，属于宿主边界。

原生 Rust Runtime 的整个 episode 使用以下受验证入口：

- `settle_execution` 等待实际根 setup、已派发的 Child／效果组请求和未落地 stage，
  然后才能确认最初的 setup 动作。
- `finish_execution` 还检查当前真实 target 与全部清理组，再执行真实 Finish。
  Finish 被拒绝时可以确认已经结束的 setup，但不能改变内核状态或使服务 Active。
- `fail_execution` 要求存在队列中保留的失败，且没有未落地工作或仍在执行的清理，
  然后保留生命周期义务和已提交依赖。
- `retry_execution` 先检查全部队列，再一起推进生命周期与 inverse 的重试身份；
  被拒绝时二者均不改变。
- `release_execution` 检查绑定来源、当前代次、restoration 状态、未完成的生命周期
  动作、根 setup／请求及全部清理队列。它自行推导 `Succeeded` 或 `Drained`，
  消费动作、关闭两个 owner，并执行真实 Unload。拒绝时三份状态均保持原状；
  成功则证明该 owner 已释放 committed dependencies 且处于 Inactive。

宿主不再选择最终的成功标志，也不再另存 `cleanup_drained` 布尔值。受验证的组
owner 记录已经接受的消耗失败，在删除组、重试和关闭时保留它。新 episode 使用
新来源和空失败记录。同步 Child 结果通过 `complete_result` 使用与 Future 相同的
受验证结果策略。Child 分配／退休、真实配对与共享槽同步现已有上述合同；
普通回调／panic 适配和完整宿主观察仍需语义对应证明。
面向外部宿主协议的底层显式报告 API 继续存在；收到报告不等于证明外部效果。

Begin、Finish、Unload 的合同连接到已有论文**控制投影**；它们还不是完整 R1 的
值／代码／continuation 解释、完整 Child 效果或整条生产轨迹的证明。静态／Node 桥接
保留各自的外部完成边界，不能把这份原生组合证明自动推广到所有适配器。

## 原生服务值参与准入、Finish 与 Unload

`native_values.rs` 现在持有原生 Runtime 的真实发布表与 episode 服务槽。
`begin_native_execution` 执行实际 Begin，同时创建绑定的 `SetupWork`、
`CleanupGroups` 和 `NativeEpisode`。外部不能用已有工作票据再次构造值 owner。
域检查及旧 publication 检查在 Begin 之前完成，拒绝时不改变控制状态。

私有捕获函数读取内核中实际 committed 绑定，并复制每个可用绑定对应的真实
`Arc<ServiceSlot>`。合同证明双向关系：每个保留的 import 都来自当前代次的
已绑定 provider，每个可用的已绑定槽也都被保留。无关服务不会因此增加持有者。
realm 与 provider 身份仍是查找键的一部分。这里保留的是同一服务槽的 referent，
不是对内部可变服务内容做不可变快照。

`NativeEpisode::provide` 只接受已声明且尚未提供的键，保存实际实参；拒绝时
原样返还实参。其 `owned_table` 投影证明了 §3.4 的同一 `coeffects::put` 键局部
更新，并保留 import 和其他键。这是 episode 的局部表，不是完整 R1 上下文。
`read` 只能选择自己提供的值或实际捕获的绑定。全局 `visible` 还会解析当前
Active provider 并检查代次。因此，撤回后新调用看不到该 publication，正在清理
的旧 episode 仍能读取原来绑定的服务槽。

`finish_native_execution` 检查所有声明值均已提供、工作和队列来自同一次准入，
且真实 Finish 守卫成立，再在同一受验证调用中进入 Active 并发布实际持有的槽。
Runtime 不再于每轮 Active 调度复制全部已发布槽；`set` 继续原地更新共享的
`ValueCell`。这里不据此宣称已测得性能提升。

`release_native_execution` 检查值、工作及 publication 的来源一致，再执行真实
排空和 Unload 协议。拒绝时保留生命周期、工作、队列、发布表与 episode 值。
成功时只移除该 owner 的 publication，关闭 episode 的后续读写，并返回实际
持有、导入和发布的槽。宿主在释放记账锁后析构这些值；部分初始化被取消也走
这条路径。保留的清理失败不能释放，重试必须通过已有的新票据协议。已经返回
给用户的 `Arc` 仍是普通引用，不是可撤销租约。

证明采用 Verus 标准库对 `Arc` referent 及克隆的合同，不证明互斥锁同步、引用
计数实现、服务内部可变内容或任意 availability 回调。静态／Node 嵌入继续保留
明确的外部宿主合同；底层生命周期 API 本身也不会自动维护上述原生组合。
生产原生适配器现通过 `NativeRuntime` 使用内部 `NativeHost`，不再暴露可变生命周期或登记 map。共享
Child 句柄、宿主记账字段的语义与完整宿主解释仍需要全局语义不变式。

## 登记与生命周期由同一状态持有

`NativeHost<R, H>` 持有真实 `LifecycleState`，以及实际
`RegisteredPlugin<R>`／宿主载荷对的 map，替代 Runtime 原先独立的
`BTreeMap<PluginId, Mounted>`。它的 `wf` 合同对所有条目建立：

- map 的成员集合恰好等于论文控制投影中的 registered 集合；
- 保存的回调身份与 map 键相同，域与真实生命周期域相同；
- 父插件和解析后的依赖／提供端口与内核的实际声明一致，包含保留的 anchor。

`register` 执行真实 Insert，并在返回前保存传入的回调和宿主对象；
`register_child` 还在同一次操作中写入实际 Child 槽。失败时原样返回两份输入。
`remove` 先通过已有生命周期 Remove 守卫，再返回恰好对应的真实条目，方便在
记账锁外析构。Unload 保留登记的回调，Remove 是另一步骤；其他条目保持不变。

`host_mut` 只借出 `H`，证明任意通过该借用进行的修改都保持登记与控制状态不变。
容器不暴露可变登记或生命周期引用。`replace`、`admit_root` 和 `call` 按 ID 选择
实际保存的登记，保持其他条目，并检查版本与调用身份。所有公开生命周期转换、
原生值组合、Child 退休和压缩操作都保持 `wf`。原生适配器直接从该状态读取未完成
票据，不再维护第二份动作视图 map。存活 ID 枚举证明无遗漏、无重复，并只扫描
存活条目，不扫描历史身份墓碑。

这把 Definition 49–50 的登记／接口部分，以及 Definition 58／63 的控制投影
连接到真实生产存储。这是该投影的保持性结果，**不是完整 Theorem 64**，也不是
完整 R1 context 解释。`H` 仍是不透明载荷：Future 状态、共享句柄、锁同步、
availability 语义与 panic 适配，不会因为容器的成员不变式而自动获得证明。
外部／静态适配器继续保留原有登记边界。

## Effect 请求与实际轮询收据

`effect_work.rs` 把实际 effect 迭代器接到既有清理 owner。
`SetupWork::enqueue_effect` 先检查真实工作 owner、生命周期来源、发起组的取消
状态、请求容量和新清理域，再在同一受验证操作中创建清理组、排队实际迭代器，
并绑定二者身份。拒绝返回原始载荷和绑定向量，两个 owner 均不改变。派发不能
使用其他生命周期或数值 ID 相同的另一清理组激活请求。

`EffectRun` 持有实际迭代器载荷。`admit` 成功后预留递增的轮询身份；回复未完成前，
再次准入或调用不能覆盖它。`call` 把实际保存的载荷和参数交给适配函数，再从
真实返回值构造私有收据。`land` 检查生命周期／组／域和当前轮询身份，才接受结果。
Pending 保留真实 stage 的 pending 状态；Ready 把实际 inverse 或错误交给
`CleanupGroups::land_result`。取消决定是否继续迭代；取消后才产出的 inverse
仍先收集，再停止后续 stage。错误收据原样返回，不改变执行 owner 或清理组。
轮询身份耗尽会拒绝准入，不回绕复用。

真实 Runtime 的 `AsyncSetup::effect`、派发和 `poll_groups` 均使用这些方法。
普通 Rust 中的 `cancelled_groups` 集合已删除；`ensure_active`、嵌套 Child／effect
准入和取消查询直接读取决定 inverse 落地的同一 stage 状态。`EffectHandle::cancel`
仍是协作式请求，驱动把请求记录到 stage 协议后，准入守卫才据此生效。原生与外部 Child
排队也经过该守卫。取消中的在途工作仍可登记 inverse，但不能利用这一点获取
新的 Child 或 effect。

这一段把实际迭代路径接到既有 L-Iter、L-Finish、L-Divert accumulator 解释，
证明结果来源、队列归属和 continuation 选择；回调合同仍需由受验证调用方满足。
传入的 Poll／panic 结果到 `EffectOutput` 的转换现已有下文的受验证合同。
任意迭代器和 inverse 的外部效果、自定义析构、宿主锁调度及不透明可变字段的
语义仍在边界之外。这不是
完整生产轨迹解释，也不证明公平性或全局终止。

## 同一生产执行 owner

`Execution<V, C, G, I>` 现持有真实 `SetupWork`、全部清理队列、实际
`EffectRun<G>` map、借出的 runner 身份、原生服务值和初始化状态。Runtime
不再另存 work owner、phase 字段或迭代器 map。静态适配器也用它管理工作、
清理与 phase，同时保留外部生命周期与服务值的明确边界。

联合不变式连接生命周期来源、清理域与存活组身份，并要求 work、cleanup 与
原生值的关闭状态一致。`begin_managed_execution` 创建这个状态；
`finish_managed_execution` 在同一个受验证调用中发布实际值并进入 Active；
`release_managed_execution` 检查完整排空、关闭 episode 并返回实际值。
Runtime 的直接退休和 restart 撤回使用 `withdraw_managed_execution`，将
控制转换与关闭新工作准入组合，同时保留在途工作和值。Child 触发的退休仍先调用
既有共享 Child 协议，再执行宿主通知。

`take_effect` 在 owner 中留下借出记录。`put_effect` 检查原始存活队列，不能
覆盖已有 runner。`retire_effect` 只有在队列排空后才能消费实际 runner，并返回
真实载荷供锁外析构。即使迭代器 map 暂时为空，借出或放弃的 runner 仍阻止
移除和释放。这是安全守卫，放弃 runner 不代表最终能够恢复。已准入 stage 在取消
后仍可落地其真实 inverse。

这些合同约束实际生产状态与转换，但尚未给出不透明回调效果、可变值内容、
全部宿主记账字段的语义解释，也没有建立整个宿主到 R1 的对应。

## 真实 Poll 结果转换

`normalize_poll` 保留实际 Pending／Ready，捕获到的 panic 只能转成失败。
`normalize_effect_poll` 区分 Pending、迭代结束、返回错误、产出 inverse 和
捕获到的 panic；它只映射一次实际 inverse，不接受调用方提供的预期结果。
Runtime 的根 setup、迭代器和清理轮询使用这些受验证函数；静态宿主复用根 setup
和清理 helper。

标准 `Poll` 的类型规格描述真实枚举的分支，没有假设 `poll`、`catch_unwind`
或回调实现正确。证明从传入转换函数的实际结果开始，不涵盖 panic 捕获机制、
轮询实现、任意回调的外部效果或最终返回。

## 真实可逆服务值与有限程序

[`ReversibleValue`](cases/reversible-values.zh-CN.md) 为三段语义连接增加了具体生产
路径。插件使用 `Setup::update_reversible` 或 `run_value_program`，普通 Runtime
和静态宿主调用同一受验证实现。私有 inverse 保存真实共享目标和捕获的前／后态。
`Execution` 在返回前登记它；`CleanupQueue::dispatch` 直接选取、执行并确认队列
中的实际对象，宿主不传入成功标志。干扰发生后，该 inverse 保留供显式重试。

`operation`、`primitive_theory` 证明替换、检查溢出的加法、异或和比较交换的
实际部分逆操作效果律。观察包含值和嵌套层级，所以后来写入相同值也不会被误认
为状态未变。`Program::component` 证明程序根和每个结果选出的 continuation 都
属于 R1 的完整有限严格载体。插件提供的已验证指令和实际比较结果决定执行路径，
没有预期结果或 transcript 参数。

实际值锁持有 ghost 历史。`history_interpretation` 分类每次写入、成功恢复和
拒绝；`ProgramReport::source_execution` 为完整运行或失败前缀构造连续的
dependent-grammar 轨迹，并保持其他表键不变。全部成功前缀的 inverse 按执行
顺序进入既有清理 owner。Cargo 构建会擦除历史。

这条**具体原语／程序路径**完成了上述连接，并不等于完整宿主 context 已完成。
普通回调、Node 对象状态以及全局联合解释仍属于下面保留的 R2 验收内容。
[中文案例](cases/reversible-values.zh-CN.md)／[English](cases/reversible-values.md)
包含代码、约束映射、故障复现和负向对照。

## 可扩展标量效果与受管提交

`ScalarEffect` 提供 Verus 模型与真实 `compute` 方法，要求实际结果等于模型。
`ScaleAdd` 不扩展固定 `ValueOperation` 枚举，即可增加检查溢出的乘加原语。
`ThenScalar`、`ChooseScalar` 用真实返回值和实际 predicate 结果证明组合。
它们将局部计算组合为**一次共享值写入、一个 inverse**，中间结果不会分别发布。

`Setup::update_reversible_with`／`AsyncSetup::update_reversible_with` 的原生路径现在
使用上文的捕获／准备／落地入口；静态宿主仍通过 `ReversibleValue::prepare_effect`
和 `Execution::apply_prepared_effect`。准备阶段捕获值／深度，释放值锁，
执行实现，将真实目标、输入、结果及擦除模型保存在私有 receipt 中。adapter 随后
锁住 episode，调用 `Execution::apply_prepared_effect`；后者重新检查准入，再于
值锁内提交。值／深度不匹配就拒绝，完整恢复到捕获状态则允许提交。取消或撤销后
不能借准备结果继续受管写入。adapter 在这些锁外捕获计算 panic，保留结构化 panic
错误种类。

成功时，受验证 owner 从真实前后态构造 inverse，在返回前追加到实际清理队列。
合同保持原有队列前缀、无关清理组、运行中的效果、checkouts、捕获的 imports 和阶段。
既有 inverse 派发执行恢复，并在干扰失败后保留 inverse 供重试。插件不提交“声称的
结果”，也不能提供一个指向其他值的 inverse。

标量锁历史现包含真实计算操作及被拒绝的准备结果。`forward_interpretation` 将成功
连接到键局部源操作，以及在任意测试表上的严格 inverse；`history_interpretation`
将拒绝提交归为保持标量观察的步骤。`terminal_component` 使用 `primitive_theory`
推导的 inverse 定律，证明这个终端标量操作在完整载体上具有 Component 成员资格。
这为论文带凭据效果（8）和 Component 约束（48）提供了到真实代码的具体路径；它
还不是控制／值／函数／Child／清理联合轨迹，也不证明任意外层 continuation。
此前表定理解释某个键上的标量；`value_alias` 现已提供真实别名投影和带条件的单键映射，
完整回调与多次调用的上下文解释仍开放。

审查路径：[`scalar_effect.rs`](../crates/cordis-kernel/src/scalar_effect.rs) 中的
`ScalarEffect`、`primitive_theory`、`prepare_effect`、`apply_prepared_effect`、
`forward_interpretation`、`terminal_component` →
[`runtime.rs`](../crates/cordis/src/runtime.rs) 的 `update_reversible_with`。
用法见[尚未发布的 API](rust-api.zh-CN.md#可扩展可逆值尚未发布)。原生与静态 setup
均接入该入口。普通 Rust 实现不会仅因实现 trait 而自动获得证明，仍须验证其模型定律。
外部副作用、任意可变服务载荷不在标量合同范围内。本轮选定运行／负向证据见上文
别名／效果部分；[剩余集成场景](r2-state-inventory.zh-CN.md#延后集成的证据)另行记录。

## 带版本的真实值与可用性回复

原生 `ServiceSlot` 现在由 `VersionedValue<Value>` 同时持有真实载荷和版本。
观察从同一次借用取得二者；即使替换成相同值，也会递增版本。容量拒绝返回原输入并保持
整个 cell。predicate 在槽锁外执行，接收结果时重新核对观察版本；捕获载荷也在释放
槽锁后析构。这不证明 predicate 本身、任意对象内部修改或普通 mutex 的调度。

Node 的替换版本进入真实 `PublicationStore`，不再由宿主维护另一份计数器。
`observation`／`leased_observation` 从同一个 owner 读取值和版本，包含被撤销、但仍由
旧 lease 保留的 publication。替换不会改变 publication 身份或将已有 lease 指向新对象。

真实 Driver 的签发、通知、校验、完成与消费者移除现在调用受验证
`availability::Availability`。签发直接检查生命周期域、真实依赖声明、Active provider
和可见 publication，再捕获其实际载荷／版本。完成时重新检查这些来源、完整待办票据、
实际载荷／版本、当前 notification 和 dirty 标志。调用方不能提交声称的“当前版本”或
“仍然有效”。未知／重复回复保持账本；已知但失效的回复只确认自己的待办一次；旧通知
不能覆写新记录。移除消费者删除记录但保留待办回复的确认入口。诊断文本不参与准入。

这属于显式宿主扩展，保留现有策略：通知标脏匹配行但不清空已接受的可用性，单独 `set`
不自动触发新检查。证明的是**接收回复时**的有效性，不是缓存 predicate 永远描述随后
的对象状态。JavaScript 对象内容、predicate 真实性与 wire 转换仍需单独合同。

审查：[`versioned_value.rs`](../crates/cordis-kernel/src/versioned_value.rs)、
[`publication_values.rs`](../crates/cordis-kernel/src/publication_values.rs)、
[`availability.rs`](../crates/cordis-kernel/src/availability.rs) →
[`Driver 适配层`](../crates/cordis-driver/src/availability.rs)、
[`Runtime 槽`](../crates/cordis/src/runtime.rs)。

## 持有真实配置的事务

`Loader` 现在由受验证 `Configuration<Snapshot, Transaction>` 同时持有已接受快照、
revision、候选快照与恢复载荷。`check_begin` 在构造插件／规划更新前拒绝版本耗尽；
`begin` 保存实际候选与恢复输入。借用待办工作不能修改已接受快照或版本；`commit`
只能消费已保存的候选，返回真实旧快照和恢复载荷，不能由调用方另传一个快照替代。
恢复采用实际重建快照、返回被放弃候选且不递增 revision。有效配置不变时刷新源表示
属于单独元数据转换，不能宣称完整观察没有变化。

普通异步 Loader 跨 await 借用它持有的待办事务。丢弃 apply 或 recover Future 因此
保留候选 ID、旧 factory、已开始的 inverse 和恢复进度。容量检查不再发生于配置已经
改变之后。

这些是快照／版本／所有权合同，尚非配置工作流的完整 refinement。`recover` 接受普通
宿主代码重建的快照，没有证明其中新 ID 对应原组件语义。树展开、模块执行、group／
include、更新体效果、生命周期动作及持久化结果仍需 R2-I 的联合论证；第 81 项状态
不因此升级。

审查：[`configuration_transaction.rs`](../crates/cordis-kernel/src/configuration_transaction.rs)
→ [`Loader::apply_prepared`／`recover`](../crates/cordis/src/loader.rs)。

## 连续的真实生产控制历史

`LifecycleState` 现在与实际 Kernel、动作协议一起持有 ghost `History`。每次基础
控制变更记录真实的前后控制观察。其不变量从空注册表开始，保留之前的前缀，并
以当前真实控制状态结束；`record_control` 不能用调用方给出的预期轨迹替换它。

`control_history_correspondence` 证明整条记录连续，每一步满足论文控制规则、
保持控制观察的内部步骤，或 `control_history.rs` 中明确的扩展。普通失配退出
对应 L-Divert／L-Leave，仍然 coherent 时的强制退出保留 Restart 分类。动态
provision 增删和首次启动前的依赖配置具有精确的接口帧；删除 provision 还要求
没有保留的 commitment 引用该端口。被拒绝的调用和存储压缩保持控制观察。
若历史没有扩展步骤，`strict_paper_trace` 从实际历史推出有限的严格论文控制
执行及其可达性结论。

原生和 Node driver 都使用这个生命周期 owner，动态 Child 插入、托管资源释放
也经过它。历史在 Cargo 构建中擦除。这是完整的**控制投影历史**，还不是整个
R1 context：服务对象内容、回调／函数字段、publication 版本以及值／清理轨迹
仍需组合为共同语义观察。仅修改协议的步骤在控制投影中属于内部步骤，其既有
收据和清理合同继续约束这些修改。

## R2 剩余验收内容

1. 在可扩展的生产插件入口，建立“实参 → 实际执行的操作 → 结果 → continuation →
   真实 inverse”的关系，并由具体原语证明效果律。原生登记与直接 `FnMut` 调用
   现已建立其中的回调／实参／结果这一段；可逆值程序还建立了具体效果／inverse
   律及结果选择的实际代码路径，但普通插件函数体仍未完成。不能改成调用方提供预期结果，或直接
   假设任意回调正确。
2. 用同一受验证的生产状态持有并组合全部并发效果组、动态子插件、publication、
   已准入工作与排空／释放决定。全部清理队列现已有共同的受验证 owner，载荷释放
   也已组合票据／租约验证；根 setup 和请求现已参与生命周期准入、失败、重试和释放。
   真实 Child 分配／退休和一次性槽状态转换现已有合同，原生 publication 与绑定值
   owner 已组合 Begin／Finish／Unload；NativeHost 现还保持实际注册表、回调和
   生命周期接口的对应。原生 Child 配对、共享槽同步和持久终态决定也已有合同。
   `Execution` 现统一持有实际工作、原生值、phase、runner 及借出记录，并组合
   发布、撤回和释放。其他共享宿主记账的语义与完整宿主观察仍需联合不变式；
   结果转换现已单独验证。
3. 证明完整生产执行轨迹的步骤分类及其与 R1 解释的关系，包括明确列出的多版本和
   动态接口扩展。实际可逆值历史及完整有限程序现已有 source 轨迹；两种适配器还共享连续且
   已分类的真实控制历史。它们整体组合后的原生／
   Node 历史仍未完成。列出一些方法的分类本身不构成这一定理。

这些就是既有的 R2 退出条件，并非为了缩小范围而新增或替换的条件。本轮没有
提升原论文条目和四项集成审查的完成状态。

## 审查与复现

八个执行 owner 测试覆盖发布与 phase 原子转换、异域撤回、释放与已关闭上下文、
失败与重试、错误 runner 归还、迟到 inverse、已派发工作，以及放弃根任务或
runner 后仍阻塞。三个 Poll 测试覆盖全部结果分支和不可复制 inverse 的实际所有权。

七个 effect-work 测试覆盖原子分配、实际载荷／绑定、Pending／Ready 收据、取消后的
inverse 收集、跨组和跨生命周期误投、拒绝后的载荷所有权、取消后不再调用迭代器。
Runtime 回归覆盖逃逸上下文、迟到 inverse 登记与落地、停止后续 stage 和保留 owner。
四个负向对照分别错配请求组、绕过取消、接受错误轮询身份或丢弃实际返回的 inverse。

```sh
cargo test -p cordis-kernel --test publication_values --test async_completion --test cleanup_queue --test cleanup_groups --test setup_work --test execution_lifecycle --test plugin_registration --test child_slot --test native_values --test native_host --test shared_child --test effect_work --test execution --test poll_result --offline
python3 scripts/record-development.py --offline
```

八个共享 Child 测试覆盖 FIFO／LIFO 配对、inverse 先于派发、失败与分配终态、
异域／过时准入、拒绝时保留载荷、并发观察／拒绝、已登记身份接入，以及拒绝后
析构重入。另两个 Runtime 回归检查克隆句柄的失败诊断和实际移除期间的身份观察。

六个原生宿主测试覆盖拒绝分配时返回两份实际输入、多 owner 间的宿主修改和回调
更新、错误／异域／旧调用、动态 Child 分配与移除、保留清理失败直到重试和
Unload，以及反复创建／删除和压缩后的存活条目枚举。

七个原生值测试覆盖精确绑定 import、真实共享槽、realm 隔离、重复／异域 Begin、
缺值 Finish、清理失败与重试、旧 publication、已关闭上下文，以及不可复制值延迟
析构。既有 Runtime 回归还覆盖共享值更新、取消 setup 和析构时重新调用上下文。

子插件槽测试覆盖重复分配、inverse 先于分配、分配失败保留、跨 runtime、旧 episode
和移除后的重复退休。四个新增负向对照分别去掉一次性分配检查、代次／父插件存活阶段检查和 Pending
取消动作，均要求指定合同拒绝该错误实现。

定向测试覆盖不可复制载荷、新旧 publication、过时代次、异域、完整清理清单、
Future 逆序完成、工厂调用时机、失败重试、析构所有权、取消后的迟到落地，
以及异域／未绑定生命周期状态、保留 provider 依赖、原子重试、删除组后保留消耗
失败，以及仍有非根组工作时尝试关闭。登记测试还覆盖 realm 隔离、父插件当前
声明、拒绝时返回不可复制载荷、错误／异域 owner、旧回调版本、直接工厂调用、
实际异步失败，以及移除后的 Child 退休。常规开发检查还会重新构建并测试实际
Rust 和 Node 宿主。

四十九个 R2 负向对照分别把真实值改为 `None`、替换租约的 publication 身份、把实际等待到
的错误改成成功、允许已取消的 continuation 继续、从排空检查遗漏非根组，以及
篡改受验证 `invoke` 调用者的实际参数、遗漏已派发请求、取消已经运行的根 Future、
替换为未绑定的清理容器，以及把消耗失败报告为恢复成功。其中五个原生值负控分别
遗漏 committed import、绕过代次检查、不完整发布、替换实际发布值表，或释放另一
episode 的 publication。另三个原生宿主负控隐藏登记、借出另一 owner 的记账
对象，或替换另一 owner 的回调。另三个共享 Child 负控给请求换用另一共享句柄、
拒绝本应合法的分配，或在未修改实际槽时报告退休完成。六个执行／Poll 负控分别
遗漏借出记录、接受异域 runner、遗漏 Active 转换、在队列存活时完成 runner、
把 Pending 变成完成，或丢弃返回的 inverse。定向实验必须先证明未修改版本、
编译错误版本，再确认指定合同确实拒绝该修改。新增五个值／程序对照改变结果分支、
忽略 depth、遗漏 inverse、伪造恢复成功或跳过 continuation；两个控制历史对照
遗漏真实步骤，或把另一个端口的声明归到传入端口。定向通过不表示完整的 184 项负向
回归已运行，详见[验证等级](validation.md)。

绑定源码的开发报告独立记录完整正向检查，不表示发布验收或整篇论文完成。本轮
没有给 Rust 用户增加 Node 依赖，也没有引入时序逻辑库。

## 受验证的原生身份分配

原生宿主的四个分配器（`NEXT_KEY`、`NEXT_REALM`、`NEXT_EPISODE`、
`NEXT_CLEANUP`）与 Rust／Node 共享 driver 的 `NEXT_DOMAIN` 现使用
[`IdentityIssuer`](../crates/cordis-kernel/src/identity_issuer.rs)。
服务键、realm 隔离、共享 Episode 代次以及 root／效果清理域、共享 driver 域由受验证 CAS 循环
分配，替代宿主局部的 `AtomicU64::fetch_update` 闭包。这补强了 Begin／work／group
检查所依赖的新鲜性，但不能据此认证任意相等的数字。

`issue` 的成功分配在实际强 compare-and-exchange 处生效。擦除后的权威状态为
准确返回的整数发放线性权限；`Identity::distinct_from` 证明同一分配器的两份
分配权限不能指向同一整数。丢弃凭据不会回收编号。持久进度凭据保证每次失败
CAS 观察到的值严格增大，因此重试循环有有限的数值下降量。这仅涉及分配器
实际执行的步骤，不证明调度公平或用户 Future 最终返回。

零被保留，`u64::MAX` 是耗尽哨兵。耗尽结果携带实际前沿的证据，
`remains_exhausted` 通过后续真实读取确认永久耗尽；所有路径都不会重置或回绕
计数器。原生宿主保留现有的耗尽时 panic 策略，共享 driver 继续返回 `Capacity` 错误。运行时每个命名空间只有一个顺序一致
原子计数器，权限表与进度历史均被擦除。

不同分配器可以返回相等整数；`starting_at` 创建独立的尾部命名空间，不是恢复
旧分配器的令牌。普通 `Arc`／`Weak`／mutex 关联、静态输入元数据以及这五个生产
分配器之外的命名空间仍是明确边界。轮询前的 Weak 检查继续保留，`HostStatus`
中条件式 Journal 归属前提**尚未**被本轮分配器证明消除。完整联合宿主解释与论文
步骤分类仍待完成。

本批源码通过 9 项定向 Verus 检查、89 项 Rust 回归、805 项 Node／Loader 回归、
全部目标／特性的严格 Clippy 和格式检查。两个严格负例均通过完整突变体编译，并在
新的匹配正例之后准确失败于分配／耗尽后置条件。299 个规范控制通过锚点预检；
全量负例执行／校准、全内核证明、完整开发／发布及 R2 验收未运行。运行覆盖包括
并发分配、丢弃凭据、耗尽、串线句柄和清理重试；没有放宽求解器、断言或超时限制。


## Execution 直接拥有共享效果状态

`Execution::effect_status(&mut self, id)` 为存活 group 安装唯一的私有共享 link，
并返回持有实际载荷的 `HostStatus`。Execution 不变式把这个准确 link 绑定到自己的
Journal、清理成员、Begin／work 身份及 group 域。`initialize_effect_status(id)`
与 `retire_observed_effect(run)` 自行选择保存的 link，不再接收调用方选择的状态，
也不再假设相同数字身份意味着同一 Journal。两个独立运行时即使所有编号相同，
也只能推进各自保存的状态。

初始化在同一 Journal 写入时段认证真实队列已 settled 且没有 pending 阶段。
退休先移除实际已排空 group 和 checkout，再为保存的 link 记录 `EffectFinished`。
返回的 `Observation` 包含真实标志及擦除的认证凭据，其历史包含更早的 group 移除。
失败退休保持整个 Execution。普通 `retire_effect` 共用这套实现，`remove` 和释放
不能静默丢弃已安装状态。退休成功移除所有者的 link，逃逸句柄仍可观察完成。

受验证单元只持有进度、不可变来源和 Journal 成员。错误值、终止错误与 Child 结果
仍由 `HostStatus` 独占；擦除的线性权限把它们的元数据连接到同一单元。Execution
保留 link 不会保留这些用户载荷。`observe()` 返回认证的成员局部历史前缀，不声称
其他成员仍处于此前状态；`execution_snapshot()` 在同一次读取中捕获完整 Journal。
`last_observed()` 明确表示载荷所有者的上次观察，可能早于 Execution 推进的进度。

这消除了真实初始化／退休入口中此前的**条件式效果状态 Journal 归属前提**，加强了
定义 58／63 和现有生命周期／清理守卫到执行代码的连接，没有新增论文公理或未经
验证的指针身份规范。整个共享 Episode 的普通 `Arc`／`Weak`／mutex 关联、静态
context 输入、任意回调及 Node／配置的 Component 解释仍是独立义务。锁顺序为
Episode → 适配层 status → 受验证单元 → Journal；回调和 waker 在释放锁之后调用。

受影响的证明闭包通过 **870 项定向 Verus 检查、0 错误**，并完整编译内核。
**882 项工作区 Rust 单元／集成／文档测试**与 **4 个受影响严格负控**通过。
每个负控均要求新匹配正例、完整突变体编译及准确命名诊断拒绝；全部 **299 个规范
锚点**、格式、工作区全部目标／特性的严格 Clippy 和论文索引检查通过。新增三个
回归覆盖不同 Journal 的相同数字身份、唯一状态创建／普通退休，以及保留 link
期间观察者错误载荷的释放。首次跳过移除负控在真实退休后置条件先于旧诊断锚点被
拒绝，重新定位后重新跑严格正负例并通过；没有放宽求解器或验收标准。
**未运行**全内核证明、全量负控／校准、Node 运行回归、完整开发、发布和 R2 语义验收。


## 实际调用与交错中的状态连续性

为 group 创建的实际状态，现在可以沿组合执行 API 持续追踪。**61 个方法**明确
保持 `status_links`，或只移除正在退休的 runner 条目。合同覆盖 root 准入／完成、
Child／effect 入队、借出／归还、标量与服务程序、inverse 登记、清理失败／重试、
publication 和释放。两个有限程序循环在每次迭代中保持准确 link。状态工厂具有准确
成功条件，并证明 `HostStatus::owned_by(execution, id)`，不能替换已有 group 的 link。

这比重新建立 `Execution::wf()` 更强：清空状态表可能仍满足该不变式，却丢失了逃逸
句柄的关联。新增 frame 合同沿实际调用链保持同一个共享分配。它保持的是 link，
不把并发变化的进度标志假装成不变值；这些标志另有完整历史合同。

每个返回的 `Observation` 现在包含其**真实构造提交**的擦除索引；受验证单元和锁
不变式保存这个索引。凭据认证初始 owner、Begin／work 身份与 kind，以及 false
进度标志、零错误和空 Child。`Observation::lifetime` 从真实创建推出到实际最新成员
凭据的完整区间。对于其中每一步 Journal 交错，`classified_step` 证明该完整 Host
记录保持不变，或执行了准确且满足守卫的 Host 转换。`progress_between` 证明来源
不变、取消／初始化／完成／终止存在性单调、错误数不减少、已分配 Child 保持一致。
不要求提交相邻、调用方筛选交错或公平调度。

这是连接实际生产者的原生共享状态安全合同，不是完整运行时观察的步骤分类，也没有
赋予任意回调、Node 对象／HMR、配置 group 或源合并完整 Component 语义；它不证明
最终完成。运行时没有新增历史日志，创建索引、区间推导和凭据均会擦除。

本版源码通过 **878 项定向 Verus 检查、0 错误**，完整编译内核；**87 项相关 Rust
回归**和**两个新增严格负控**通过。每个负控均要求新匹配正例、完整突变体编译和
准确命名诊断拒绝，分别丢弃借出 runner 的实际状态关联，或伪造观察的创建索引。
全部 **301 个规范负控锚点**、格式、工作区全部目标／特性的严格 Clippy、论文索引
和改动文档的本地链接通过检查；此前 299 个负控定义保持不变。前一版的
870／882／4 属于其原源码证据。本版**未运行**全内核证明、完整 Rust／Node 测试、
全量负控／校准、完整开发、发布和整个 R2 语义验收。


## 已记录原生观察的完整分类

实际 Journal 观察现在由同一个分类器覆盖**全部 13 种 Record 和未登记的托管 inverse
义务表**。`interpreted_trajectory` 从认证快照构造完整序列：初始两张表为空，末态
等于实际快照，每个原始提交都保留。调用方不提供预期初态，也不能筛选调用列表。

| 实际步骤 | 已建立的解释 |
| --- | --- |
| 内置或可扩展标量写入 | 实际 allocation 上的 R1 dependent operation；准确 outcome、所选 continuation，以及每个恢复堆上的严格 inverse |
| 恢复或拒绝／过期／阻塞尝试 | 准确的部分 inverse／operation 定义域；被拒绝的 value 尝试保持两张完整观察表 |
| 原生生命周期规则 | 现有 R1 控制规则，Restart 单独标为扩展；保留真实归属和 publication 记录 |
| 槽位／载荷替换、载荷退休或分配 | 准确的选中记录、版本／新鲜性变化，保持其他全部记录 |
| Work、清理、groups、Host、轮询控制、recipe、配置或来源 | 在同一完整输入上满足实际转换及其 guard；明确保留为实现／宿主转换 |
| 托管 inverse 登记 | 实际更早的 forward 写入、准确队列转换及未登记义务移除；跨 Journal 登记不能制造本地写入顺序 |

frame 同时保持其他每个记录的值及存在性。完整已记录状态的 stutter，等价于选中记录
**和 pending 表**均不变，不能只根据某个投影判断。即便标量内容相同，成功写入仍会
改变 depth，因而不是完整状态不变；槽位／载荷／native 版本变化、载荷退休、新分配和 inverse 登记也
不能被误分类为完整 stutter。

真实 `Journal::snapshot`、`NativeRuntime::execution_snapshot` 和
`HostStatus::execution_snapshot` 生产者导出该合同。`record_recipes_following` 为
实际返回提交认证完整分类；已登记 Value／Service 的 root 和 Child 报告在
`completed()` 中包含它，并连接原有的效果先于返回定理。索引和完整观察均擦除，
不增加运行时历史日志，也不执行额外回调。

同一个实际返回合同还证明 `local_inverses_registered`：成功前缀中，托管 inverse
属于返回 Journal 的每次写入，登记义务已经清偿。`Evidence::settled_through` 将这个
事实保持到实际返回前缀中的每个后续交错；`unique_settlement` 排除第二次消费。
函数失败返回也为已成功执行的前缀保留保证。其他写入者仍可有 pending 义务；登记
不等于 inverse 最终执行或恢复成功。

审查入口：[joint_classification.rs](../crates/cordis-kernel/src/joint_classification.rs)、
[Journal 生产者](../crates/cordis-kernel/src/joint_execution.rs)、
[原生返回生产者](../crates/cordis-kernel/src/native_runtime.rs)、
[Value](../crates/cordis-kernel/src/value_function.rs)／[Service](../crates/cordis-kernel/src/service_function.rs)
报告。`classify_step` 组合对象操作、所有者转换、frame、拒绝和 inverse 来源引理，
使用现有求解器限额。

**完整已记录原生观察不等于完整宿主观察。** opaque 载荷内部、JS 对象／Fiber／HMR
及 ALS、普通 Arc／Weak／mutex 关联、group／源合并的 Component 语义仍待完成。
显式配置或 recipe 转换只证明该转换，不赋予任意回调效果语义；原始具名端口解释仍需
别名条件。不同 Journal 保持独立，也不由此推出公平调度、最终结束、整个 R2 或整篇
论文完成。三个 partial 工作项及原有验收标准保持不变。

前一分类器批次在 Cargo 导入修复后通过 **894 项定向 Verus 检查、0 错误**，完整编译内核；
工作区全部目标／特性的严格 Clippy 通过。格式、全部 **301 个既有规范负控锚点**、
论文索引和改动文档本地链接已检查。没有增加假设、unchecked 实现、求解器限额，
也未放宽负控标准。该版本**未运行**运行测试、新增／全量负控、校准、全内核证明、
完整开发、发布和整个 R2 验收。此前 878／87／两个负控属于前一版本。新运行场景及负控留待相关集中验收：全部记录类型与清理失败／重试交错；
证明返回函数自身的本地 inverse 已登记，同时保留其他写入者的 pending 义务；拒绝
把登记当作 stutter、遗漏 pending 投影或二次清偿。已有测试及全部 301 个严格负控
定义保持不变。

## 真实执行中的共享强类型载荷

原生宿主现在用 [`SharedPayload<T>`](../crates/cordis-kernel/src/shared_payload.rs)
存储非标量服务，包括实际的 `Arc<dyn Any + Send + Sync>`。它替代普通宿主中的
`Mutex<VersionedValue<Value>>`。真实载荷、版本、私有锁、权威强类型历史和 Journal
成员由受验证 owner 共同持有；历史及对应凭据在 Cargo 编译后擦除。

`Execution::new_payload` 选择真实 Episode 的 Journal，生产 `provide` 与动态
`publish` 调用这个工厂；独立／静态存储建立明确的独立域。读取、`set`、
`ServiceHandle::set` 和可用性检查使用同一 owner。捕获保留原 owner 与原值；
`check_result` 重新读取这个 owner，接受条件恰好是实际传入的回调结果为真、且
owner 仍存活且捕获版本仍为当前版本。换成相同值也会递增版本，不能用另一个 cell 的同号版本替代
捕获的真实 owner。

共同观察现在包含 `Payload { source, revision }` 与终态 `RetiredPayload`，
分别有准确的 `PayloadReplace` 和 `PayloadRetire` 步骤。`payload_execution::indexed` 与
`Snapshot::complete_projection` 将从初次分配开始的每个真实强类型版本连接到
完整交错 Journal 中的位置，不遗漏该 owner 的任何修改。
`SharedPayload::execution_snapshot` 在持有自身读锁时观察 Journal，把实际当前载荷
和该读取时刻连接起来；owner 退休后返回 `None`，不会构造存活载荷。
共同 Journal 记录身份／版本，不序列化任意 `T`。

真实 Runtime 检查点调用
[`payload_service_snapshot` 与 `scoped_payload_service_episode_snapshot`](../crates/cordis-kernel/src/native_payload_runtime.rs)。
它们先收集载荷和标量槽的凭据，再在同一次 Journal 读取中认证真实保留的 publication、
Episode 自有服务、已捕获 imports、control、work、清理和 setup scope。
完整的 [`payloads::projection`](../crates/cordis-kernel/src/native_payload_observation.rs)
保留服务表的每个键，区分标量解析、本地载荷身份／版本、已退休载荷和外域 owner。
`project_replacement` 与真实 `Replacement::production_aliases` 保持全部无关服务
观察；指向被替换 owner 的当前别名均看到新版本。不同域保持独立，不制造共同历史。

替换将旧的可执行 `Arc` 完整交还。审查观察被擦除，结果不额外持有新载荷的运行时副本，
避免这份副本在外层宿主锁内触发用户析构。既有宿主调用者先释放 bookkeeping 锁，
再析构旧值或被拒绝的值；predicate 也在载荷锁外运行。这保持现有的可重入设计，
不构成任意用户析构函数或宿主 mutex 调度的证明。

既有释放回归暴露了固定版 vstd 锁的一个集成要求：丢弃锁不会析构其中存放的值。
现在 `SharedPayload::retire` 记录终态、清空真实存储，并在释放锁后交还载荷。
重复退休不再返回载荷；替换以 `Closed` 拒绝，capture／refresh 返回 `None`，此前
predicate 的结果也不能被接受。Journal 的 `payload::retained` 证明排除退休后的复活。
原生宿主在真实槽元数据中保留 `PayloadLifetime` guard，其普通 Rust 析构函数在最后
一个服务槽引用释放时调用这个受验证退休操作。保留的读取 Arc 仍可延长原载荷寿命。
直接使用底层 kernel 的调用者须显式退休 owner；这不宣称 Verus 已证明任意析构执行。
四项既有释放／重入回归保持原断言，并在修复后复跑。

在论文到代码的审查路径中，本轮补强 Definition 29 的操作／结果、Definition 48 的 Component 及
Definition 58 执行观察所需的真实观察输入。它**没有**证明任意 `T` 的内部修改、
一般异构效果／inverse 定律，或原始具名端口的 Component 成员资格。普通 Episode
Arc／Weak／mutex 关联、静态 context 输入、完整 JS／Fiber／HMR／ALS 和配置
group／源合并含义仍待完成。三个 partial 项和原有 R2 退出标准保持不变。

审查路径：实际 [`runtime.rs`](../crates/cordis/src/runtime.rs) 的存储与工厂
→ [`Execution::new_payload`](../crates/cordis-kernel/src/execution.rs)
→ [`shared_payload.rs`](../crates/cordis-kernel/src/shared_payload.rs)
→ [`payload_execution.rs`](../crates/cordis-kernel/src/payload_execution.rs)
→ 上述联合服务投影和 Runtime 检查点。

最终源码通过 **955 项定向 Verus 检查、0 错误**、完整内核编译、**102 项既有 Rust
回归**（原生服务、静态宿主、可逆程序与配置），以及工作区全部目标／特性的严格
Clippy。格式、全部 **301 个未改动的规范负控锚点**、论文索引及 **526 处改动文档
本地链接**检查通过；结果与本次源码哈希绑定。初次出现的四项载荷释放失败由显式
退休协议修复，没有放宽断言。本批未新增运行测试，也未执行 Node 验收、新增／全量
负控、校准、全内核证明、完整开发、发布或整个 R2 验收。前一分类器的 894 项检查
仍作为历史证据。待补充的新验收场景：并发替换与别名捕获；不同 owner 的同号
版本；predicate 执行与回复之间的替换；外层锁释放后的载荷析构重入；版本容量拒绝；
清理失败／重试期间的本地／外域值交错。已有测试和严格负控标准保持不变。

## 可恢复的强类型载荷替换

`Setup::replace_service` 和 `AsyncSetup::replace_service` 现在可以替换已声明的
原生服务载荷，并在返回前把真实逆操作登记到清理队列。root 和 Child 回调共用该入口：

```rust,ignore
setup.replace_service(greeting, String::from("updated"))?;
```

入口选择 Begin 时绑定的 provider，保留真实服务槽位，支持非标量 Rust 类型和生产
使用的 `Any` 载荷。`ReversibleValue` 继续使用现有标量 API；这个原生服务入口明确
拒绝静态存储。调用该操作不会让普通回调周围的任意计算自动获得证明。

这里把两类状态明确分开：

| 状态 | 正向替换 | 成功恢复 |
| --- | --- | --- |
| 实际 Arc、语义 head/depth | 创建新 head，增加深度 | 恢复原 Arc、head 和深度 |
| 读取版本 | 递增 | 继续递增；旧谓词结果仍然过期 |
| 清理义务 | 登记真实逆操作并保留槽位 | 只有实际受守卫的恢复成功才移除 |

真实 cell 的不变式为所有尚未恢复的 managed 深度预留版本容量。正向写入预留两次
递增，分别用于写入和自身逆操作；恢复消耗一次版本，同时减少一层深度。因此，匹配
当前存活状态的逆操作不会因为版本计数耗尽而无法恢复。逆操作类型自身的不变式由
Verus 检查，绑定它的原始状态历史。后来的 managed 写入会阻塞较早的恢复，直到
后来写入被恢复；重复执行已经完成的逆操作不能覆盖当前状态。普通 `set` 会建立新的
语义 head，并使较早的逆操作失效；不能宣称重试一定能解决这种外部冲突。

实际清理队列新增专门的强类型逆操作分支。受验证调度器选中原始槽位和票据、执行
真实逆操作，再由实际结果决定成功或失败。失败保留原逆操作及槽位保留对象，并阻塞
同组较早的清理；现有显式重试产生新票据。成功后，被替换载荷和保留对象交还适配器，
在释放 Episode 锁之后析构。用户析构函数不在受验证的载荷锁内执行。

`PayloadApply` 和 `PayloadRestore` 都是 Journal 中明确的非 stutter 步骤。
同 Journal 的正向写入取得线性 pending 义务，由真实清理登记消耗。
`Admission::pending_interval` 证明这个义务在所有中间交错步骤中持续存在。
不同 Journal 保留独立身份，不伪造跨域总序。完整强类型历史、别名投影和原生分类器
都包含这两种新修改。恢复被拒绝时保留载荷，不伪造成功写入或成功逆操作。

论文审查路径为 Definition 29／式 (31) →
[`operation`、`primitive_law`、`Inverse::interpretation`、`roundtrip`](../crates/cordis-kernel/src/payload_inverse.rs)
→ [`apply_native_payload`、`apply_payload`、`dispatch_payload_cleanup`](../crates/cordis-kernel/src/payload_cleanup.rs)
→ [runtime.rs](../crates/cordis/src/runtime.rs) 中的真实宿主入口。
操作定律覆盖整个强类型语义载体；真实 owner 选择的新 head 是显式操作参数。
`roundtrip` 从相互衔接的逆操作栈推出恢复结果，没有另行假设每个逆操作成功。
单调读取版本是实现扩展，不属于声称恢复到旧值的状态。

这补上了一个非标量原语及其生产队列组合。任意 `T` 内部可变状态、自动推进、一般
异构回调的 outcome／continuation 解释、动态别名下原 named-port Component 定理、
完整 Node／配置联合语义仍未完成。一般函数返回的步骤组合仍需继续连接。强类型恢复的
issue／观察／acknowledgement 区间已在[下文](#强类型清理的请求读取和确认)接通。
R2 原有验收条件和三个 partial 工作项保持不变。

此前强类型 inverse 批次源码通过 **941 项定向 Verus 检查、0 错误**、完整内核编译，以及 5 组宿主中的
**102 项既有 Rust 回归**。工作区全部目标／特性的严格 Clippy、格式、论文索引／审查
检查和 **301 个未改变的规范负控锚点**均通过。证明范围为 `reversible_value`、
`cleanup_groups`、`cleanup_queue`、`execution`、`lifecycle_state`。源码哈希及日志记录
在本地 `/tmp/cordis-r2-payload-inverse/checks.json`。此前 955／102 属于上轮源码，
不继承到本轮。新增强类型路径运行案例、新增／全量负控、Node 验收、全内核证明、
完整开发、发布和整个 R2 验收**未运行**。既有回归不等于新强类型 API 的运行验收。
没有增加假设、unchecked 实现或求解器限额。
新增集成场景留待集中验收：多层强类型替换；两个 consumer 乱序恢复后重试；恢复
相同值后的过期谓词回复；普通替换与退休冲突；槽位保留和析构重入；容量预留；以及
丢失逆操作、复用 head、不递增读取版本、把受阻恢复确认为成功等负控。已有测试和
严格负控标准保持不变。


## 强类型清理的请求、读取和确认

真实强类型清理调度器现在返回自身请求、载荷观察和确认的可擦除认证凭据
`Evidence<T>`。凭据由 `dispatch_payload_cleanup` 实际构造，绑定队列、原始逆操作、
票据和真实恢复结果，适配器不能用自行提供的成功标志替代受验证结果。

| 实际结果 | 凭据 | 队列确认 |
| --- | --- | --- |
| 恢复成功 | 加锁读取存活状态，随后提交真实 `PayloadRestore` | 成功确认移除原始逆操作 |
| 存在干扰 | 加锁读取当前状态，该语义状态拒绝此逆操作 | 失败确认保留原逆操作和槽位保留对象 |
| 已关闭 | 读取 owner 的真实终态 `RetiredPayload` 凭据 | 失败确认保留清理义务 |

读取对应真实历史的前缀长度，无需追加事件，可以紧接请求发生。只有成功恢复才有
写入位置。逆操作保留实际 Journal，使载荷退休后仍能认证读取。凭据映射、历史和
结果见证会从运行产物中擦除；保留 Journal 句柄不会保存旧载荷的历史值。

在同一 Journal 内，读取涵盖请求；真实恢复写入晚于读取；确认晚于本次尝试的终点。
`custody_interval` 证明同一票据在所有中间状态持续有效，且保留 admission 时的
committed providers。`microsteps` 保留分类轨迹中的全部交错提交。无论成功或失败，
`completed_attempt_stays_closed` 都证明该旧票据在任何认证后续历史中不能重新生效，
包括产生新 attempt 编号的重试。不同 Journal 仍保留独立历史，不推导跨域总序。

审查入口为 [`payload_attempt.rs`](../crates/cordis-kernel/src/payload_attempt.rs)、
[`payload_inverse.rs`](../crates/cordis-kernel/src/payload_inverse.rs) 中的实际读取／恢复，
[`payload_cleanup.rs`](../crates/cordis-kernel/src/payload_cleanup.rs) 中的队列组合，以及
[`payload_restoration.rs`](../crates/cordis-kernel/src/payload_restoration.rs)、
[`cleanup_interval.rs`](../crates/cordis-kernel/src/cleanup_interval.rs) 中的区间和后续历史定理。
这将 Definition 29／式 (31) 的具体逆操作定律连接到实际清理，并与 Definitions 58／63
的既有控制投影衔接。它补齐这一强类型协议区间，不证明任意回调、`T` 内部修改、调度
活性或剩余的一般函数、Node 和配置语义。R2 仍在推进中。

本轮源码通过 **964 项定向 Verus 检查、0 错误**、完整内核编译、5 组宿主中的
**102 项未改动 Rust 回归**、工作区全部目标／特性的严格 Clippy、格式、论文索引／审查
检查和 **301 个未改变的规范负控锚点**。证明范围为 `reversible_value`、
`cleanup_groups`、`cleanup_queue`、`execution`、`lifecycle_state`。绑定源码的本地证据
位于 `/tmp/cordis-r2-payload-interval/checks.json`。此前切片计数属于历史证据。
新增强类型路径运行案例、新增／全量负控、Node 验收、全内核证明、完整开发、发布和
整个 R2 验收**未运行**。没有增加假设、unchecked 实现或求解器限额。

新增集成场景仍留待集中验收：先因干扰失败，再恢复后续操作并显式重试；清理前退休；
没有中间写入的读取；边界间出现无关提交；新重试与重复旧确认；以及替换请求凭据、
丢失真实读取因果关系、将受阻／关闭 owner 确认为成功等负控。既有测试和严格负控标准
保持不变。
