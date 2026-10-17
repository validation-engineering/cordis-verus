# R2 生产执行验收

[English](r2-acceptance.md) · [里程碑](paper-refinement-roadmap.zh-CN.md) · [源码映射](paper-refinement-map.md)

R2 在 **managed-production/v1** 明确范围内完成：受支持的可执行托管函数载体，以及
原生、Node 引用／协议、配置扩展。第 5 包组合前四包的语义审查和可复现验收，保留
原有三条退出条件及原论文审计结论。与 R1 一样，完成声明带有明确的解释范围。

## 三条退出条件对应什么

| 原始 R2 条件 | 实际代码与证明 | 贯通验收 |
| --- | --- | --- |
| 托管入口的真实参数、结果、延续和 inverse 来源 | `Plugin::native_function` → `NativeRuntime::run_managed_root` → `Execution::run_function`；`Step::interpretation`、`Report::interpret_queue`、注册返回的 `execution_interval` | schema 默认值成为实际 Child 参数，执行混合标量／类型化效果，真实结果选择延续；冲突阻塞保留的 inverse，恢复后回到原输入。反例删除返回处的效果见证、丢弃选定延续。 |
| 组合准入、调用、并发落地、排空、释放，调用者无需给出预期结果 | 原生 owner／Journal 与 `configuration_snapshot`；NodeRuntime／Bridge 的实际声明及 `HostSnapshot::production_trace`；既有 issue／read／restore／acknowledge 合同 | Loader 失败保留已提交配置，旧 Episode 访问被拒绝，provider 等待 consumer，恢复重建新身份；Node 失败保留真实替换对象与依赖，在新重试 pending 时拒绝旧回复。 |
| 每一步都有适用的语义关系 | native／Node 的 `classified`、`production_trace`，Bridge 精确转换和配置／来源投影 | 从实际生产所有者取得快照；反例将控制停顿冒充完整观察不变、提前结束 pending 声明、替换真实 Insert 位置，必须在指定合同被拒绝。 |

[机器可读审查表](paper-refinement-plan.json)把六个 R2 工作项完整分配到三条原始条件，
列出执行与证明入口。清单检查只验证引用与范围一致性，不能代替 Verus 或语义审查。
本包复用已建立的生产合同、增加贯通执行证据，不通过包装定理增加证明数量。

## 两条真实执行路径

[原生示例](../crates/cordis/examples/r2_production.rs)使用一个真实 Loader／Runtime、
配置源文件、group 和托管 Child，检查八个阶段：加载、清理阻塞、provider 保留、
inverse 排空、配置重建、参数更新、源文件保存、最终释放。每个阶段都捕获实际联合
生产快照。第二个 writer 制造真实类型化冲突；示例显式卸载它，因为服务依赖不是
所有权。配置恢复 pending 时禁止保存；重建产生新的 root／Child 身份，后续更新把
标量从 13 改为 15，最终清理恢复为 10。保存后读取实际文件确认结果，第二次保存无变化。
没有使用模拟状态机，也没有给内核传入人为制造的预期执行轨迹。

```sh
cargo run -p cordis-verus --example r2_production --locked --offline
```

[Node 案例](../tests/node-compat/r2-acceptance.test.mjs)使用真实 addon、Driver 和
HostBridge，动态发布 JS 对象，绑定真实 Child consumer，替换对象并注入清理失败。
失败后仍可读取实际替换对象。新票据重试期间，旧回复被拒绝且当前快照不变；只有
consumer 成功确认后 provider 才能清理。全过程检查引用／协议快照。测试覆盖适配器
行为，形式化证明覆盖所调用的内核合同，不把任意 JS 回调的计算视为已证明。

```sh
node scripts/build-node.mjs --offline
node --test --test-timeout=30000 tests/node-compat/r2-acceptance.test.mjs
```

## 统一复现

使用固定工具链和已缓存依赖：

```sh
python3 scripts/check-r2-acceptance.py --offline
python3 scripts/check-r2-acceptance.py --check
```

第一条命令先执行覆盖三条退出条件的固定 12 个 canonical 反例，使过期的诊断定位
在耗时的整体流程前暴露。每个反例都需要新鲜匹配正例、完整变异源码编译，以及指定
函数、诊断类型和源码位置的准确拒绝。然后仅调用一次 `record-development.py --offline`，
执行整核证明、Rust／Node 回归、全部示例和提取／安装包检查，从实际日志确认两条
贯通案例。两个阶段必须绑定同一份未变化的源码。超时、资源耗尽和编译错误不能作为
成功反例证据；提前清理确认需要在成功和失败两个分支都被拒绝，不依赖求解器先报告哪一个。

报告位于 `target/r2-acceptance/report.json`。基线、变异源码、编译产物和原始验证日志
保存在 `target/r2-acceptance/` 下的新证据目录，失败时也保留。报告绑定全部源码、开发
记录／日志、工具产物、选定反例和输出。`--check` 只复核这些证据，不重新证明，也不能
刷新过期证据。仓库内的[开发记录](development-report.json)提供对应的源码绑定结果。
新 checkout 需运行命令产生本地 R2 报告；里程碑标签本身不是通过证据。

这不是完整 318 项反例回归或其校准。报告明确保留 `fullNegativeControls: not_run`、
`scopedCalibration: not_run`、`releaseAcceptance: false`、`paperCompletion: false`。

## 明确范围与后续工作

完整受验证载体包括有限存储的 root／Child 函数、受验证标量效果与类型化替换、全部
原生 Journal 记录及 pending inverse、精确的 owner／Episode／work／清理协议、类型化
配置／来源历史、Node 协议状态和真实 Bridge 引用身份。Ghost 历史会被擦除，本包不
增加用户运行依赖或运行日志。

- 任意回调计算、可变 `T`／JS 对象内部及未验证效果实现没有效果正确性证明；加入托管
  解释器前仍需提供对应定律和执行连接。它们的额外影响不能被宣称为完整观察停顿。
- 分配语义涵盖共享别名；字面命名端口 Component 投影仍需明确的读写范围和单别名
  条件，不能假定动态解析恒定或冲突别名相互独立。
- Restart、多版本 publication、动态接口和配置是分别规定的扩展；只有对应投影不含
  扩展时才进入严格论文控制闭包。函数效果与 inverse 仍通过实际调用／回执连接，
  单靠控制投影不能证明其语义。
- 同一实际 Journal 的所有者共享顺序；独立 Journal 和 Node 引用／协议历史保留各自
  顺序及实际守卫截面，不从数字 domain 相同推断实例相同，不捏造全局时钟。
- 普通适配器同步、Node-API／JS／ALS、弱引用真实性、JSON／URL／IEEE 转换、错误
  汇总、调度、外部静态 lease 和文件系统持久性保留明确边界。案例测试这些行为，
  不将其提升为形式化证明。group／include 是所属注册序列，不是原子论文 Component，
  也不证明任意 factory 代码。

以上是 R1 和前四包已有条件，没有把缺失的 inverse 定律或正确执行历史改成假设。
托管解释器、精确修改、生产历史及来源定律仍由证明承担。一般复杂交错恢复属于 R3；
全局推进、调度条件、终止与合流属于 R4。R5 仍需原论文整体审计与发布／平台验收。
原始反例和四项集成审计状态均保持不变。
