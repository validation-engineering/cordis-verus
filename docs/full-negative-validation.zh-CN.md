# 完整负控验证

[English](full-negative-validation.md) · 简体中文

发布验证会有意修改内核操作、守卫或规格，要求证明拒绝这些修改。
全部 121 项 canonical mutation 都必须先编译成功，再在验证**整个 crate** 时产生明确的
合同失败；未修改的内核也必须验证通过。超时、资源上限、前端错误或不完整结果均不能
满足这项要求。

## 执行与回收

执行器默认使用一个 worker，总 CPU 预算不超过两个可用核心，并考虑进程 affinity 与
Linux cgroup 配额。未修改内核的基线使用与 mutation worker 相同的线程数，不再隐式
启动九个线程。显式配置及实际生效的预算都会记入结果：

```sh
CORDIS_NEGATIVE_JOBS=1 CORDIS_NEGATIVE_THREADS=2 CORDIS_NEGATIVE_TIMEOUT=2400 \
  python3 scripts/record-verification.py --offline
```

`CORDIS_NEGATIVE_CPU_BUDGET` 可以在检测到的 CPU 上限内提高默认预算。增加并发不保证
更快，因为每个 Verus 线程都可能占用一个 SMT solver。调整 timeout 只影响墙钟时间，
不改变求解资源上限或证明合同。普通本地发布验证仍会重新执行全部负控。

每次 verifier 调用拥有独立进程组。超时、取消和终止会清理 Verus 及其 solver 后代；
默认情况下，一个 worker 失败后，执行器停止派发，并取消正在执行的其他 worker。标准输出、诊断及
`.meta.json` 阶段记录保留，包括耗时、命令、退出状态、源码指纹和取消状态。任务队列只
保留当前 worker 预算允许的工作，不再预先提交全部 121 个任务。

每个进程组只发送一次终止请求。监督器观察主进程退出后，直到组内清理完成才回收它，
使进程组标识在清理期间保持占用。Python 支持时使用 `waitid(WNOWAIT)`，否则在 macOS 上使用
`kqueue(NOTE_EXIT)`；实际方法写入每次阶段记录。阶段记录保留进程组快照、信号及清理错误；清理失败不能把超时或
取消变成可接受的证明证据。CI 步骤使用 `exec`，使取消信号直接到达监督器。强制终止
仍可能留下不完整阶段文件，汇总器会拒绝这些文件。

## 失败后继续收集

使用 `--keep-going` 可以诊断本轮或本分片的全部 mutation：某项 mutation 未通过负控
验收时，记录失败后继续执行后续项。例如资源耗尽、进程成功清理后的超时，以及变异后
意外验证通过，仍算失败，但不会再遮挡后续负控。未修改内核的基线必须先通过。
取消、清理失败和基础设施错误仍会停止执行；运行被中断时，该模式不保证得到完整结果。

在 GitHub Actions 中选择 **Full release validation → Run workflow**，启用
`diagnostic_keep_going`，保持 `create_draft` 关闭。对应的命令为：

```sh
gh workflow run release-validation.yml \
  --repo validation-engineering/cordis-verus --ref main \
  -f diagnostic_keep_going=true -f create_draft=false \
  -f include_macos_intel=false
```

该模式须显式开启；普通发布运行仍在分片内遇到失败后停止。诊断运行保持同样的整 crate
检查、资源上限和进程清理，失败后也保留原始工件，不使用 `continue-on-error`。
基线和分片任务会在上传工件前，将简明 JSON 摘要写入控制台，并将相同的报告结果写入
Actions 任务摘要，包括来源提交、运行与尝试编号、基线结果、逐项结果和诊断覆盖数量。
因此，上传失败后仍能看到哪些负控已经执行。缺失、中断或损坏的报告会明确标记为不完整。
该展示不能恢复缺失的原始证据，也不会被发布汇总器接受；验证和上传的失败状态保持不变。

只要有负控失败，分片最终仍以失败退出。诊断运行会跳过 quality 与 draft-release 任务，
即使全部负控通过也不会进入这两个任务。同时请求诊断模式和创建草稿时，工作流会在
计划任务中直接拒绝，在验证开始前报错。

在本地诊断全部负控：

```sh
python3 scripts/check-negative.py --keep-going --jobs 1 --threads 2 --timeout 2400
```

在本地诊断一个分片时，使用新的输出目录，按需对其他索引重复执行。单片只覆盖分配给它的
负控：

```sh
python3 scripts/negative-shards.py run \
  --shard-index 0 --shard-count 18 --output target/negative-diagnostics/shard-0 \
  --jobs 1 --threads 2 --timeout 2400 --compile-timeout 300 --keep-going
```

`diagnostic.json` 按 canonical 顺序记录各项结果，失败项包含错误类型与消息。计数区分
选定、已尝试、通过、失败和未执行的负控；`complete: true` 表示已尝试全部选定项，
并不表示没有失败。单体执行器将其写入 `target/proof-negative/`，分片写入指定输出目录，并保留原始 stdout、stderr
及阶段元数据。完整执行后的诊断分片在 `shard.json` 中记录：全部负控通过时状态为
`diagnostic-passed`，否则为 `failed`，且始终为 `releaseAcceptance: false`。
宣称收集完整之前，应检查报告中是否仍有未执行的负控。

诊断证据不能用于发布验收：汇总器会明确拒绝，包括全部通过的诊断运行。修复问题后，
应在同一份最终源码快照上重新运行普通完整门禁，将 `diagnostic_keep_going` 设为
`false`，或在本地去掉 `--keep-going`。完整收集诊断用于规划修复；发布验收仍要求
每个选定平台完成新一轮普通验证。

## CI 并行执行与证明范围

发布工作流默认选择 Linux x64 和 macOS Apple Silicon（ARM64）；手动触发时设置
`include_macos_intel=true` 可加入 macOS Intel。工作流先在每个选定平台分别验证一次
未修改的整 crate。预检保留 `--trace --time` 诊断，所有选定平台全部通过后才启动负控
分片，避免相同的基线失败在整个矩阵中重复发生。

每项 mutation 仍编译并验证**整个变异后的 crate**，使用一个 worker、两个 Verus
线程，单次编译时限为 300 秒。同一份平台计划为预检和分片提供一致的证明时限：

| 平台 | 单次证明时限 | 分片数 | 每片最多负控 | 编译与证明总预算 | 作业余量 |
| --- | ---: | ---: | ---: | ---: | ---: |
| Linux x64 | 40 分钟 | 18 | 7 | 315 分钟 | 45 分钟 |
| macOS ARM64 | 60 分钟 | 25 | 5 | 325 分钟 | 35 分钟 |
| macOS Intel（可选） | 90 分钟 | 41 | 3 | 285 分钟 | 75 分钟 |

计划器检查负控覆盖完整，并在六小时分片作业内至少预留 30 分钟用于安装、证据检查、
清理和上传。预检作业在证明时限之外另留 15 分钟。负控任务最多同时运行十二个。
这些是执行预算，并非实测证明耗时；不增加求解器资源上限，也不改变证明合同。

分片复用本平台在**同一 workflow run 和 attempt** 中通过预检的基线，原始输出、阶段
元数据与哈希随分片证据一起保留；不跨提交或运行缓存。独立本地分片仍重新运行基线；共享预检复用要求完整的 CI run
和 attempt 标识。

`scripts/negative-shards.py collect` 只接受准确且完整的分区，重新检查原始 stdout、
stderr 和调用元数据，包括共享基线。证据绑定完整源码输入哈希、canonical mutation
内容、verifier／solver／证明库字节、平台、线程设置及 GitHub run 和 attempt。缩小
验证范围的 flags、源码变化、缺项或重复、摘要篡改、取消、清理失败及资源错误都会使
汇总失败。最终 mutation 列表保持 canonical 顺序。

每个平台的 quality 任务收集本平台计划中的全部分片结果，并完成正向证明、测试、示例、软件包
构建与安装检查。只有完整汇总报告可以进入 `verification/v3`；预检或单片绿色不能
代替发布验收。每个选定平台都必须通过全部 121 项整 crate 负控及完整 quality 门禁，
才能创建运行时草稿。草稿的产物与证据必须准确对应本次选定的平台；未选择 Intel 时，
不宣称本次已验证 Intel，也不提供 Intel 产物。

工件名称带平台、attempt 和分片标识。失败后应重跑**整个 workflow**；只重跑失败任务会
混用不同 attempt，汇总器会明确拒绝。汇总器不能认证任意本地 JSON，它信任受检查的执行
环境与 GitHub 工件传输，再校验内容一致性与精确输入绑定。

在本地分布执行时，使用相同且不变的源码快照与平台，将全部索引分别写入新目录，然后用
`record-verification.py --negative-shards <directory>` 传入这些目录的父目录。
单个分片可以用于诊断，但不能作为发布结果。CI 记录绑定其 run／attempt，不能与本地
生成的记录互换。

## 证明稳定性

基线与变异调用统一使用 `--multiple-errors 0`。在
[固定版本的 Verus 实现](https://github.com/verus-lang/verus/blob/168759867f8c4ba0be848f5a3e438c75cee3e6e3/source/rust_verify/src/verifier.rs#L806)
中，它只在某个 `CheckValid` 首次得到 `Invalid` 后停止追加诊断查询，不跳过首次查询、
其他函数，也不减少正常基线必须完成的主证明义务。默认的追加查错可能在已有明确合同
失败后再次耗尽资源；此设置只控制该诊断搜索，不缩小证明范围或增加资源上限。
主查询因资源限制返回 `unknown` 仍是失败，任何实际报告的资源错误仍会使负控结果被
拒绝。调用元数据与汇总器要求基线和所有变异统一采用这个固定设置。

该固定版本在追加诊断预算为零时，也会给成功查询输出“not all errors may have been
reported”提示。此提示本身不表示跳过证明，仍以验证统计与完整错误日志判定结果。

`Kernel::release_provision` 使用 `#[verifier::spinoff_prover]` 获得独立求解上下文，避免
变异 crate 中此前失败查询的影响。它的可执行函数体、前置条件、后置条件和资源上限
均未改变。完整正向及负控检查仍负责验证这种证明组织方式；单独的诊断检查不是发布证据。

组合证明 `causal_normalization::adjacent_swap`、
`fresh_semantics::configuration_preservation` 和 `rewrite_confluence::swap_frame`
在证明体内隐藏 `primitive_theory` 的展开，使用已证明子引理的合同，避免不必要的
量词理论展开。具体插入示例在组合前显式调用已有 operation 引理。公开合同、可执行
行为、mutation 定义和求解器资源上限保持不变；定向负控仍须在完整变异 crate 中产生
明确失败，并且没有资源错误。

具体 foreign-child 示例把恢复与注册表取值、末端状态搬运、目标执行分别放入已证明的
辅助引理，组合时使用其合同，避免在同一查询里展开所有状态与量词理论。已有公开后置条件、
可执行代码及负控清单保持不变。局部耗时诊断只用于选择证明组织方式，最终验收仍依赖
完整正向证明和整 crate 负控。

删除归纳证明通过已证明的 `fragment_landing_guard` 引理取得每次 landing 的守卫条件。
删除私有依赖排除条件时，会暴露一个小而明确的合同义务，避免在整个归纳上下文里搜索。
具体前缀证明复用 fragment 合同，不重复证明更强的条件。公开合同和资源上限不变，
资源失败仍会使负控证据被拒绝。

token 排除、provision 逆操作对应的 restriction、单步加载 target 分别由已证明的
`removal_excludes_retained_token`、`provision_receipt_action`、`loading_step_target`
小引理给出。搬运、恢复和区间证明使用这些合同，避免重复执行大范围量词搜索。
observational journal 不变量组合已验证的单项 `provided_journal_entry`，避免在量词中
重复展开生命周期推理。owner 删除的恢复证明在已有投影合同足够时隐藏 child undo。
`invocation_record_metadata` 与 `retained_invocation_prior_landing` 分别检查 receipt
元数据与定位原始 landing 的历史推理。
这些辅助引理仍由同一次整 crate 验证检查，没有新增假设；守卫或投影变异仍须产生明确
合同失败，任何资源失败仍会使整项负控结果不可接受。

另见[验证门槛](validation.md)、[发布流程](releasing.md)，以及
[执行器](../scripts/check-negative.py)／[汇总器](../scripts/negative-shards.py)在
`scripts/tests/` 中的回归。

构造等式与单条记录的事实先由独立引理证明，再供较大的组合证明使用。
`swap_construction` 确定运输后的后缀，`last_mapped_token` 确定压缩后的日志位置，
`landing_catalogue_equation` 确定捕获的 owner。顺序、插入、保留和 Fresh 落地证明
也将局部事实与带量词的整段执行推理分开。`FreshDriver::step` 通过
`instruction_receipt_metadata` 获取 receipt 身份和 actor 控制记录保持不变的事实；
旧卸载示例通过 `related_table_entry` 获取表域与值关系。这些事实先由小引理证明，
再供包装层组合使用。既有公开前提与后置条件保持不变，
错误变异可以在更小的引理中被拒绝，减少下游组合查询的资源耗尽。每个引理仍须
通过未变异整库的验证，其结论不会被作为未经证明的假设加入。选定证明的探针
仅用于调试，完整 crate 的负向验收标准保持不变。

`program_trace::allocation_monotone` 隐藏事件关系 `ack`，在序列归纳中使用
`acknowledgement_frame` 已证明的合同，避免再次展开每种事件的注册和历史条件。
历史名称复用变异仍须触发原有的名称不可复用合同。
`Kernel::compact_bindings` 将保留位置的扩展、最终图不变量与绑定等价关系的恢复
拆成私有且经过验证的辅助引理。循环使用这些引理的合同；可执行过滤过程和公开
后置条件保持不变。反转 live 条件仍须违反经过检查的前提，任何附带的资源错误
仍会使整个负向结果不合格。

`mixed_grammar::restore_retires` 在 journal 归纳中隐藏 `undo` 的具体展开，使用单独验证的
子插件逆操作退休合同。交换帧证明组合已有的交换与后缀合同，不再展开状态转换、transport
或跨越守卫定义。共享恢复示例将前向目标事实与一般删除定理分开，并使用已证明的投影
等价关系得到终态数值。既有公开前提与保证全部保留；示例轨迹额外暴露实际的 owner
和外部 journal token 以及 provider 所有权；前向示例显式检查保留下来的调用解析到
committed provider 并成功执行。Fresh 终态恢复在组合 episode 和终态合同时，隐藏
episode 回放谓词的内部展开。可执行转换、变异定义和求解资源上限均未改变。

子插件逆操作的搬运先通过 `child_inverse_state` 检查具体退休状态等式，再组合已有合同。
保留 Active 子插件的父插件恢复示例直接使用 `restore_retires` 定理；退休位的责任仍由
同一次整 crate 验证中的底层子插件逆操作证明承担。
