# 完整负控验证

[English](full-negative-validation.md) · 简体中文

发布验证会有意修改可执行内核代码，要求证明拒绝这些修改。
全部 114 项 canonical mutation 都必须先编译成功，再在验证**整个 crate** 时产生明确的
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
一个 worker 失败后，执行器停止派发，并取消正在执行的其他 worker。标准输出、诊断及
`.meta.json` 阶段记录保留，包括耗时、命令、退出状态、源码指纹和取消状态。任务队列只
保留当前 worker 预算允许的工作，不再预先提交全部 114 个任务。

每个进程组只发送一次终止请求。监督器观察主进程退出后，直到组内清理完成才回收它，
使进程组标识在清理期间保持占用。Linux 使用 `waitid(WNOWAIT)`，macOS 使用
`kqueue(NOTE_EXIT)`。阶段记录保留进程组快照、信号及清理错误；清理失败不能把超时或
取消变成可接受的证明证据。CI 步骤使用 `exec`，使取消信号直接到达监督器。强制终止
仍可能留下不完整阶段文件，汇总器会拒绝这些文件。

## CI 并行执行与证明范围

发布工作流先在三个平台分别验证一次未修改的整 crate。预检保留 `--trace --time` 诊断，
三个平台全部通过后才启动负控分片，避免相同的基线失败在整个矩阵中重复发生。

随后每个平台运行十八个分片，每片六或七项 mutation，使用一个 worker 和两个 Verus
线程。每项 mutation 仍编译并验证**整个变异后的 crate**。单次编译时限为 300 秒，
证明时限为 2,400 秒；最多七组编译与证明共 315 分钟，在六小时作业时限内为安装、
证据检查及上传预留 45 分钟。负控任务最多同时运行十二个。这些墙钟时间预算不增加
求解器资源上限，也不改变证明合同。

分片复用本平台在**同一 workflow run 和 attempt** 中通过预检的基线，原始输出、阶段
元数据与哈希随分片证据一起保留；不跨提交或运行缓存。独立本地分片仍重新运行基线；共享预检复用要求完整的 CI run
和 attempt 标识。

`scripts/negative-shards.py collect` 只接受准确且完整的分区，重新检查原始 stdout、
stderr 和调用元数据，包括共享基线。证据绑定完整源码输入哈希、canonical mutation
内容、verifier／solver／证明库字节、平台、线程设置及 GitHub run 和 attempt。缩小
验证范围的 flags、源码变化、缺项或重复、摘要篡改、取消、清理失败及资源错误都会使
汇总失败。最终 mutation 列表保持 canonical 顺序。

每个平台的 quality 任务收集本平台十八片结果，并完成正向证明、测试、示例、软件包
构建与安装检查。只有完整汇总报告可以进入 `verification/v3`；预检或单片绿色不能
代替发布验收。运行时草稿仍要求全部三个平台通过完整 quality 门禁。

工件名称带平台、attempt 和分片标识。失败后应重跑**整个 workflow**；只重跑失败任务会
混用不同 attempt，汇总器会明确拒绝。汇总器不能认证任意本地 JSON，它信任受检查的执行
环境与 GitHub 工件传输，再校验内容一致性与精确输入绑定。

在本地分布执行时，使用相同且不变的源码快照与平台，将全部索引分别写入新目录，然后用
`record-verification.py --negative-shards <directory>` 传入这些目录的父目录。
单个分片可以用于诊断，但不能作为发布结果。CI 记录绑定其 run／attempt，不能与本地
生成的记录互换。

## 证明稳定性

`Kernel::release_provision` 使用 `#[verifier::spinoff_prover]` 获得独立求解上下文，避免
变异 crate 中此前失败查询的影响。它的可执行函数体、前置条件、后置条件和资源上限
均未改变。完整正向及负控检查仍负责验证这种证明组织方式；单独的诊断检查不是发布证据。

组合证明 `causal_normalization::adjacent_swap`、
`fresh_semantics::configuration_preservation` 和 `rewrite_confluence::swap_frame`
在证明体内隐藏 `primitive_theory` 的展开，使用已证明子引理的合同，避免不必要的
量词理论展开。具体插入示例在组合前显式调用已有 operation 引理。公开合同、可执行
行为、mutation 定义和求解器资源上限保持不变；定向负控仍须在完整变异 crate 中产生
明确失败，并且没有资源错误。

另见[验证门槛](validation.md)、[发布流程](releasing.md)，以及
[执行器](../scripts/check-negative.py)／[汇总器](../scripts/negative-shards.py)在
`scripts/tests/` 中的回归。
