# Child 清理失败时更新 provider

[English](update-recovery.md) · [论文审查](../paper-review-guide.zh-CN.md) · [原有 R01 义务](../r01-prewrite-replay.zh-CN.md)

本案例包含一个 provider、一个 consumer，以及 consumer 拥有的一层 Child。
一次真实可逆写入造成干扰，使 Child 的逆操作无法恢复预期状态。运行时保留 consumer
和 provider，直到显式重试成功，再恢复旧数据、激活更新后的 provider 和新的 Child。
运行不需要 Node.js、网络服务或任意异步回调。

本交付范围名为 `provider-consumer-one-child/v1`，证据由**已验证内核合同**和
**普通 Rust 宿主集成测试**组成。它不宣称完整宿主调度器、R01、公式 (55) 或整篇论文
已经证明。原有 R01 验收条件及原文审计／反例状态均保留；一般恢复、全局终止和合流后置。

## 独立复现

在仓库根目录使用固定工具链及已缓存依赖：

```sh
# 用户可直接运行的示例，输出经过断言检查的事件和 JSON 结果。
cargo run -p cordis-verus --example update_recovery --locked --offline

# 原生 owner／票据案例、实际 Runtime 案例及 action 票据回归。
python3 -B scripts/reproduce-update-recovery.py --offline

# 同时重新运行选定内核证明。
python3 -B scripts/reproduce-update-recovery.py --offline --proof

# 对五处真实实现进行严格变异检查。
python3 -B scripts/check-update-recovery-controls.py
```

依赖尚未下载时，可从 Cargo／复现命令中去掉 `--offline`。证明检查前使用
`./scripts/install-verus.sh` 准备 Verus。`target/update-recovery/report.json`
记录源码哈希、精确命令、原始日志、实际数据和是否运行了证明；未加 `--proof` 时明确
记录 `not_run`，不沿用旧证明计数。负控报告位于
`target/update-recovery-controls/report.json`。整个内核的开发验收另外由
`python3 -B scripts/record-development.py --offline` 记录。这些命令不代表发布平台
验收或全量负控回归。

## 实际发生的事情

provider 提供可逆计数器。consumer 显式依赖计数器并提供 marker；Child 显式依赖这
两个服务。因此，Child 有真实的 committed 服务依赖；不会把父子所有权暗中当作依赖。

| 阶段 | 旧计数器 `(值, 逆操作深度)` | 结果 |
| --- | --- | --- |
| provider 启动 | `(10, 0)` | 发布服务 |
| consumer、Child 分别写入 | `(13, 2)` | 保留两个真实逆操作 |
| 显式注入干扰写入 | `(17, 3)` | 干扰也有自己的逆操作 |
| 请求更新 provider | `(17, 3)` | Child 恢复失败；consumer、provider 不能清理 |
| 不重试而再次轮询 | `(17, 3)` | 失败继续阻塞，不隐式重试 |
| 恢复注入的写入 | `(13, 2)` | 原 Child 逆操作重新满足定义域 |
| 显式重试 Child | `(11, 1)`，再到 `(10, 0)` | Child、consumer、旧 provider 依次释放 |
| 新 provider 与新 Child 启动 | 新计数器 `(23, 2)` | 新数据从 `20` 开始，两层插件重新执行 |
| 最终关闭 | 新计数器 `(20, 0)` | 三个插件全部移除 |

干扰通过原始资源句柄显式注入，不属于插件的受管操作。保证是检查干扰、拒绝错误恢复
并保留责任，不是排除所有外部写入，也不是自动回滚。原生案例还伪造受管逆操作的成功
确认，检查旧／重复回复、action 与 restore 尝试的新鲜性，以及旧 Episode 回复不能
改变新 owner 的队列。

## 论文 → 合同 → 执行代码 → 证据

论文位置采用 `upstream.lock.json` 的固定版本。定义 54／L-Unload 位于第 36–37 页，
精确解释见论文审查 PR-01。严格逆操作定义域采用组件／逆操作约束的显式 R1-DOMAIN
修订，不宣称原文所有操作都是总函数。

| 保证 | 可执行合同与证明 | 实际调用／复现证据 |
| --- | --- | --- |
| 恢复期间保留 committed provider（定义 54、L-Unload） | `Kernel::begin_cleanup`／`finish_cleanup`；`binding_protects_provider`；`cleanup::update::failed_child_keeps_chain` 对未获得新的 Child 授权确认的任意有限清理命令历史，推出两层依赖保护 | 共享／原生生命周期适配器；两个案例读取真实 committed 绑定，并拒绝过早清理 |
| 失败保留真实逆操作（严格组件／逆操作解释） | `Inverse::restore_following` 同时检查值和深度；`CleanupQueue::restore_value` 拒绝后保留同一逆操作；`NativeRuntime::fail_managed_execution` 从真实失败队列导出失败凭据 | `Setup::update_reversible` 与原 registered root；拒绝后值仍为 `(17, 3)` |
| 宿主成功标志不能替代受管恢复 | `RecordedExecution::complete_result` 拒绝受管槽位的宿主确认；恢复通过 `dispatch` 调用原逆操作 | 原生案例在重试前后伪造成功，均被拒绝 |
| 重试产生新尝试，旧回复不能释放（落实 L-Unload 顺序的实现协议） | `retry_execution`、`consumed_ticket_never_returns`、清理队列的精确票据／已交付检查 | 原生案例检查 action 与 restore attempt 增长；`cleanup_protocol` 回归覆盖旧 action 回复及新 Episode |
| Child 请求与逆操作指向同一所属 Child | `enqueue_native_child` 原子生成请求／逆操作；`register_shared_child` 绑定父 Episode；`retire_shared_child` 实际退休；原生 `release` 单独记录 Child Unload | 原生案例消费真实请求和逆操作；宿主使用 `Setup::mount`；不把 retirement 当作完成 Unload |
| 恢复后才能释放 provider，再激活更新 | `release_execution` 从工作／队列排空导出结果并执行真实 L-Unload；`begin_managed_execution` 创建下一 Episode | Runtime 使用 `update_plugin`、`retry_cleanup`、`settle`、`dispose_all`，断言释放／启动事件顺序及新旧数据 |

依赖链定理要求真实 committed 绑定和失败凭据。Begin 构造绑定；失败合同把队列失败
经 `LifecycleState`、`NativeHost` 传到 `NativeRuntime`，不假设清理成功。有限历史
的每一步必须满足生产 `cleanup_step` 关系；`execute_cleanup` 和 `run_cleanup`
建立该关系。重试成功来自实际逆操作；没有假设任意干扰环境最终都会恢复所需状态。

源码：[依赖链证明](../../crates/cordis-kernel/src/cleanup_update.rs)、
[清理协议](../../crates/cordis-kernel/src/cleanup_protocol.rs)、
[真实工作与队列释放](../../crates/cordis-kernel/src/execution_lifecycle.rs)、
[受管确认边界](../../crates/cordis-kernel/src/managed_lifecycle_callbacks.rs)、
[原生案例](../../crates/cordis-kernel/examples/support/update_recovery.rs)、
[Runtime 案例](../../crates/cordis/examples/support/update_recovery.rs)。每份案例实现由
可运行示例与集成测试共用。

## 验收与边界

五项负控变异实际实现：把失败报告改为成功、绕过释放凭据、丢弃保留载荷、忽略逆操作
深度、拆开 Child 请求和逆操作的身份。每项要求新的匹配正向证明、完整 mutant 编译
成功，并在指定合同处被拒绝。超时、语法错误和其他位置失败不算有效证据。

不宣称证明任意回调、析构、JavaScript、外部 I/O、操作系统持久性或调度公平性。
宿主闭包与更新路由由集成测试检查；协议安全和所选数据操作在 Cargo 实际编译的内核
源码中验证。本案例不把普通 `FnOnce` 失败的 `Drained` 策略当作恢复成功。完整父函数
等价、任意多 owner 恢复、Node 恢复及任意调度合流继续保留在原有工作清单中。
