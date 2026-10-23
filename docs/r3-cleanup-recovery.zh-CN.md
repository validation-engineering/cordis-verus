# R3：通过生产清理派发器恢复

[English](r3-cleanup-recovery.md) · [生产恢复](r3-production-recovery.zh-CN.md) · [里程碑](paper-refinement-roadmap.zh-CN.md)

生产混合清理派发器现在将真实 scalar／typed 恢复尝试接到 registered 函数保留的逆操作
后缀。在明确的实际执行条件下，有限组合证明可以推出恢复成功以及返回 Begin 值。
这推进了生产实现与式 (55) 的对应；**R3 仍在进行**。

## 实际执行及保留证据

Rust 宿主通过 `Cleanups::pop` 调用 `Execution::dispatch_payload_cleanup`。
同一段已验证队列实现选择实际动作、执行带守卫的恢复、确认真实结果并返回 completion。
普通回调和 Child 清理保持独立分支。

每次受管清理现在携带实际派发前后的队列快照，作为擦除证据。
`Dispatch::authentic` 与 `finished` 是这一生产入口的后置条件，将快照对应到实际
选中的槽位、票据、恢复尝试和确认。scalar 分支也向上传递与 typed 分支相同的完整
队列变化合同。

值观察来自 scalar 实际提交或 typed 尝试的持锁读取。`recorded` 在真实 Journal
检查点解码该观察；typed 成功结果使用恢复对象的真实来源历史和记录的 revision。
退休的 typed 对象被解释为缺失，不会被赋予虚构的值。新增证据均为 `Ghost` 数据，
不会增加运行时历史缓存、payload 克隆或额外加锁。

## 真实返回建立的合同

| 保证 | 实际来源及证明 |
| --- | --- |
| 成功恰好对应严格逆操作定义域 | `Dispatch::recovery`、`strict_step`：真实观察值等于所选逆操作捕获的输出 |
| 成功恢复捕获的输入，且仅消费当前槽位 | 实际 scalar／typed 写入、确认及 `finished` 队列变化 |
| 失败保留同一个逆操作及所选槽位 | 实际返回队列；`progress` 保持剩余恢复的可选结果及尝试处的局部值 |
| 重试保留逆操作并使用更新票据 | `Execution::retry` 传递槽位、等待序列不变以及同 token、更大 attempt；`resumed_inverse` 组合两次真实 completion |
| 完成后的旧票据持续失效 | `completed_attempt_stays_closed` 使用任一分支的真实 Journal 收据，覆盖后续重试 |

严格定义域按 `(Journal, allocation)` 确定，而非服务名，因此别名会指向同一逆操作
定义域。观察值包含可逆语义状态；仅 payload 内容相等不足以使重试成功。
失败保留的是实际尝试时的状态，不一定是外部写入之前的状态。整个派发／读取／写入／
确认区间也不被宣称为原子操作。

## 从保留后缀到有限清理序列

`managed_cleanup_path` 使用实际返回的派发结果。前后队列来自这些结果保留的边界，
不由调用方另行提供替代快照。`values_at` 根据真实输出构造值轨迹；`pending` 解释
尚未消费的逆操作，并跳过之前成功清理留下的 `None` 槽位。

`linked` 是明确的充分来源条件：

- 结果属于同一个已接入 Journal 的队列，Journal 前缀有序，attempt 身份严格递增；
- 相邻实际槽位向量衔接，每次选择本调用后缀中最后一个非空槽位；
- 每次实际读取与此前构造的值轨迹一致。

`RegisteredReport::cleanup_progress` 从已建立的真实 Begin／返回恢复合同出发，
证明每个有限前缀保持剩余恢复义务。`cleanup_attempts_succeed` 从这些来源条件推出
每次实际逆操作成功。后缀全部消费后，`cleanup_recovers_begin` 证明构造出的值结果
等于真实 Begin 值。期望结果表和逆操作成功均不是额外前提。

这些条件会排除这条连续轨迹中的冲突失败读取。[交错恢复证明](r3-interleaved-recovery.zh-CN.md)
现在将真实外部受管写入、阻塞尝试、外部恢复及后续清理放进同一有限历史。它从匹配的
实际成功恢复推出逆操作已全部消费，并在端点来源条件成立时，将值接到真实 native Unload。

投影仍限于本次调用触及的对象。publication、动态创建的 Child 效果、pending
registration 和一般合法生命周期删去仍需组合。调度公平性及最终重试保持为独立义务。

## 审查与验证

- [cleanup_groups/payload/recovery.rs](../crates/cordis-kernel/src/cleanup_groups/payload/recovery.rs)：真实观察、
  严格定义域、剩余逆操作栈保持及重试组合。
- [cleanup_groups/payload.rs](../crates/cordis-kernel/src/cleanup_groups/payload.rs) 与
  [cleanup_queue/completion.rs](../crates/cordis-kernel/src/cleanup_queue/completion.rs)：实际派发、
  擦除边界保留及后置条件传递。
- [reversible_value/managed/cleanup_path.rs](../crates/cordis-kernel/src/reversible_value/managed/cleanup_path.rs)：
  从真实结果有限组合回到 registered Begin 值。
- [execution.rs](../crates/cordis-kernel/src/execution.rs)：生产重试后置条件；
  [runtime.rs](../crates/cordis/src/runtime.rs)：宿主调用入口。

当前组合的证明、编译与回归证据记录在[交错恢复](r3-interleaved-recovery.zh-CN.md#审查与验证)。
此前仅覆盖清理的结果不会自动认证后续源码修改。

集成验收时需补充的新场景：

- 带别名、既有队列前缀和成功消费所留空槽的 scalar／typed 混合后缀；
- 真实失败、逆操作保留、重试准入及旧回复拒绝；
- 拒绝无关队列域、重复 attempt、槽位变化，以及无法衔接已记录轨迹的真实读取；
- 替换边界快照、丢弃失败逆操作、跳过非空槽位或接受定义域外值的合同突变。

完整开发记录器及新负向控制验收仍待运行。旧验证报告不会自动认证新源码；全量负向
回归和校准仍为 `not_run`。本文不提升原论文 68／69 条目的审查状态，也不标记 R3 完成。
