# R3：普通 Rust 宿主的恢复所有权

[English](r3-host-recovery.md) · [最终恢复](r3-final-recovery.zh-CN.md) · [中间观察](r3-observation-recovery.zh-CN.md)

本页对应 R3 剩余工作的第 3 包：将普通 Rust 宿主的实际修改入口接到
`RecordedExecution`。**R3 整体仍在进行中**；合法剩余生产执行及 Node 独立协议恢复
仍待完成。

## 实际改变

`Runtime` 和 static host 从接入到清理、释放都持有同一份记录型所有者。
`Plugin::native_function` 在真实注册 root 返回时接入，保留该调用的队列前缀；作为
Child 挂载时也使用此入口。其他 root 在 Begin 后接入，保留既有回调、value 和
service program 行为。通过 `owner_context` 进行的后续写入、可恢复执行游标、
effect 组及后续 Child 登记都扩展同一所有者。

所有者通过经过验证的 `Deref` 提供只读 `Execution`，不提供 `DerefMut` 或公开的
可变内核借用。宿主若误用底层修改方法，会在 Rust 类型检查时失败，必须改用维护
历史的入口。

| 实际操作 | 维护的合同 |
| --- | --- |
| scalar 写入、typed 替换、value／service program | 保留旧队列前缀、token 身份和已派发宿主动作；新逆操作追加到原有义务。 |
| root work、effect 句柄、准入与发布 | 保留无关组的历史和原始调用基线。 |
| managed 清理派发 | 实际读取、逆操作尝试及确认进入历史，包括失败。 |
| 宿主回调／Future 确认 | 只能确认已派发的宿主动作，不能消费 managed 逆操作；拒绝时返回原始结果。 |
| 受控重试 | 检查 control／Episode 身份，保留失败资源和义务，发出新票据后清除失败标志。 |
| 受控 Unload、effect 退休、static seal | 删除执行存储前，将真实排空队列保留为终态证据。 |

`terminal_history` 证明：终态队列中的每个 managed 逆操作都有对应的真实成功派发；
绑定 Journal 的队列还保留匹配的确认收据。`release_controlled` 对 `Runtime` 实际
调用的释放入口导出这项保证，覆盖最初前缀及后续登记。这不是仅从空 Vec 推断恢复。

新增的前缀合同在现有可执行修改函数及其循环中证明，不是另加给普通回调的假设。
`NativeDriver` 还提供 recorded root、携带证据的受控释放及第 2 包的 native 恢复
快照入口，供验证客户端使用。

## 论文对应与边界

本包将实际适配器接到式 (55)／(56) 的生产 refinement 所使用的逆操作历史。
它不改变这些公式、恢复查询的来源／闭合条件及原论文审计结果。外部共享值句柄仍能
产生干扰；完整生产者捕获提供外部来源覆盖，不能只凭宿主观察到的回调列表判断。
逆操作成功登记，不等于外部干扰已结束，也不等于所有观察已恢复到初值。

历史、payload 观察及终态队列使用 `Ghost`／`Tracked`，在执行构建中擦除；迁移不
保存额外运行日志或历史 payload Arc。仍可用真实 root 报告调用内核的显式共同截面
捕获 API；`Runtime` 不长期保存所有完整报告，也不提供运行时“恢复已证明”标志。

普通 Rust 适配器及任意回调本体仍在 Verus 验证边界之外。验证所有者约束被调用的
操作，不证明外部 I/O 真实性、调度公平、Future 最终完成或任意 payload 内部修改。
static host 共享所有权协议，但不因此获得 native publication 语义。Node 独立的
多版本发布协议、一般合法删除、全局终止与合流仍属于后续工作。

## 审查与复现

| 来源 | 审查内容 |
| --- | --- |
| [reversible_value/managed/interleaving/history/lifecycle/host.rs](../crates/cordis-kernel/src/reversible_value/managed/interleaving/history/lifecycle/host.rs) | 只读内核访问、宿主追加合同及终态消费定理。 |
| [reversible_value/managed/interleaving/history/lifecycle/callbacks.rs](../crates/cordis-kernel/src/reversible_value/managed/interleaving/history/lifecycle/callbacks.rs) | 受守卫的回调／Future 确认与拒绝结果保留。 |
| [reversible_value/managed/interleaving/history/lifecycle/native.rs](../crates/cordis-kernel/src/reversible_value/managed/interleaving/history/lifecycle/native.rs) | recorded root 返回、受控重试与终态释放。 |
| [poll_control.rs](../crates/cordis-kernel/src/poll_control.rs) | 实际 control 身份检查及带来源的 Unload。 |
| [native.rs](../crates/cordis-driver/src/shared/native.rs) | 普通 driver 对同一所有者的调用。 |
| [runtime.rs](../crates/cordis/src/runtime.rs) | root／Child 接入、实际清理派发和调度调用。 |
| [reversible_value/managed.rs](../crates/cordis/tests/managed_function.rs) | 后续 scalar／typed 写入、Child、回调失败、前缀保留、重试成功及旧 context 拒绝。 |

既有 scalar／service program、异步回调、effect／句柄、static host 和插件测试覆盖
迁移后的路径。新增运行案例检查可见值和清理行为，不能读取擦除的证明数据。

```sh
python3 scripts/record-development.py --offline
python3 scripts/check-profile-controls.py host
```

[开发记录](development-report.json)将完整开发验收绑定到准确源码。`--check` 只查
哈希，不重跑证明。两项定向控制故意遗漏追加历史或终态队列，必须整体编译成功、通过
新的匹配正向基线，并在指定断言处被拒绝。本地报告位于
`target/r3-host-controls/report.json`。全量负向回归和 scoped calibration 若未
另行运行，均为 **not_run**。开发验收不代表发版验收或整篇论文完成。

[第 4 包](r3-native-deletion.zh-CN.md)新增真实来源上的 native 中间区间删除；完整效果轨迹重放仍待完成。
