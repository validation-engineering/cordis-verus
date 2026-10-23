# R3：通过原执行器重放 native 控制轨迹

[English](r3-control-replay.md) · [Native 区间删除](r3-native-deletion.zh-CN.md) · [完整 Journal 删除](r3-effect-deletion.zh-CN.md) · [里程碑](paper-refinement-roadmap.zh-CN.md)

满足来源条件的 native Episode 区间，现在可以生成一段**通过生产 `Kernel` 方法实际执行的剩余控制轨迹**，并记录每一步实际产生的控制状态。

这关闭了重放缺口中的注册表分配和 Kernel generation 部分。**完整生产 Journal 重放与 R3 整体仍未完成。** 服务值、action ledger 票据、work domain 和 Node 协议事件不属于本次控制结论。

## 从来源到实际执行

`Snapshot::replay_control_window` 将真实生产快照连接到：

1. 已有 native 区间删除定理：从来源闭合条件推出合法剩余控制历史。
2. 可执行的有限名称置换：保留的 Insert 按原顺序获得连续 ID；父身份和 committed provider 使用同一置换。
3. 原有 `Kernel::insert`、`begin`、`check_iteration`、`finish`、`leave`、`retire`、`begin_cleanup`、`finish_cleanup` 和 `remove`。没有直接安装目标状态或计数器的替代实现。
4. 每一步实际结果等于重命名后的剩余源状态；generation 等于该身份自保留 Insert 起实际保留的 `Begin` 次数，有限来源长度给出计数器上界。

推荐入口现为[生产源命令自动关联](r3-source-chain.zh-CN.md)。`NativeRuntime::new_recorded` 从实际成功转换及已保存的注册声明生成命令，包含继承依赖和私有 reservation anchor。`control_source_snapshot` 自动导出命令／快照关联及分配上界；底层 `Snapshot::replay_control_window` 仍保留明确的来源前提。

```rust,ignore
let captured = runtime.control_source_snapshot()?;
let replay = captured.source.replay(&captured.cut, &keep, Ghost(window))?;
let retained_kernel = replay.execution.kernel();
```

普通运行时默认关闭记录。有界记录器明确报告耗尽，不会认证截断来源。完整 Journal 历史与 typed payload 证据仍被擦除；命令是有限的可执行审查输入。窗口及效果选择条件仍需满足。

准备阶段会拒绝掩码长度错误、出生 ID 越界和身份重复分配，丢弃的输入也不能重复出生。重放保留正常的可执行错误返回。结果拥有独立 Kernel，不修改原运行实例。这个按需审查入口保存有限命令计划；中间状态和来源证书只在证明层存在。

## 真实运行案例

`tests/native_control_replay.rs` 用真实 native runtime 执行同一 owner 的前、中、后三次 Episode。中间 Episode 创建的 Child 实际完成 Unload、Retire 和 Remove；后续新分配的 provider 及其 consumer 被保留。

| 观察 | 原执行 | 实际剩余执行 |
| --- | --- | --- |
| 控制步骤 | 24 | 13 |
| 注册表分配槽位 | 4 | 3 |
| 后续 provider ID | 2 | 1 |
| consumer ID／parent | 3／2 | 2／1 |
| consumer 的 committed provider | 2 | 1 |
| 原 owner 的 generation | 3 | 2 |

注册参数来自实际 `RegisteredPlugin`，无需手工维护另一份声明。案例还检查原 runtime 未被修改。运行案例检验适配路径；一般保证由 Verus 合同在上述来源条件下给出。

## 审查与验证

| 义务 | 代码／证明入口 |
| --- | --- |
| 来源区间推出可运行计划 | [lifecycle_state/native/runtime/history/deletion/replay.rs](../crates/cordis-kernel/src/lifecycle_state/native/runtime/history/deletion/replay.rs)：`executable_step`、`executable_path`、`replay_control_window` |
| 真实注册参数 | [kernel_replay.rs](../crates/cordis-kernel/src/kernel_replay.rs)：`Command::from_registration` |
| 连续分配与身份转换 | [kernel_replay/names.rs](../crates/cordis-kernel/src/kernel_replay/names.rs)：`compact`、`prepare`；[mixed_driver/fresh/names.rs](../crates/cordis-kernel/src/mixed_driver/fresh/names.rs)：`prefix_pairing` |
| 真实调用准入与准确后继 | [kernel_replay.rs](../crates/cordis-kernel/src/kernel_replay.rs)：`replay_admission`、`unique`、`replay_one`、`execute` |
| 实际 generation 计数 | [kernel_replay.rs](../crates/cordis-kernel/src/kernel_replay.rs)：`generations`、`represented_generations` |

`python3 scripts/check-profile-controls.py control-replay` 检查两种错误实现：沿用出生的旧编号、跳过实际 `Kernel::begin`。每项要求匹配源码的正向证明、突变版本编译成功，以及指定合同明确拒绝。全量负向回归单独运行。

## 剩余边界

这里的 `Kernel::finish_cleanup` 实现已获准的**控制层** Unload，不会确认真实插件析构、消费 managed inverse，也不调用 `NativeRuntime::release_managed_execution`。生产清理仍受原有清理守卫和所有权证书约束。

Journal 的 allocation key 是擦除的证明身份；真实注册表 ID、Kernel generation 是不同的量。本次转换后两者。完整 Journal 仍需引用／来源转换、typed inverse 与 work 身份、publication 载荷对应、异步 landing 和 Node 协议恢复。控制状态在重命名后相等，不意味着旧 action ticket 或不透明 payload 身份可以复用。不据此宣称一般完整效果式 (55)、R3、全局终止或发布验收已完成。
