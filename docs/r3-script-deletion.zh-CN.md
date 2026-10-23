# R3：从真实脚本构造合法删除执行

[English](r3-script-deletion.md) · [Episode 值恢复](r3-episode-recovery.zh-CN.md) · [生产恢复](r3-production-recovery.zh-CN.md)

实际 Mixed `run_script` 报告现在除 Episode 值恢复等式之外，还携带有条件的**合法剩余执行**。
目标由报告的来源历史构造，不要求调用方提供一个成功的目标执行、期望堆状态或成功逆操作。

另有[闭合区域构造](r3-closed-region-deletion.zh-CN.md)可对 Mixed／Fresh 中 owner 创建的 Child 与实际 consumer 关联删除。本页私有 Episode 证书保留其原有条件与共享效果结果。

## 允许的来源区间

选定区间从真实 owner Begin 开始，到同一 Episode 的真实 Unload 结束。它可以位于更长
脚本内部，也允许脚本在该区间之后返回检查错误。额外条件检查同一份真实来源：

- owner 在区间内执行表操作，不创建 Child。
- Begin 时其他注册接口避开 owner 的私有 provision。
- 外部 Insert／Child 创建保留来源中的真实身份，其新依赖满足同一排除条件；区间内
  不插入或删除 owner 本身。

在这些守卫下允许外部表操作、外部 Child 生命周期、动态注册变化和早于区间的外部逆历史。
允许共享依赖键：实际 Xor 库对所有输入证明严格正向／逆操作交换及原始结果稳定性。
依赖被删除 owner 私有 publication 的 consumer 不满足声明条件。

## 结论与实际执行的连接

构造器省略 owner 的激活及清理步骤，保留外部 retirement。owner 仍已注册并处于
Inactive。外部调用在目标状态上重新解释，其逆操作票据映射到构造出的目标历史。证明得到：

1. 每个保留的转换都合法，起点是实际 Begin 之前的状态。
2. 最终控制状态和表观察与真实 Unload 后一致；历史票据编号无需相同。
3. 目标的表投影等于此前对同一来源 Episode 证明的外部值重放。

`ScriptReport::recovery_history_witness` 对每个满足条件的闭合区间包含删除证书。
实际脚本成功返回及检查错误返回都会调用建立证书的路径；`delete_private_episode`
使用同一见证取得构造出的目标。

| 审查环节 | 源码 |
| --- | --- |
| 实际脚本见证及建立路径 | [mixed_driver/episode_replay.rs](../crates/cordis-kernel/src/mixed_driver/episode_replay.rs) |
| 来源守卫、目标构造及报告查询 | [mixed_driver/deletion.rs](../crates/cordis-kernel/src/mixed_driver/deletion.rs) |
| 实际 Xor 库的严格接口 | [xor_recovery_algebra.rs](../crates/cordis-kernel/src/xor_recovery_algebra.rs)：`strict_interface` |
| 合法转换及逆操作映射 | [foreign_child_deletion.rs](../crates/cordis-kernel/src/foreign_child_deletion.rs)：`closed_deletion` |

## 定向验证

最终组合检查覆盖 native Begin、managed／payload 恢复、Mixed／Fresh 脚本入口和
Xor 接口：**401 verified，0 errors**。内核全部目标、全部功能的 Clippy 及论文映射
一致性检查也通过。这是定向开发证据，不是整篇论文或发布验收。

```sh
source scripts/toolchain-env.sh
./scripts/verify.sh --verify-module mixed_driver --verify-module xor_recovery_algebra \
  --verify-module reversible_value::managed --verify-module reversible_value::payload \
  --verify-module lifecycle_state::native::runtime::episode \
  --num-threads 2 --triggers-mode silent --output-json --time
```

## 边界及待验收内容

当前证书用于 Mixed 脚本，独立于 Fresh 值恢复及生产 native／Node 生命周期删除。
独立的闭合区域结果已处理选中的 Child／consumer 家族；将其与本页单 Episode 的
共享效果范围组合，仍需处理出生、名称、父子关系及 consumer 准入，表值相同并不足够。原论文反例和
R3 退出条件保持不变。

集中验收仍需覆盖：共享依赖的非空 Episode、外部 Child 创建与 Unload、多次内部
Episode、检查错误前缀，以及私有 consumer 和 owner-created Child 的拒绝。负控应
拒绝丢弃外部 Child 出生、错误保留标签或虚构目标逆操作来源。完整开发与负控验收仍
独立于定向证明检查。
