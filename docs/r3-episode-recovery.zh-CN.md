# R3：真实 Episode 全过程的恢复合同

[English](r3-episode-recovery.md) · [里程碑](paper-refinement-roadmap.zh-CN.md) · [源码映射](paper-refinement-map.md)

R3 第一批将式 (55)、(56) 接到**同一次真实 Mixed／Fresh 脚本执行中的所有 Episode 检查点**。
不再要求脚本最后一条成功命令恰好是所选 owner 的 Unload。真实 `run_inspected` 入口也携带
这项合同。R3 仍在进行；本批覆盖具体的同步 Unit／Child／Provision／Xor 语言，尚未覆盖
managed-production/v1 的完整效果载体。

## 提供什么保证

从任意一次成功 Begin，到该 owner 下一次 Unload 之前的任意检查点：

```text
将 owner 保留的逆操作序列应用于当前表观察
    =
将实际 foreign 值映射应用于 Begin 紧后的表观察
```

这是定理 68、式 (55) 的具体表值实例。foreign 映射包括其他 actor 在 Unload 时实际捕获的
逆操作日志，即使这些收据早于当前 Episode。Fresh 使用每次真实 Child 落地记录的分配选择。

如果检查点之后实际执行了 owner Unload，其后状态具有相同的值观察，而且 owner 表为空：
对应推论 69、式 (56)。后续成功命令不影响这一历史结论。再次 Begin 会产生新的起点快照，
形成独立恢复区间。

对于**返回机器中仍未结束的 Episode**，合同还把上述值等式接到真实存储的 journal、真实表
以及 `restore_receipts`：结果为 `Some`，其投影等于 foreign 重放。有定义性来自已有的
执行历史定理，调用者不需要假设恢复成功。这里约束的是实际 Unload 使用的同一套收据解释，
没有新增另一套恢复实现；它不允许绕过生命周期清理守卫。

发生受检查错误时，保证作用于已经成功执行的前缀。被拒绝的请求及其后的命令不会进入源轨迹。

## 论文到代码的审查路径

| 论文约束 | 合同与实现 |
| --- | --- |
| 定义 51：观察全部已登记表，包括 Loading 值 | `projection::project`；`equal_payload` 通过唯一所有者转移观察，不要求无关执行元数据相同 |
| 引理 59：Begin／Unload 之间保持 installed | `terminal_episode::{mixed_open_interval,fresh_open_interval}` 从实际转换序列推出区间 |
| 定理 68／式 (55)：任意 Episode 检查点的恢复 | `episode_replay::recover_cut`、`fresh_episode_replay::recover_cut`；实际 Xor 库证明自身标量交换律 |
| 推论 69／式 (56)：结束 Episode 的 Unload | `recovered_at` 将每个结束点连接到真实下一源状态与 owner 空表 |
| 使用真实收据，无须调用方提供恢复模型 | `MixedDriver::{source_journal,source_restoration,restored_observation_from_source}`；Fresh 通过实际内部 driver 复用 |
| 所有查询共享同一个真实源执行 | `ScriptReport::recovery_history_witness`；实际 Mixed／Fresh `run_script` 的建立路径调用 `establish_recovery_history` |
| 公开检查入口的值、函数和恢复对应 | `run_inspected` 在 R1 解释证据之外传递 `recovery_history` |

实现位于 [episode_replay.rs](../crates/cordis-kernel/src/episode_replay.rs)、
[fresh_episode_replay.rs](../crates/cordis-kernel/src/fresh_episode_replay.rs) 和
[inspected_run.rs](../crates/cordis-kernel/src/inspected_run.rs)。`recovery_source` 提取共同源证据；
`current_recovery` 提取该证据及当前真实 journal 的恢复等式。这些历史和查询都是编译时擦除的
证明数据，不新增运行时历史缓冲或用户依赖。

## 为什么还不能等同于合法删除执行

锁定的论文 v1 第 46 页已区分两种解释：式 (55) 比较表值，控制字段不在关系中。将它解释成
“owner 从未执行时仍可发生的执行”，还需要其他条件，包括 owner 创建的 fiber 没有执行步骤。

例如，owner 发布一个服务并创建 Child；consumer 使用该服务，Child 又发布自己的值。
恢复会移除 owner 的服务，但 Child 的值一直保留到它自己清理。若删除 owner，Child 不会存在，
consumer 的 Begin 也可能不再合法。表观察相等并没有构造出合法剩余轨迹。在值代数中，缺失 key
上的标量操作按恒等处理；真实严格解释器仍会拒绝缺失值。

另有[有条件的删除证书](r3-script-deletion.zh-CN.md)，现已将实际 Mixed 报告接到私有表
owner 的合法剩余执行，允许外部 Child 生命周期。它使用同一来源见证，将目标表投影接到
这里的恢复等式；owner 创建的 Child 和私有 consumer 不在该证书范围内。值定理本身
不抹除 Child、不回退 allocator、不恢复任意外部 I/O，也不证明全局终止或提升原论文的
partial／refuted 状态。单独 mutator 和 bootstrap 尚未
获得新的全 Episode 报告合同。定理 68、推论 69 对原文不受限目标仍为 `partial`。

## 复现

[运行案例](../crates/cordis-kernel/tests/episode_replay.rs) 使用真实 `run_script`／`run_inspected`：

- consumer 阻止 owner 清理，真实 Child 收据、已发布值和 provider 逆操作继续保留；
- 两次 Episode 使用不同的 provider 起点快照，分配不同 Child；
- 两次 owner Unload 都位于同一成功历史中间，之后还有成功转换和被拒绝的命令；
- consumer 的正向与逆操作抵消，Child 的值保留到它自己清理。

使用固定工具链与缓存依赖：

```sh
source scripts/toolchain-env.sh
cargo test -p cordis-kernel --test episode_replay --locked --offline
python3 scripts/check-profile-controls.py episode
python3 scripts/record-development.py --offline
```

两条选定的**语义突变**分别丢弃 foreign 历史，以及在恢复观察中用空 journal 替代真实收据。
突变必须整 crate 编译成功，并由指定恢复合同拒绝。既有严格检查器不把超时、资源耗尽、编译
失败或无关诊断算作证据。原始日志、源码副本和哈希保留在 `target/r3-episode-controls/`；报告
明确将完整负控和 calibration 标为 `not_run`。这与包含完整证明、运行和打包检查的
[开发记录](development-report.json)分开；两者都不代表发布或整篇论文验收。旧 R2 验收产物仍只
对应其原始源码，不能仅修改哈希使之变成新的通过记录。

## R3 还剩什么

1. 把恢复区间接到 R2 的实际受管标量／typed replacement、共享别名、待完成逆操作尝试与
   联合生产历史。从这些历史推出所需的合法干扰条件；具体 Xor 等式不会自动推广到这些效果。
2. 将构造式删除扩展到明确允许的 Child／consumer 情况。构造合法剩余执行，保留真实分配和
   准入，并明确何时无法删除。表值相等不能替代这项退出条件。
3. 在所审查的组件载体及多轮生产 Episode 上组合适用结果，按原有 R3 退出条件进行统一语义
   审查与验收。

后续[生产恢复批次](r3-production-recovery.zh-CN.md)已补齐真实混合历史衔接、严格逆序列和
typed 实际尝试的定义域；生产 Episode 层面的完整组合仍待继续。
