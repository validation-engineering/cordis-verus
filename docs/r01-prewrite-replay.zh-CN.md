# R01：从真实输入和共享存储推导重放

[English](r01-prewrite-replay.md) · [固定义务](paper-mapping-inventory.zh-CN.md#r01) · [操作合同](native-operation-contracts.zh-CN.md)

按需使用的 `closed::replay::Session` 从真实 managed 调用推导对象映射和历史输入，再调用原有的原生登记、Begin、受保护 root 解释器、Finish 和清理路径。标量与 typed 指令在跨调用及真实清理后继续共享同一批目标对象。调用方不提供预期目标堆、逆操作字或 head 编号映射。

**R01 仍开放。** 下述数据执行连接已经实现；完整函数和资源边界依赖仍须一起关闭。固定验收条件及原论文审计没有缩小。


近期交付优先级调整为独立范围的 [provider／consumer／Child 更新案例](cases/update-recovery.zh-CN.md)。一般 R01 组合后置；该交付不更改或关闭本页原有义务。

## 封闭值与普通兼容路径

有完整数据检查的路径使用 `closed::Value`：由基础值、序列、映射和显式对象引用组成的不可变有限图。引用包含真实名称与种类，不仅是向量下标。检查器遍历全部存储节点及指令常量，包含未走到的分支；也对显式 `objects::Table` 检查捕获输入。检查过程中不调用用户相等函数、回调或析构逻辑。

引用保持逻辑含义，`objects::Projection` 将它解析到不同的物理分配。表包含未访问及已退休对象；来自其他表但下标与种类相同的引用会被拒绝。共享引用继续共享。会话 schema 固定；接收未来值时检查同一 schema，不隐式添加对象。

普通 generic managed API 仍接受任意 `Arc<T>`。保留指针相同不能证明可变内部状态、隐藏句柄、析构或外部效果相同。封闭路径拒绝所有 `ScalarEffect` 回调指令，包括未走到的分支。加入新原语必须同时扩展受检查指令语言、实际提交／逆操作实现及相应定律。

## 实际执行与失败行为

| 连接 | 实际实现与保证 |
| --- | --- |
| 对象与首次输入 | [Bank](../crates/cordis-kernel/src/managed_replay_bank.rs) 核对实际出生／输入记录，构造物理分配单射。[Projection](../crates/cordis-kernel/src/closed_objects.rs) 覆盖完整声明表；未访问但带有不支持逆操作债务的对象会被拒绝。 |
| 混合 root／Child 函数体 | [Session](../crates/cordis-kernel/src/managed_replay_session.rs) 获取原有锁、检查保留源输入、预留修订号空间，再运行[原解释器](../crates/cordis-kernel/src/managed_function.rs)。成功报告建立标量值／深度和 typed 值／head／深度对应。 |
| 跨调用历史 | [Archive](../crates/cordis-kernel/src/managed_replay_archive.rs) 保留历史检查点并单调扩展 head 映射。真实清理可以恢复旧 head，同时递增防旧回复修订号；后续调用先检查该状态。后续函数没有访问的已退休 payload 不阻止该函数执行。 |
| 槽位与别名 | [操作数槽位](../crates/cordis-kernel/src/managed_replay_slots.rs)及[声明槽位](../crates/cordis-kernel/src/closed_slots.rs) 区分槽身份和对象身份。同一源槽的别名共享目标槽，选择同一对象的不同槽仍独立。替换使用真实 CAS，并保留历史版本映射。 |
| 发布 | [Finalization](../crates/cordis-kernel/src/managed_replay_finalization.rs) 将 root 后的自有服务绑定到实际成功 Finish。同一源 provider 的服务共用一个目标清理 owner；早期／后期 provide 保留原阶段，Finish 重试保留已安装前缀。 |
| 插件身份 | [Fiber 记录](../crates/cordis-kernel/src/managed_replay_fibers.rs) 用实际调用收据关联源／目标 ID。同一源插件后续启动复用目标登记，并取得新的 Episode 票据。封闭包装层根据先前映射调用检查实际源父节点，拒绝未知或不同父节点。 |
| 清理与重试 | 原生协议保留依赖、逆操作 owner 及失败尝试。root 后声明同步失败时，`Error::After` 保留真实报告和清理 owner；完成或重试 Finish 保持报告对应关系。 |

首次观察按真实调用顺序选择，不受输入 `Vec` 顺序影响。已声明但未访问的槽也被纳入。同一次声明捕获中，同一槽的观察互相矛盾时明确拒绝；身份分配耗尽、旧目标版本及不支持的源历史也明确失败。

正常返回会释放已持有的锁。部分执行后的错误保留 owner，不代表回滚。准入、容量、源选择和干扰保持为显式失败定义域。锁与票据提供安全合同，不证明公平性或最终终止。

## 面向论文的函数证据

[`paper_contract`](../crates/cordis-kernel/src/closed_contract.rs) 从实际源程序、目标报告、对象投影和保留逆操作字构造证据，不接收替代程序或预期结果。

- `functions` 在任意成对测试输入上关联 root／当前续体调用。绑定是输入上下文的一部分；未来 typed head 从准入时钟生成，并扩展已有历史映射。
- `inverses` 关联真实标量／typed 逆操作字的严格定义域及结果，包含对象缺失和当前状态不匹配。
- `allocations` 导出完整对象投影的单射。

这些属于**严格且区分准入的修订关系**，不是原文仅观察表的公式 (54)。既有的无限制读法反例保留。函数定理解释一次调用及其续体，不能表述成涵盖调用后任意宿主操作的完整父函数；尤其是数据逆操作字尚不包含父 owner 另行排队的原生 Child 逆操作。

## 仍须关闭的连接

以[固定依赖图](paper-mapping-inventory.zh-CN.md#r01)为准，剩余实质工作包括：

1. 将完整原生父／Child 控制与清理字接到 managed 数据函数解释，包含任意输入上的准入和失败定义域。真实 Child 运行演示不等于该定理。
2. 关闭整个纳入保证的 Component 资源边界，覆盖受保护调用前后的操作。generic 公开 owner 仍可接收普通宿主动作，这些动作不会因使用同一 owner 自动获得封闭数据证明。公开封闭入口的源 namespace 前提也需要接到经验证的生产者。
3. 完成 S01／S02 整篇解释审查，将明确命名的定义域／读写修订带入剩余恢复和重排陈述。
4. 在最终源码上执行集中验收及必要的指定负控。局部证明检查和运行用例是不同种类的证据。

这里不宣称公式 (55)、任意调度恢复、引理 79、终止、合流、任意 Rust／JS 插件正确或整篇完成。这条原生路径不需要 Node.js；普通 Cargo 构建会擦除证明。

## 复现

```sh
cargo test -p cordis-kernel --test closed_replay --locked --offline
cargo test -p cordis-kernel --test managed_replay --locked --offline
python3 -B scripts/check-profile-controls.py r01-exclusive
python3 -B scripts/record-development.py --offline
```

[封闭数据用例](../crates/cordis-kernel/tests/closed_replay.rs)覆盖混合调用、失败／重试／继续执行、源／目标 Child 所有权、重复 Episode、早期／后期发布、多服务 provider、槽别名与替换、退休引用、外部名称及外部干扰。原标量和 typed batch 辅助入口仍保留各自较窄的支持范围。最后的 development 记录需要在最终源码修改后刷新，旧总数不是当前工作树的证据。完整负控独立运行，未实际执行时保持 `not_run`。
