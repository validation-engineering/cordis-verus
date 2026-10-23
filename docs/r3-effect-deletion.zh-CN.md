# R3：转换完整 native Journal 观察载体

[English](r3-effect-deletion.md) · [Native 区间删除](r3-native-deletion.zh-CN.md) · [里程碑](paper-refinement-roadmap.zh-CN.md)

第 5 包将中间 native Episode 区间接到**合法的剩余 Journal 轨迹**，涵盖其他保留记录、真实守卫读取、槽位引用及 pending 逆操作登记。来源仍是前几包恢复捕获使用的真实生产快照。
**R3 整体仍在进行中。** 本包构造的是 R2 Journal 关系中的剩余执行；通过真实分配器重新运行，以及任意 Rust／Node 回调重放，尚未完成。

## 保证与来源条件

调用者提供 native 区间和针对真实 Journal 前缀的证明层效果掩码。native 动作由区间规则选择，其他效果由掩码选择。调用者不提供期望初态、合法目标轨迹或逆操作成功前提。查询要么构造剩余轨迹，要么返回来源阻断：

| 检查 | 含义 |
| --- | --- |
| Window | 原 native 边界、consumer、Child 或闭合条件不满足 |
| MaskLength | 掩码没有对应这个完整来源前缀 |
| Local | 保留操作失去准确的本地前态 |
| Read | 保留守卫失去原配置、队列、owner 或注册观察 |
| Reference | 保留的本地槽位失去原对象 |
| Cause | 逆操作登记／settlement 或 scalar 逆操作失去创建来源、保留关系或唯一消费条件 |

成功时，每个保留步骤满足真实 `joint::step` 与 R2 记录分类。Work、Cleanup、Groups、Host、Control、配置、scalar 操作、槽位替换和 payload 版本转换都保留自己的合同。普通步骤保留原操作及准确输入；跨记录守卫的实际读观察保持一致。涉及 native 的读只比较对应 actor 的注册与 owner，不将无关的 native revision 当成依赖。

本地槽位仍指向保留的 Object；外部 Journal 引用只保留身份。登记与 scalar Restore 的来源下标随轨迹压缩，仍指向保留的真实正向操作；scalar 来源在目标中只能被消费一次。保留 pending 写入及其 settlement 不能被拆开，尚未登记的义务准确保留并重新编号。

最终 native control、publication、Episode owner 与原终点相同，native revision 则记录剩余 native 提交数。它不自动意味着其他记录或整个堆相同。第 4 包对其他 Episode、Child 实际 Remove 和 consumer 闭合的要求继续适用。任意掩码可能被拒绝；本包还不自动推导每个选中 Episode 的全部效果。

内部 `Plan::construct` 是带步骤转换义务的组合定理；公开快照查询从真实来源、native 区间定理和上述读取条件中推导该义务，不要求调用者预先证明目标能够执行。

## 与真实代码、同一恢复切点的连接

```rust,ignore
let capture = runtime.publication_snapshot()
    .with_effect_deletion(Ghost(window), Ghost(effect_mask));
```

`RecoveryCapture::with_deletion(...).with_effects(...)` 保留原 value／Child／native 恢复结果，并在**同一个快照**上增加完整 Journal 构造。它不再次读取 Journal、不执行回调或清理。掩码、历史与构造结果均被擦除，不增加无界运行日志。构造轨迹是证明数据，不会伪造真实 Receipt 或第二个物理 Journal。

## 非空案例与验证

证明客户端从 **17 个来源提交**中推导合法性：两组交错写入及登记、一组失败清理和更新票据后的重试、成功恢复、本地槽位，以及之后仍未登记的写入。删除一组对象／队列的效果后留下 **7 个合法提交**。保留登记从来源写入下标 5 改为目标下标 2；最终 pending 来源从 15 改为 5。原部分逆操作的定义域保持有效；仍在队列中的逆操作不会被解释成队列已经排空。

两项严格定向负向控制拒绝跳过守卫读检查以及保留旧登记下标：
`python3 scripts/check-r3-effect-deletion-controls.py`。
[开发记录](development-report.json)将源码与全内核证明、已有真实失败／重试测试及独立打包检查绑定；全量负向回归单独记录，未运行时仍为 `not_run`。

## 审查路径与剩余边界

- [native_joint_deletion.rs](../crates/cordis-kernel/src/native_joint_deletion.rs)：真实快照、来源阻断、native 转换及终点。
- [joint_erasure.rs](../crates/cordis-kernel/src/joint_erasure.rs)：压缩位置、pending 守恒、逆操作来源与唯一消费。
- [joint_erasure_reads.rs](../crates/cordis-kernel/src/joint_erasure_reads.rs)：实际守卫所需的准确读取。
- [joint_erasure_client.rs](../crates/cordis-kernel/src/joint_erasure_client.rs)：非空来源与剩余执行。
- [managed_deletion_capture.rs](../crates/cordis-kernel/src/managed_deletion_capture.rs)：同切点 value／Child 组合。

Journal 分配 key 是擦除的证明身份；真实注册表 ID、Kernel generation、action ticket、work domain 和不透明 payload 身份需要各自的转换合同。[Native 控制重放](r3-control-replay.zh-CN.md)现已通过原 Kernel 实际调用完成注册表 ID 压缩与 generation 重新生成，但尚未执行这里的完整 Journal 关系。两者的组合仍需完整生产者解释、typed inverse payload 来源和引用／票据转换。准确前态／读检查会保守拒绝部分可恢复的共享写入和带版本变化的 payload／槽位路径。完整堆恢复、Mixed／Fresh 按 Episode 重放、异步 landing 转换及 Node 独立协议恢复仍待推进。同一切点组合多个证书并未消除这些义务。

本包推进 Lemma 79 在所支持载体上的构造性剩余执行部分，不更改原 Theorem 68／Corollary 69／Lemma 79 审计结论，不宣称一般 Equation (55)、整篇论文、发布、调度公平或全局终止已完成。
