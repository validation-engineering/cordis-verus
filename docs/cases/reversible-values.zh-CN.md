# 具有真实 inverse 效果律的服务更新

[English](reversible-values.md) · [R2 合同](../r2-execution.zh-CN.md)

插件可以更新已声明的 `ReversibleValue`，无需自行编写清理回调。受验证内核执行
实际操作、计算真实结果，并在返回前把实际 inverse 存入该插件的清理组。
只有受验证的 inverse 真正恢复了值，清理才能报告成功。

```rust
use cordis::{Plugin, ReversibleValue, ServiceKey, ValueOperation};

let limit = ServiceKey::<ReversibleValue>::new("configuration limit");
let plugin = Plugin::new("temporary increase", move |setup| {
    let result = setup.update_reversible(limit, ValueOperation::Add(5))?;
    println!("{} -> {}", result.before, result.after);
    Ok(())
}).requires(limit);
```

provider 使用普通 `setup.provide` 发布 `ReversibleValue::new(10)`。
克隆的值共用同一把受验证锁。原语包括替换、检查溢出的加法、异或、比较交换。
`ValueProgram::new` 还支持有限程序，只能向后面的指令跳转，由真实比较结果选择
分支。`run_value_program` 持有值锁执行整个程序，再按执行顺序保存所有 inverse。
溢出会报告失败，但已经执行的前缀仍保留清理信息。空程序合法；错误跳转在执行前
被拒绝。

## 复现失败与恢复

```sh
cargo run -p cordis-verus --example reversible_values
```

案例运行三个真实插件：

1. provider 发布 `10`。两个 consumer 依次修改为 `15`、`22`。
2. 第一个 consumer 退休。它的 inverse 被后一次写入阻塞，值保持 `22`；其
   inverse 和依赖继续保留。
3. 退休 provider 会撤回第二个 consumer，它清理后恢复 `15`。由于第一个清理
   仍失败，provider 继续保留。
4. `runtime.retry_cleanup(first)` 恢复 `10`，随后 provider 才能释放。

依赖撤回会让 consumer 保持登记并进入 Inactive，不会隐式退休 consumer。
案例也检查了这一语义区别。

## 从论文到运行代码的审查路径

| 约束 | 实际代码与证明 |
| --- | --- |
| 操作返回值、结果以及真正的部分逆操作 | [`Cell::forward`、`operation`、`primitive_theory`](../../crates/cordis-kernel/src/reversible_value.rs) 实现并证明 Definition 30 和 Lemma 39 的 dependent grammar 所需的标量原语前提 |
| 结果选择实际 continuation | `Branch::select` 和 [`ReversibleValue::run`](../../crates/cordis-kernel/src/value_program.rs)，宿主不提供预期结果 |
| 每个程序根和 continuation 都属于 Component | `Program::member`、`Program::component` 实例化 [R1](../r1-semantics.zh-CN.md) 的完整有限严格载体，不把载体缩成成功输入集合 |
| 观察来自真实执行状态 | 真正的 `vstd::RwLock` 持有 `ValueState { value, depth }` 和 ghost 执行历史；`snapshot` 在锁内读取实际字段 |
| 保存的 inverse 就是本次实际操作产生的那个 | [`Execution::apply_value`、`run_value_program`](../../crates/cordis-kernel/src/execution.rs) 保存真实 inverse 对象；程序部分实现在 `value_program.rs` |
| 清理不能替换 inverse 或仅上报成功 | [`CleanupQueue::dispatch`](../../crates/cordis-kernel/src/cleanup_completion.rs) 在同一个受验证调用中选取、执行和确认实际槽位中的 inverse |
| 恢复失败保留恢复信息 | 被阻塞的 inverse 留在原清理槽位，队列进入失败状态；既有受验证重试协议创建下一次尝试 |
| 整段历史对应 source 步骤 | `history_interpretation` 分类每一次记录的写入、成功恢复和拒绝；`ProgramReport::source_execution` 为实际完整程序或失败前缀构造连续的 dependent-grammar 轨迹 |

inverse 函数的解释覆盖**任意输入**：仅当当前 `(value, depth)` 与捕获的后态
完全相同时，才返回捕获的前态。观察包含 depth，因此再次写入相同值也会阻塞
较早的 inverse。inverse 是不可复制的线性对象，字段私有，持有原共享目标，
不能被重定向到另一个值。depth 表示嵌套层级，不是全局唯一版本号。

轨迹由实现本身构造，调用方不提供 source execution 或预期 transcript。
Cargo 构建会擦除 ghost 历史，不会保留不断增长的运行时审计日志。
程序只保存真实代码、结果和 inverse。值锁内不会执行用户回调。

## 范围与剩余工作

这是原生 Runtime 和静态 Rust 宿主实际使用的原语与程序路径。它证明真实保存的
`u64` 值的效果律，补充了此前只追踪不透明回调结果、句柄的合同。其 source 解释
是 R1 所使用的 dependent value grammar，**并没有**把整个 Runtime 注册表解释
成 R1 的递归 context。

普通 Rust 闭包、JavaScript 对象、I/O、可用性谓词和外部调度器仍保持原有证明
边界。该 API 不会验证包含此次调用的整个回调，没有把新操作暴露给 Node，也不
保证发生干扰后最终一定恢复。完整宿主联合不变式、函数字段、动态 Child／
publication 组合及整个原生／Node 执行轨迹分类，仍是 R2 剩余工作。原来的三条
R2 退出条件和原论文审查状态保持不变。

回归覆盖原语、并发访问、同值干扰、程序分支及失败前缀。真实 Runtime 测试覆盖
依赖保留、显式重试、逃逸上下文拒绝和静态宿主。五个可以编译的负向对照分别
改错结果分支、忽略层级、丢弃真实 inverse、把恢复失败报告成成功、跳过实际 continuation，必须在指定
合同处被证明拒绝。定向证据与完整负向回归、发布验收分别记录。
