# 受控效果：让内核直接执行论文中的操作

[English](r3-controlled-effects.md) · [反例](r3-effect-boundary.zh-CN.md) · [R3 剩余工作](r3-remaining-work.zh-CN.md)

**已选择的架构是：论文恢复保证涉及的状态，统一通过受控内核操作访问。** 插件描述操作；源执行与目标重放使用同一份经过验证的 Rust 实现，完成真实读取、计算、写入、逆操作创建和历史记录。任意回调的返回值合同不能建立这个边界。

## 已实现的执行路径

```text
ManagedInstruction::scalar / Effect::Kernel
  -> 原 registered root 或 Child 函数解释器
  -> 声明服务与执行 owner 捕获
  -> 持有值写锁期间计算封闭的 Instruction
  -> 共用 commit_calculation：真实写入 + Journal 票据 + 逆操作
  -> 原 execution owner 将逆操作登记到自己的清理队列
```

`Instruction` 是仅含数据的封闭枚举，支持内置值操作和检查溢出的乘加。它不能存放闭包、trait object 或共享服务句柄。执行器只根据锁内的真实值和指令参数计算，函数分支仍由真实结果选择。typed replacement 继续使用同一个异构函数及原有 payload／逆操作路径。普通 Rust 宿主的 `ManagedInstruction::scalar` 默认走这条受控路径。

受控路径与扩展路径共用真实标量提交及逆操作注册。`Effect::Scalar` 仍在值锁外调用可扩展的 `ScalarEffect`，随后检查捕获的输入；它保留返回值和干扰拒绝合同，没有因此获得纯度保证。受控路径持有值锁时不执行任意回调。

## 证明与实际代码的对应

| 论文到代码义务 | 实际实现与合同 |
| --- | --- |
| 原语使用真实输入 | [`Instruction::evaluate` 与 `commit_calculation`](../crates/cordis-kernel/src/reversible_value/effect.rs) 在同一次值写锁持有期间，从真实状态计算。受控操作成功等价于原语在该实际状态有定义，并排除回调计算干扰。 |
| 声明选择、别名 frame、真实逆操作所有权 | [`apply_native_controlled`](../crates/cordis-kernel/src/reversible_value/native_effect.rs) 重新检查执行 owner 和准入，连接真实先前票据，导出现有服务／别名解释。[`apply_controlled_effect`](../crates/cordis-kernel/src/reversible_value/controlled.rs) 把实际逆操作登记进原清理队列。 |
| 依赖函数成员资格及真实执行 | [`reversible_value/managed.rs`](../crates/cordis-kernel/src/reversible_value/managed.rs) 和 [`reversible_value/managed/semantics.rs`](../crates/cordis-kernel/src/reversible_value/managed/semantics.rs) 将受控指令接入同一个函数语义与成功前缀报告。`controlled_execution` 从实际报告推导无标量干扰，使用既有 R1 函数解释和原可执行解释器。 |
| 目标执行保留完整源函数 | [`Source::instantiate_controlled`](../crates/cordis-kernel/src/reversible_value/managed/replay.rs) 在目标注册之前检查所有指令，包括未执行分支。[`batch::run_controlled`](../crates/cordis-kernel/src/reversible_value/managed/replay/batch.rs) 在创建 provider 前检查每个源函数，之后使用原共享对象批量执行和真实源顺序。 |

论文条目导航：操作及 mediated grammar 对应 Definition 29/30，组件对应 Definition 48，confinement 对应 Definition 55，见[论文台账](paper-coverage.md)。上述合同在已审查的 R1 解释下加强这些条目的运行前提。一般恢复对应 Theorem 68 / Corollary 69，恢复表达式是 Equation (55)；受控原语／函数路径没有因此完成这些一般恢复结果。

这些检查可执行且有证明：含 `Effect::Scalar` 的源函数会被拒绝，目标 runtime 保持不变。接受意味着保留函数确实受控，不意味着后续所有生命周期动作必定成功。例如算术无定义仍会失败，并保留真实成功前缀供清理。

## 复现与审查

```sh
cargo test -p cordis-kernel --test managed_replay --test replay_effect_boundary --locked --offline
bash scripts/check-r3-effect-boundary.sh
python3 -B scripts/check-profile-controls.py controlled-effects
```

案例覆盖标量／payload 混合调用、乱序传入的源函数、真实目标清理恢复初态、成功前缀后的溢出，以及未执行的回调分支。同一个经过验证的回调反例会被受控入口拒绝；扩展入口仍可复现干扰。严格负例修改准入检查和真实计算输入，要求匹配的正向证明、可编译的错误实现及指定合同失败，不能把超时算作通过。

集成结果应检查与源码绑定的[开发记录](development-report.json)。这些案例和选定负例不代表完整负例回归、发布验收或 R3 完成。

## 尚未跨越的边界

这是所选架构的首个实际实现，还不是覆盖所有插件资源的排他访问能力系统。其他 owner 仍能通过现有 API 访问共享值；完整调度器需要从生产历史构造目标状态，并推导交错与所有权条件。`Arc<T>` payload 建模保留的值身份与替换；`T` 内部任意修改、回调、析构函数和外部 I/O 没有因此获得深层状态证明。

扩展指令集需要经过验证的实现、声明的读写范围，以及真实历史与逆操作所有权的接入，不能仅给任意回调贴上“纯函数”标记。原生生命周期调度器、一般所有权闭包、剩余执行路径和最终式 (55) 组合，仍属于固定的 R3-A/B/C/D 工作。
