# typed Child 合法，不代表当前能够插入

[English](typed-child-domain.md) · [精化里程碑](../paper-refinement-roadmap.zh-CN.md)

插件的组件定义可以合法，但另一个已登记插件预留了子插件所需的 provision，创建仍会
被阻塞。服务表为空不表示声明端口可用；retire 也不释放预留，remove 才会释放。

本案例把定义 48、52 连接到与 55–57 条相关的精确定义域边界。原清单状态保持不变。

## 形式化输入

[`paper_instantiation`](../../crates/cordis-kernel/src/paper_instantiation.rs)
提供具体的 `SmallState` 载体，以及已经证明插入、退役、背景保持和忠实读回定律的
编辑器。子组件是 dependency 为 `true`、provision 为 `false` 的 Unit iterator。
每个 key 的值类型是 `int`，解释覆盖载体上的全部输入。子组件满足完整 Component
谓词，超出了语法 membership。它声明 provision 而不安装值；定义 48 本身不要求
最终发布全部声明。

[`equal_observations_different_domains`](../../crates/cordis-kernel/src/typed_child_domain.rs)
在两个具体输入中检查同一 typed Child 和同一个 fresh 名字 2：

| 观察 | 预留之前 | 另一个子插件 1 预留之后 |
| --- | --- | --- |
| 父插件可见绑定 | `true → 7` | `true → 7` |
| 全表投影 | 不变 | 不变 |
| 父组件与阶段 | 不变 | 不变 |
| 名字 2 | fresh | fresh |
| provision `false` | 可用 | 被 Inactive 且表为空的子插件 1 预留 |
| 实际 typed instantiation | `Some`，捕获 child 2 的 inverse | `None` |

成功结果包含实际 child 名字、依赖名字的 continuation 和捕获的 retirement。
立即执行 retirement 有定义、保持表观察，并留下仍登记的 child。

## 与可执行代码的连接

`kernel_domain` 证明：在明确的容量、fresh 名字前提下，这个 typed primitive 的接纳
恰好等于相应注册域上的 `Kernel::insert_enabled`。`registration_matches` 对应已登记
名字与冲突 provision；它不解释运行时服务值、阶段或回调。

`check_instantiation` 调用生产方法 `Kernel::check_insert`，ghost 参数在运行时擦除，
不能提供运行答案。受检 `exercise_domain_gap` 从实际空 Kernel、insert 和 check 调用
自行建立注册关系，证明预留前成功、预留后拒绝。运行回归还检查真实的 `Conflict`
分类、retire 后仍被阻塞，以及 remove 后恢复接纳。
实际插入身份由 native 分配器决定；预检查成功不代表预留了未来的身份或端口。

```sh
cargo test --offline -p cordis-kernel --test typed_child_domain
./scripts/verify.sh --verify-module typed_child_domain --triggers-mode silent
```

第二条是局部开发检查。全内核证明与完整开发验收另由
[绑定源码的开发记录](../development-report.json)报告。

canonical 负控 `typed-child-check-accepts-reserved-provision` 将客户端中的生产检查
替换为无条件成功。其局部 selector 为 `typed_child_domain::check_instantiation`；
mutant 必须能编译，并在该函数的精确定义域后置条件处失败。局部实验不代表完整负控
回归或全部 canonical selector 已校准。

## 仍需完成的义务

子组件输入的 witness 没有建立创建者父组件的原始全上下文 witness，也没有构造递归
Gamma。native 示例连接了注册定义域，并未实现 `SmallState` 中带值的完整上下文。
因此，本结果不能无条件反驳原文 57、73 或 80，也没有完成 Component 到生产实现的
整体精化。

[R1 严格部分解释](../r1-semantics.zh-CN.md)现已提供独立的完整载体父组件／续体／子组件合同，以及真实值、代码与逆操作表示；还基于本案例证明了单一恢复／准入关系的障碍。原文总函数 witness 与生产回调／值精化仍保持独立；本注册定义域案例自身的范围不变。
