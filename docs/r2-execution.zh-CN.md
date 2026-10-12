# R2：生产执行路径的合同

[English](r2-execution.md) · [论文里程碑](paper-refinement-roadmap.zh-CN.md)

R2 要把论文约束连接到实际的托管调用。**R2 仍在推进中。** 下列合同已经用于
Rust 和 Node 宿主，补齐了载荷和结果传递的缺口；它们尚不构成整个宿主的语义
refinement，也没有证明任意插件回调满足 Component 合同。

## 已用于实际运行的合同

| 用户可观察的行为 | 可执行合同 | 生产调用者 |
| --- | --- | --- |
| publication 持有 owner 实际传入的值 | `PublicationStore::publish_checked` 检查真实生命周期域、代次和准入，再保存泛型载荷 | `Driver::publish` → `LifecycleDriver::publish_value` |
| 替换保留 publication 身份并返回真实旧值 | `replace_checked` 和 `ValueCell::replace`；拒绝时原样返还新值 | `Driver::set`、Rust `ServiceSlot::replace` |
| 旧清理租约仍读取自己保留的值 | `leased_value` 从真实租约记录中取得 publication 身份与载荷 | `Driver::read` |
| 只有生命周期和完整资源清单检查通过，才能转移实际载荷 | `finish_resources` 将已有票据／租约协议与载荷转移组合；拒绝时三者均保持原状 | `LifecycleDriver::finish_cleanup_values` |
| 异步清理消费其 Future 实际返回的结果 | `await_completion` 用 Verus 原生 Future 语义保存来源与实际结果；`complete_future` 据此判定成功、失败或消耗 | Rust `initialize_cleanup`、`Runtime::finish_reply`、`StaticCleanupFuture::complete_reply` |
| 先保存实际返回的 inverse，再决定是否继续 | `CleanupQueue::land_result` 自行分配 token、保存实际 inverse，并根据结果和取消状态选择后续动作 | `Runtime::poll_groups` |

Node 容器保存的是实际的 `u64` JavaScript 值句柄；Rust 值单元保存的是实际的
`Arc<dyn Any + Send + Sync>`。这些合同不解释 JavaScript 对象的可变字段，也
不解释 Rust 值的内部可变状态。载荷无需实现 `Clone`、`Copy`、`Debug` 或相等比较。租约固定的是 publication
身份，而非不可变快照：替换该 publication 会改变其租约读到的值；新 publication
则使用另一个身份。

清理适配保留既有策略：可重试工厂失败后继续保留；普通 Rust 的一次性清理失败
可以报告为已消耗的 `Drained`，静态宿主采用 `RetainFailure` 并保持阻塞。
两者都不会被自动报告为成功恢复。待丢弃的工厂和被拒绝的载荷在记账互斥锁释放后
才析构，以便用户 `Drop` 安全地重新调用宿主。

## 与论文的对应

`publication_projection.rs` 把真实容器解释为键值查找表。
`publish`、`replace`、`revoke` 在自己的函数体中使用相应证明：

- 发布向当前不可见的键插入实际传入值。
- 替换只更新该键，并返回它真实的旧值。
- 撤销只移除该 publication 的可见性。重复撤销不能隐藏同键的新 publication。
- 改变租约元数据、回收已撤销的值不改变当前查找表；保留租约观察是另一个观察，可能改变。

这里解释的是注册表的可见性投影。宿主 phase、依赖和可用性检查仍会对服务查找
施加额外条件；单独这张表不是整个宿主观察。

这些是 §3.4 键局部更新的实际实例，对应 `coeffects::put`。它们不等于证明
多版本宿主注册表与 R1 的整个 reified context 相同。写回返回的旧值能够恢复单次
替换，也不能据此推导插件在干扰下的完整 inverse law。

`LifecycleState` 现在向上层传播插入时实际的 parent／dependencies／provisions，
Begin 时的 committed bindings，以及 Finish、Retire、Remove、Unload 的已有
控制步骤关系。记录压缩保持控制观察；显式重启和动态接口改变保留各自的扩展合同。

`land_result` 同时证明真实载荷更新，以及 Iter、Finish 或延迟 diversion 的
累加器投影。这一投影不解释不透明 inverse 函数的外部效果。论文没有对应守卫的
失败或显式效果组取消，仍属于宿主扩展。

## 异步证明的边界

对于传入 `await_completion` 的 Future，Verus 证明：如果完成值返回，其中保存
的就是该 Future 的真实输出，以及包装时传入的来源。这不证明它最终一定返回，
也不证明调度公平。`Completion` 的字段不能由接收者替换，但它不是外部 I/O 的
真实性凭证：调用者仍可以包装一个立即完成的 Future。

插件实参到 callback factory、factory 到实际 Future、返回 inverse 到实际效果，
仍需要经过检查的实现合同。调用任意闭包的普通 Rust 适配层在验证 crate 之外；
它们的测试和小型 `witnessed_completion` 调用者都不能证明全部生产回调满足这些条件。

## R2 剩余验收内容

1. 在可扩展的生产插件入口，建立“实参 → 实际执行的操作 → 结果 → continuation →
   真实 inverse”的关系，并由具体原语证明效果律；不能改成调用方提供预期结果，
   或直接假设任意回调正确。
2. 用同一受验证的生产状态持有并组合全部并发效果组、动态子插件、publication、
   已准入工作与排空／释放决定。当前载荷释放与票据／租约验证的组合比这个整体不变量窄。
3. 证明完整生产执行轨迹的步骤分类及其与 R1 解释的关系，包括明确列出的多版本和
   动态接口扩展。列出一些方法的分类本身不构成这一定理。

这些就是既有的 R2 退出条件，并非为了缩小范围而新增或替换的条件。本轮没有
提升原论文条目和四项集成审查的完成状态。

## 审查与复现

```sh
cargo test -p cordis-kernel --test publication_values --test async_completion --test cleanup_queue --offline
python3 scripts/record-development.py --offline
```

定向测试覆盖不可复制载荷、新旧 publication、过时代次、异域、完整清理清单、
Future 逆序完成、失败重试、析构所有权以及取消后的迟到落地。常规开发检查还会
重新构建并测试实际 Rust 和 Node 宿主。

四个负向对照分别把真实值改为 `None`、替换租约的 publication 身份、把实际等待到
的错误改成成功、允许已取消的 continuation 继续。定向实验必须先证明未修改版本、
编译错误版本，再确认指定合同确实拒绝该修改。定向通过不表示完整的 136 项负向
回归已运行，详见[验证等级](validation.md)。

绑定源码的开发报告独立记录完整正向检查，不表示发布验收或整篇论文完成。本轮
没有给 Rust 用户增加 Node 依赖，也没有引入时序逻辑库。
