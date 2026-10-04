# 诊断、维护与可靠关闭

`Runtime::snapshot()` 只读取状态，不驱动用户 callback。它按 plugin ID 返回稳定排列的节点：phase、retired/restoring、parent、固定端口、committed 和当前 target，以及阻碍继续执行的原因。

- `MissingDependencies`：Inactive 节点还缺少哪些 key/realm。
- `SetupPending` / `EffectsPending`：异步初始化或哪些 effect group 尚未结束。
- `CommittedConsumers`：哪些消费者仍绑定到正在退出的 provider。
- `CleanupPending`：已进入恢复，或 Active 节点取消的 effect 仍在执行 inverse。
- `Failed` / `TargetChanged` / `RetiringChildren`：失败锁存、解析变更或子节点退休。

多个原因可以同时出现。原因只描述当前状态，不保证外部 future 会完成。`snapshot.to_json()` 返回带 `cordis.runtime/v1` 标识的 JSON；`snapshot.to_dot()` 区分实线依赖边和虚线 ownership 边，并转义插件名称。导出不读取 service payload；名称和错误文本仍由应用提供。

```rust
use cordis::Runtime;
let mut runtime = Runtime::new();
println!("{}", runtime.snapshot().to_json());
println!("{}", runtime.snapshot().to_dot());
let reclaimed = runtime.compact();
assert_eq!(reclaimed.removed_bindings, 0);
```

## 历史回收

`Runtime::compact()` 调用实际经过 Verus 验证的 `Kernel::compact_bindings` 和 `compact_declarations`。它们按稳定 filter 删除失效 binding 和已经 remove 的节点声明，保持其余元素顺序、live bindings、registered interfaces、节点 identity/phase 及 `wf`。可以在异步 setup 或 cleanup Pending 时调用，不需要丢弃 episode，也不改变正在使用的 provider。

runtime 每累计 256 次 episode 清理或节点删除，自动安排一次回收；应用也可在大量变更后显式调用。`storage_stats()` 报告当前记录数量，供检查 live bindings 与历史 records 的差异。这些是记录数，不是分配器容量或精确字节数。

**节点 tombstone 仍然保留。** PluginId 单调递增且永不复用，删除后旧 handle 不会指向新插件。反复 restart 同一节点不再无限积累 binding 记录；无限创建全新节点仍会增长 identity slots。框架不声称已经实现稀疏 identity 存储或严格常量内存。需要长期运行且产生海量 fresh revisions 的应用，应监测 `identity_slots` 并选择适当的进程/运行时生命周期。

测试把回收与未回收内核在多轮 provider revision、三层依赖、错误路径和清理期间进行逐步对照，还运行 1,024 次同 ID restart 检查历史回收与 provider binding 一致性。负向证明会把回收条件改成保留失效项、删除 live 项，并要求该错误实现能编译但不能通过证明。

## 显式 shutdown

`Runtime::shutdown().await` 退休全部插件、驱动清理、回收历史，然后汇总错误。`ShutdownError` 分别保留 lifecycle 错误、shutdown 开始时已锁存以及关闭期间落地的 setup 错误、所有尚未取走的 cleanup 错误。一个 inverse 失败不会跳过其它可执行 inverse，也不会伪装成资源完全恢复成功。

丢弃 shutdown future 只暂停驱动，不撤销退休请求；再次 shutdown 会继续，已记录错误不会因 pause 丢失。正常成功后可重复调用。保留中的事件 continuation、永不结束的 stage/handler 或阻塞 Drop 仍会阻止完成；框架不会通过强行丢弃在途工作破坏恢复契约。

需要分阶段控制时，原有 `dispose/dispose_all`、`join/settle`、`take_cleanup_errors` 仍可使用。单独丢弃 Runtime 不执行异步 inverse。上述诊断、自动维护和关闭编排是普通 Rust，只有其调用的 kernel primitive 及明确契约经过 Verus 验证。
