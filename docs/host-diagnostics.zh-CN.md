# 解释生命周期等待

[English](host-diagnostics.md) · 简体中文

Node 宿主通过 `ctx.snapshot()` 导出实际 shared Driver 状态，用于解释缺依赖、provider
等待消费者、清理失败和旧 episode 拒绝。读取快照不驱动转移，不运行 `Service.check`，
不重试清理，也不读取服务 payload。

```js
import { Context } from '@cordis-verus/compat-cordis';
const ctx = new Context();
try {
  const worker = await ctx.inject(['storage'], () => {});
  const entry = ctx.snapshot().plugins.find(node => node.id === worker.id);
  console.log(entry.blockers); // MissingProvider, port.service === 'storage'
} finally {
  await ctx.dispose();
}
```

内部调度和原生插件观察使用独立的轻量状态投影；完整依赖图和诊断记录只在显式请求
快照时生成。

Cordis 和 Harness profile 使用同一组诊断类型。这是宿主观察接口，不是另一套调度器，
也不是异步 callback 的新增形式化证明。

## 依赖和清理屏障

快照保留 `abi: 1`，新增 `diagnosticsSchema: 'cordis.driver/v1'`。ID 使用十进制字符串。
每个插件除既有状态外，还包含 `dependencies`、`committed`、`target`、`blockers` 与
Node 的 `host` 观察。端口保留 native key/realm ID；可用的 `service`、`realmLabel`
来自宿主此前已登记的名称，不会为了展示而查找服务。

| 原因 | 含义 |
| --- | --- |
| `MissingProvider` | 没有匹配的 provider 声明或保留 publication。 |
| `RealmMismatch` | 在其他 realm 观察到该服务，不表示这些 provider 已经就绪。 |
| `ProviderUnavailable` / `PublicationMissing` | provider 存在，但当前无法满足该端口。 |
| `CheckNotEvaluated` / `CheckPending` | 尚无可用的 availability 缓存结果，或检查仍在途。 |
| `CheckRejected` / `CheckError` / `CheckInvalidated` | 缓存的检查返回 false、抛错，或原始输入身份已失效。 |
| `CommittedConsumers` | 指定消费者 episode 仍保留这个 provider。 |
| `PendingAction` | 实际 setup/cleanup ticket 尚未完成。 |
| `RetiringChildren` | 保留的子节点阻止 inactive owner 继续执行或移除。 |
| `CleanupFailed` | 清理失败，仍需显式重试；成功 inverse 不重放。 |
| `Failed` / `TargetChanged` / `Unsealed` | setup 失败、当前与 committed 依赖不同，或注册尚未完成。 |

多个原因可以同时存在。如果 Driver 仍可使用此前接受的缓存结果，新 availability 检查
本身就不是阻塞。缺少 setup 依赖不会被列为 cleanup blocker。重试已经开始时显示
`PendingAction`，不能仅因保留着历史错误文本就判断当前仍失败。

`committed` 描述当前 episode 实际保留的 publication 和 provider generation；`target`
投影内核的当前 binding。替换过程中，binding 可能仍指旧 provider 且 `publication: null`，
而 root lookup 已能看到另一个 provider。诊断保留这种瞬态，不以根服务查询伪造内核
目标。target mismatch 不自动等于缺陷。

## 带标签的 inverse 观察

注册 effect 时提供标签，便于定位清理动作：

```js
ctx.effect(() => async () => { await flushBufferedWrites(); }, 'flush buffered writes');
const snapshot = ctx.snapshot({ includeTiming: true });
```

`host.action` 包含实际 native ticket 和当前清理阶段，例如 `draining-tasks`、`inverses`、
`draining-calls` 或 `closing-objects`。`host.inverses` 列出保留的注册：`id`、`parent`、
`owner`、`generation`、`registeredGeneration`、`label`、`state`、`attempts`，以及可用的
错误信息。状态分别是 `registered`、等待 effect initializer 的 `waiting`、`running`、
`failed`。插件直接返回的清理函数默认标签为 `plugin cleanup`。嵌套 effect 及同一个
函数的多次注册都有独立身份。

prepared generation-zero 资源保留 `registeredGeneration: '0'`；只有真实 setup ticket
接纳它时，`generation` 才更新。setup 前取消仍为零代次。成功 inverse 被移除；失败
项在显式 `retryCleanup()` 后仍保留相同 ID。嵌套失败包装也会重试，成功兄弟项不重放。
这里展示保留中的工作，不保存无限历史。原生 Rust stream/object/session close 失败
由 action stage 和 Driver error 反映，不给原生库内部操作伪造 JS inverse ID。

默认快照没有时钟，状态未变化时重复读取结果相同。`includeTiming` 为运行中的 action
和 running/waiting inverse attempt 添加 `elapsedMs`，表示自该动作/尝试开始后的宿主
经过时间，包含等待。它不是 CPU 时间、死锁判断或最终完成保证，也不为每一种依赖
blocker 提供计时器。

## 旧 episode 错误与边界

`CordisError` 保留原 code/message，并可附带不可变 `details`：`owner`、
`requestedGeneration`、`currentGeneration`、`removed`、`operation`。托管 continuation
和 Rust handle 的拒绝使用实际宿主身份。即使 generation 相同，已关闭或替换的 handle
仍可能被拒绝；不能仅靠代次比较推断准入。原生错误中缺少的字段不会通过解析消息来
猜测。读取或复制错误不授予权限。

快照是复制结果，不执行 effect metadata getter。错误与标签是应用提供的文本，因此
这里不承诺自动脱敏。服务值、callback 对象和配置 payload 不会被主动导出。

普通 Rust `Runtime::snapshot()` 仍是另一套[诊断接口](diagnostics.md)。该宿主遇到失败
的 `FnOnce` inverse 时会报告错误并继续清理，不是 Node Driver 的保留重试队列，详见
[语义说明](semantics.md)。两种诊断接口均不扩大内核证明范围，也不关闭论文中的
host-boundary 义务。

回归入口：[Driver 观察](../crates/cordis-driver/tests/driver_diagnostics.rs)、
[Node 观察](../tests/node-compat/diagnostics.test.mjs)、
[Rust object 准入](../tests/node-compat/rust-objects.test.mjs)。
