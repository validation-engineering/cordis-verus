# 生成式生命周期证据

[English](generated-lifecycle.md) · 简体中文 · [原始更新恢复案例](update-recovery.zh-CN.md)

`provider-consumer-one-child/v1` 将五条用户保证连接到真实执行、可执行 Verus 合同和
故意破坏的实现。它通过生成历史扩展固定案例，不关闭 R01 或整篇论文义务。
所有权、调用路径及边界见[审查地图](../review-map.zh-CN.md)。

## 复现

使用仓库锁定的工具链与已安装的离线依赖。Native 场景和重放需要 Rust、Python；
上游比较另外需要 Node、锁定 Cordis checkout 和 npm 依赖。证明负控需要 Verus，
但用户运行已经编译的应用不需要运行 Verus。

```sh
python3 -B scripts/check-lifecycle-campaign.py native --offline --seed 260824 --cases 96
python3 -B scripts/check-lifecycle-campaign.py compare --offline --build --seed 260824 --cases 48
python3 -B scripts/check-lifecycle-campaign.py controls --offline --seed 260824 --cases 12
```

整体验收先完成源码修改，在最终源码上运行一次开发记录器，再运行上面三个命令、
原有精确对照及审计。若开发记录器已构建同一份 Node 源码，对照可省略 `--build`。

```sh
python3 scripts/record-development.py --offline
# 在源码不变的前提下运行上面的 native、compare 和 controls。
node scripts/check-node-compat.mjs
python3 -B scripts/check-lifecycle-campaign.py accept
```

`target/lifecycle-campaign/` 保存完整输入、原始 stdout/stderr、命令、版本与哈希。
`acceptance/report.json` 将最终源码绑定到开发检查、生成执行、上游比较、缩减和
严格证明记录。审计命令检查证据，不重新运行证明。`target` 中是本地产物，不代表
已经上传到 GitHub Release。

## 实际运行什么

| Profile | 真实执行器 | 观察及边界 |
| --- | --- | --- |
| `native-managed/v1` | [`lifecycle_scenario`](../../crates/cordis/examples/lifecycle_scenario.rs) 调用 `NativeRuntime`、recorded root／Child 和真实 inverse dispatch | 同时检查值和深度、target／committed 身份、owner／Episode／action／restore 票据、原始 Child 句柄、publication、保留槽位及每个中间状态。观察器刻意保留值句柄以检查终态，不是分配器回收测试。 |
| `plugin-lifecycle/v1` | [共享 JS fixture](../../tests/compat/lifecycle-scenario.mjs) 分别绑定原生 facade 与锁定的原版 Cordis | 真实公开 API 的 setup、publication、清理尝试、错误、资源身份、所有权／Episode 和回调顺序。原生诊断另外检查依赖保留，不据此声称 JS callback 已获证明。 |

Native 生成器变化注册顺序、有界标量参数、Child／consumer 故障位置、同值干扰、
重复失败、显式重试和旧／重复回复。每条完整 Native 场景都必须成功运行多个 root／
Child Episode，并在关闭时恢复初始值和深度。有效场景、故意无效命令和干扰三类
必须实际出现；全部拒绝不能通过。

生成器的小型算术模型选择输入、检查快照，不给执行器注入 ghost journal、历史、
收据或预期结果。[生成器](../../scripts/lifecycle/scenarios.py)与
[观察检查器](../../scripts/lifecycle/oracle.py)属于普通测试代码，不是另一份运行
实现，也不是生成器自身的形式化证明。

这些是有限、有种子且按必需场景分层的历史，不是任意插件的均匀随机样本。Native
内部票据操作没有对应的原版公开 API，因此保留原生保证测试，在插件对照中明确记为
不支持。任意异步调度、一般别名迁移、不透明 `Arc<T>` 效果和全局终止不在此范围内。

## 不掩盖差异的对照

报告列出尝试数、完成进程数、支持数，以及 `matched`、`intentional_difference`、
`unsupported`、`unexplained`／`inconclusive`。未解释差异、崩溃和超时阻止验收。
成功退出的进程仍可能报告不支持，不用一个“兼容百分比”掩盖这些结果。

ID 投影只允许真实注册 ID 与观察到的 birth 之间的受检双射，保留父归属、不同 Child
创建、Episode 和资源绑定。原始 ID、错误、快照和完整有序事件都保留。不会排序回调
事件来制造相等。原生专有诊断单独记录，因为上游公开 API 没有同一观察面。
原有固定差分 fixture 继续进行其**不做归一化的精确比较**。

以下两项差异只针对该 fixture 和锁定版本审查：

| 策略 | 原生 facade | 锁定的原版 Cordis | 验收要求 |
| --- | --- | --- | --- |
| `dependency-cleanup-order/v1` | Child、consumer、provider 顺序执行清理回调 | 本更新 fixture 中为 provider、consumer、Child；先关闭 consumer 时为 consumer、Child、provider | 分别检查两边完整顺序和身份；无故障场景的其他公开状态／结果必须一致，不推广为任意上游调度的结论。 |
| `cleanup-failure-retention/v1` | 抛错阻塞更新，保留旧依赖并阻止相关 provider 释放 | `_unload` 记录错误、消费该 disposable 并继续更新 | 核对注入错误、失败对象、保留资源、所有中间状态及两边完整事件顺序；不能将任意不一致归入此策略。 |

上游依据是不可变 checkout 的 `packages/core/src/fiber.ts` 中 `_unload`，锁与源码
字节绑定在 bundle 记录中。原生策略经共享 Driver 接到
[`LifecycleState`](../../crates/cordis-kernel/src/lifecycle_state/cleanup.rs)。公开
API 对照是对这条连接的实测证据，不是对 JavaScript／FFI 的证明。

重试扩展在更新失败后显式执行 `settle_fault` 观察域级错误，然后修复故障并调用
`retryCleanup`。更新 promise 拒绝后，域里仍可能有尚未被观察的错误；场景保留这次
诊断，不将其吞掉。原版没有对应的公开 `retryCleanup`，所以该扩展整体记为不支持，
同时独立检查原生恢复、再次更新和最终关闭。

## 对同一错误实现比较测试和证明

既有[五项负控](../../scripts/negative-controls.update-recovery.json)是唯一变异来源。
运行器复制实际 workspace，只修改指定实现表达式，完成编译，然后交给真实行为
调用者和不变的严格证明检查器。

| 变异 | 行为调用者 |
| --- | --- |
| 失败报告当成功 | 实际 `execute_cleanup` 命令循环及重复失败回归 |
| 绕过成功收据释放 | 同一调度入口回归，检查拒绝释放和 provider 保留 |
| 丢弃保留载荷 | 拥有真实载荷、地址及析构计数器的队列测试；适用的生成资源轨迹 |
| 忽略逆操作深度 | 同值干扰测试和 Native 生成历史 |
| 拆开 Child 请求与逆操作 | 原始句柄与实际注册关联测试及生成 Child 观察 |

Native 生成器直接调用受管 primitive，不覆盖仅位于 `execute_cleanup` 的变异；
这部分由真实调度入口测试覆盖。`generated` 和 `targeted` 的结果分别记录为已发现、
未发现或无法判定，并说明适用边界。指定测试必须实际执行，并在审查过的断言位置
失败，才计作发现；编译错误、零测试或无关 panic 不计。证明拒绝要求新正向基线、
完整变异编译和恰好指定合同诊断。全量负控和发布验收单列为 `not_run`。

忽略深度的变异还用于缩减。每个候选必须在原实现通过，并在变异实现违反**同一保证、
同一操作和同一角色**。缩减器删除命令，最后逐一检查剩余命令均不能单独删除；只宣称
该判据下的单步删除极小，不宣称全局最短。保存原始／缩减后的完整命令、全部试验日志、
制品哈希和重放命令。例如正常场景可这样重放：

```sh
python3 -B scripts/check-lifecycle-campaign.py replay --offline --input target/lifecycle-campaign/native/scenarios.json
```

缩减报告中的 `replay` 命令选择保存的变异制品及预期失败。缩减前缀是失败证据，不能
冒充完整关闭场景。`controls --behavior-only` 只是集成试运行，不能满足配对或整体验收。
