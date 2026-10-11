# 拒绝仍保留调用者的生命周期等待

[English](reentrant-wait.md) | 简体中文

受管回调可能一边保留 provider，一边请求卸载 provider 或它的 owner。等待卸载会使
回调一直不结束，而 provider 必须等该回调所属 consumer 清理完成。Cordis Verus
以 `REENTRANT_MUTATION` 拒绝这种请求，并指出实际被保留的 provider。

本案例覆盖一项具体的生命周期等待策略，不声称任意 Promise、Rust Future、锁或
跨进程 RPC 都不会死锁。

## 复现

在已准备 Node 和锁定 Rust 工具链的 checkout 中运行：

```sh
npm ci --ignore-scripts
npm run build:native
node --test --test-timeout=30000 tests/node-compat/wait-admission.test.mjs tests/node-loader/rust-module-reverse.test.mjs
```

测试覆盖 Cordis 与 Harness 两个兼容 profile。动态模块套件加载真实 Rust 库，
没有用 mock 替换桥接。绑定源码的[开发记录](../development-report.json)记录完整
验证结果；上述单独命令属于行为测试。

## 实际过程

测试建立 `consumer -> relay -> provider` 的 committed 服务依赖。
另一个 `branch` 拥有 provider；consumer 不在这个子树内。

1. consumer setup 中等待 `provider.dispose()` 或 `branch.dispose()` 都会被拒绝。
   错误给出 consumer、generation、target 和实际 retained provider。检查不会发起退役。
2. consumer cleanup 执行同一守卫。第一次清理故意失败，provider 和 relay 仍可读取。
3. 显式重试再次检查守卫并成功；外部调用随后可以正常释放 relay 和 provider。
4. 独立用例允许无关插件和其他执行域的卸载；两个并发入口也能完成嵌套的
   `JS -> Rust -> JS -> Rust` 调用。

错误说明当前回调保留了哪项依赖，不是超时报错，也不表示整个应用已经无法推进。

## 论文、合同与真实调用

| 义务 | 可执行合同或证据 |
| --- | --- |
| 保留当前 episode 捕获的 provider 身份 | `Kernel::committed_reaches` 在且仅在源 generation 仍有效时返回答案；答案等于存活 committed 边的自反传递闭包，不使用当前 target 解析。 |
| 精确拒绝建模范围内的等待冲突 | `Kernel::check_wait` 在当前 episode 下，当且仅当 invocation 不再持有未完成工作，或其 committed 闭包与 target 的所有权子树无交集时允许等待。拒绝返回真实被保留的节点。 |
| 将依赖保留接到清理顺序 | `retained_dependency_blocks_cleanup` 证明非自反的 committed 依赖路径会阻止 target 的实际内核清理守卫开放。 |
| 真实宿主调用受检实现 | `assertNotWaitingForAncestor` 通过真实 Driver 发送 `check_wait`；Driver 调用同时由 Cargo 编译和 Verus 验证的内核方法。 |
| 识别错误实现 | 规范负控分别放行被保留的 provider、放行旧 episode、误拒无关 target，变异的是真实可执行判断。完整负控回归与开发检查分开。 |

审查入口为 [wait_guard.rs](../../crates/cordis-kernel/src/wait_guard.rs)、
[Driver](../../crates/cordis-driver/src/lib.rs)和
[宿主守卫](../../packages/compat-cordis/runtime.js)。图规范独立于遍历算法：可达节点
属于所有包含调用者、且沿依赖边闭合的集合。实现利用内核已有的性质：存活依赖链上
的绑定记录位置严格递减。

[锁定论文](https://arxiv.org/pdf/2608.25512v1#page=36)的定义 54、L-Unload 和定理 70
约束依赖保留及释放顺序。等待准入是为落实这些约束增加的宿主规则，没有完成定理 73
的进展义务，也不改变论文覆盖清单。

## 验证边界

宿主仍须如实提供 invocation owner、`holding` 活跃事实和完整 AsyncLocalStorage
祖先链，选择正确的 Driver 执行域，转换 JSON 并实际抛出错误。这些事实及 JS/FFI
连接有测试，但不能由内核证明自动取得。判断只观察一个不可变内核状态，不为后续状态
预留权限。回调终止、调度公平、任意回调效果、域修改队列和一般 RPC 等待环仍在范围外。
已结束的 continuation 保留 episode 身份；除非仍持有独立 native 工作，否则不再阻塞等待。

下一项集成目标是将上述 invocation 与 transport 事实接到受检请求所有权，再将本案例
纳入独立 Harness 故障报告。已有的清理报告、重试与旧凭据保证单独见
[清理协议](../cleanup-protocol.zh-CN.md)。
