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
node --test --test-timeout=30000 tests/node-compat/wait-admission.test.mjs tests/node-compat/invocation-ledger.test.mjs tests/node-loader/rust-module-reverse.test.mjs
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

## Rust Future 结束后仍在进行的请求

Rust 插件可能发出两个 JS 请求，丢弃它们的 Future 后返回。真实 transport 在交给
JS 前记录两个请求；取消不会撤销记录。乱序回复只消费自身的精确票据，第二个回复
到达前，job 仍不能结束。

`RequestTicket` 记录 domain、owner、generation、session、job、request 和恢复权限。
回复必须在每个字段上匹配尚未结束的票据；不匹配、重复或跨域回复不改变任何记录。
JSON 中所有数字身份
都使用十进制字符串。域内请求 ID 不回绕、不复用；已完成记录会回收。native 回调的
生命周期等待准入读取这份真实记录，不接受 JS 提供的 `holding` 标志；已结束请求的
票据返回 `StaleAuthority`。

动态模块回归创建两个并发 root：数字 session/job/request ID 相同，domain 不同。
测试拒绝跨域及字段被修改的回复，确认两个回调仍 pending，再接受实际回复、拒绝重放，
并确认模块资源计数归零。backend 回归还覆盖一个 job 丢弃两个 Future 后取消，随后
收到乱序的成功／失败回复：

```sh
# 通过仓库环境使用固定工具链。
bash -c 'source scripts/toolchain-env.sh; cargo test --offline --locked -p cordis-node --test plugin_runtime exact_receipts'
```

失败回复只确认请求已经结束，不表示资源清理成功；stream/object 失败仍保留在资源
journal 中供重试。票据是内部生命周期身份，不是不可伪造的安全凭据。插件继续使用
既有 `ctx.call`、stream 和 object API。自定义 addon 须在 `rustInfo` 中声明
`requestProtocol: 1`，JS bridge 会在派发前拒绝旧协议；动态库 ABI 不变。

## JS 作用域与已结束的 continuation

setup、cleanup、owned task 以及 effect 初始化／逆操作在运行回调前，会向 native
`InvocationLedger` 登记。登记检查内核当前 generation；返回的 `ScopeHandle` 只含
domain 和 scope 身份，owner 与 generation 保存在原生记录中。回调成功或失败会结束
自身作用域；单独取消不表示结束。

真实等待路径将本域 ALS 作用域身份列表交给 `check_scope_wait`。受检遍历在且仅在
所有传入身份均已分配、且每条仍存活记录的代次有效且不存在建模冲突时放行。已完成的
嵌套作用域不能使遍历跳过仍存活的祖先。拒绝给出实际记录的 owner 与保留的 provider；
JS 不再向这项判断传入 owner 元数据或可覆盖结果的 `holding` 标志。

已完成记录立即回收，身份永不复用。旧身份仍可表示不再持有工作的调用来源，因此普通
游离 continuation 可以在 setup 结束后等待 settle 或关闭域。未分配或跨域身份被拒绝，
重复结束不能消费其他作用域。已完成 continuation 的代次新鲜性仍由 JS episode 守卫
检查。该账本证明所有权记账与等待准入，不是独立的清理屏障，也不证明回调确实已结束。

`invocation-ledger.test.mjs` 观察真实原生命令：取消两个并发任务，乱序结束（含失败），
检查仅已完成的记录消失；嵌套 effect 覆盖传入的祖先集合。诊断字段
`snapshot().storage.invocationScopes` 表示存活 JS 回调记录，不是 effect 资源数量。
自定义 addon 须在 `bindingInfo` 声明 `scopeProtocol: 1`；公开插件 API 不变。

## 论文、合同与真实调用

| 义务 | 可执行合同或证据 |
| --- | --- |
| 保留当前 episode 捕获的 provider 身份 | `Kernel::committed_reaches` 在且仅在源 generation 仍有效时返回答案；答案等于存活 committed 边的自反传递闭包，不使用当前 target 解析。 |
| 精确拒绝建模范围内的等待冲突 | `Kernel::check_wait` 在当前 episode 下，当且仅当 invocation 不再持有未完成工作，或其 committed 闭包与 target 的所有权子树无交集时允许等待。拒绝返回真实被保留的节点。 |
| 将依赖保留接到清理顺序 | `retained_dependency_blocks_cleanup` 证明非自反的 committed 依赖路径会阻止 target 的实际内核清理守卫开放。 |
| 真实宿主调用受检实现 | `assertNotWaitingForAncestor` 将 JS 作用域接到 `check_scope_wait`，反向 Rust 票据接到 native `check_wait`；两者组合账本所有权与同时由 Cargo 编译和 Verus 验证的同一内核判断。 |
| 将所有权接到真实 native 请求 | `PluginContext::enqueue` 调用 `RequestLedger::issue`；`Backend::reply_request` 在同一 transport Mutex 下调用 `complete`；`Backend::poll` 使用精确的 `job_drained`。取消和丢弃 Future 不消费票据。 |
| 组合请求所有权与等待判断 | `RequestLedger::check_wait` 要求 Driver 域内已记录的完整票据，再以持有未完成工作的身份调用受检内核判断。`assertNotWaitingForAncestor` 将反向回调接到此路径。 |
| 记录 JS invocation 所有权 | `InvocationLedger::begin` 记录当前 owner episode；`finish` 只移除自身存活记录并保留其余记录。单调身份计数不复用 ID，也不保留已完成记录。 |
| 检查传入的所有祖先 | `InvocationLedger::check_wait` 当且仅当全部传入身份已知、所有存活记录有效且无冲突时放行；`any_live` 用同一账本判断域是否仍有调用工作。 |
| 识别错误实现 | 规范负控分别放行被保留的 provider、放行旧 episode、误拒无关 target，变异的是真实可执行判断。新增负控接受被修改的请求归属、在回复前排空、在等待判断中忽略存活请求。作用域负控忽略存活记录，或在已完成的嵌套作用域处提前结束遍历。完整负控回归与开发检查分开。 |

审查入口为 [wait_guard.rs](../../crates/cordis-kernel/src/wait_guard.rs)、
[请求账本](../../crates/cordis-kernel/src/request_ledger.rs)、
[调用作用域账本](../../crates/cordis-kernel/src/invocation_ledger.rs)、
[transport](../../crates/cordis-node/src/plugin.rs)、
[Driver](../../crates/cordis-driver/src/lib.rs)和
[宿主守卫](../../packages/compat-cordis/runtime.js)。图规范独立于遍历算法：可达节点
属于所有包含调用者、且沿依赖边闭合的集合。实现利用内核已有的性质：存活依赖链上
的绑定记录位置严格递减。

[锁定论文](https://arxiv.org/pdf/2608.25512v1#page=36)的定义 54、L-Unload 和定理 70
约束依赖保留及释放顺序。等待准入是为落实这些约束增加的宿主规则，没有完成定理 73
的进展义务，也不改变论文覆盖清单。

## 验证边界

native 请求账本证明精确发票、回复消费、pending job 查询及其与等待守卫的组合；
JS invocation 账本还证明登记、精确结束、记录回收和对传入作用域列表的遍历。
两份 Rust 实现同时由 Cargo 编译和 Verus 验证。普通宿主代码仍负责在构造 context 时
捕获 owner/session/job 身份，在 Mutex 下维护 payload、waker 与记录的对应，派发 JS、
报告实际结果、保留完整 AsyncLocalStorage 祖先链并抛出错误。JS 仍决定何时登记和
报告回调结束。这些连接有测试，尚无整个宿主的 refinement 证明：原生遍历无法识别
宿主漏传的祖先。作用域身份和请求票据都是内部身份，不是防御同进程任意代码的安全凭据。

判断只观察一个不可变内核状态，不为后续状态预留权限。回调终止、调度公平、任意回调
效果、域修改队列和一般 RPC 等待环仍在范围外。已结束的纯 JS continuation 可保留
episode 身份而不持有 action；反向调用的游离 continuation 不能在回复后复用旧票据。
backend shutdown 会放弃 transport 并报告失败，不能当作资源清理成功确认。

下一步把本案例纳入独立 Harness 故障报告，并审查回调实际结果与 ALS 祖先完整性
这两项剩余宿主边界。已有的清理报告、重试与旧凭据保证单独见
[清理协议](../cleanup-protocol.zh-CN.md)。
