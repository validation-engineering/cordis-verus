# R2 第 2 包：宿主与 Node 组合

当前 R2 状态以[第 5 包统一验收](r2-acceptance.zh-CN.md)为准：managed-production/v1 范围已完成。下文保留各批次历史记录及其当时的验证范围。

[第 4 包](r2-production-composition.zh-CN.md)已补充实际引用表历史和生产协议分类；下文的验证边界仍然适用。

[English](r2-host-composition.md) · [R2 合同](r2-execution.zh-CN.md) · [论文里程碑](paper-refinement-roadmap.zh-CN.md)

本包把受验证的生命周期与服务身份连接到**宿主实际使用的引用**：Node 对象、Fiber、
所选回调，Rust 共享 Episode，以及静态强类型导入。可执行内核拥有真实引用表，检查
它们之间的归属关系；生产适配层直接调用这些函数。

本包完成的是这一引用与派发关联范围。**R2 仍在进行中**：完整配置语义、整个生产
步骤的 refinement 和最终 R2 验收属于后续包。本包没有证明任意 JS／Rust 回调体。

## 对用户的实际价值

- 服务读取返回真实已提交绑定选中的那个对象，包括因清理失败而保留的不可见
  publication。仍被 publication、Fiber 或回调 claim 引用的对象不能提前移除。
- Setup 与清理保留真实待处理生命周期票据的 claim。错误 Fiber、旧票据和重复回复
  不能完成该调用。正在运行的 setup 保留当时所选回调与配置引用；后续 restart
  才选择新的回调。
- 强类型 Rust 导入携带真实 Node 查询签发的封闭凭据。适配层先核对运行域、consumer、
  generation 和 port，再取得 provider 的原始强类型槽。静态组装检查完整的声明／
  继承端口集合，并保留传入的真实 `Arc`。
- 普通 Rust 的每次共享 Episode 访问都检查：锁内 execution 是否仍与不可变上下文
  一同签发的身份一致。替换了 execution 时，先拒绝，再阻止访问。

用户插件 API 无需改变。JS 兼容层要求原生 addon 的 `hostProtocol: 1`，因此需要
构建或安装配套 addon。对原生 Rust 库而言，Node 仍是可选兼容宿主。

## 真实生产路径

| 所有者 | 实际调用路径 | 合同 |
| --- | --- | --- |
| `Bridge<WeakReference<NativeObject>>` | JS `HostBridge` → Node-API bridge → `issue`、`publish`、`replace`、`resolve`、`remove` | 同一所有者内 ID 不复用；返回最初签发的准确引用；检查运行域，并按真实 publication 表检查保留条件。 |
| Fiber 表与回调 claim | `_activate`／`_cleanup` → `beginAction` → `Bridge::begin_call`；`completeAction` → 真实 driver 完成 → `finish_call` | 已绑定 Fiber、保留配方与待处理票据属于同域；只有该票据确实不再待处理，才核销 claim。 |
| `HostSnapshot` | `validateHostSnapshot` → `Bridge::snapshot` | 逐一检查所有保留 publication 和已登记 Fiber 都有对应引用；联合观察将真实 `Selected` 读取解释为这个引用堆上的查询。 |
| `Selected` | typed 请求 start → `NodeRuntime::select` → `ResolvedImport` → `typed_instance` | 私有凭据来自真实读取事件，保留准确的域、consumer、generation、port、publication 和 provider；替代重新解码 JSON 数字来构造选择。 |
| `static_values::Values<ServiceSlot>` | `StaticPlugin::begin` → `from_definition`；setup 读写 → checked values | 解析真实 realm 与继承端口；拒绝缺失、重复和额外导入；保留原始槽，按真实声明限制写入。 |
| `host_context::Association` | native／static 创建 → `SharedEpisode::checked_lock` | 上下文与 execution 共享真实生命周期来源和 work 域；实际 mutex 获取后立即检查这一关联。 |

桥接层的泛型载荷就是适配层实际使用的 Node-API 弱引用，并没有另建一套只含整数的
对象模型。[JS 适配层](../packages/compat-cordis/host-bridge.js) 在私有 `WeakMap`
中一次性关联 native box 与载荷，并在私有 root map 中保留活跃 box。原生查询返回
同一个 box；表操作不会调用载荷 getter 或回调。原生弱引用避免增加经 JS Domain
形成的原生强引用环。

`Object.freeze` 固定的是配方中的 callback／config **引用**，并未冻结用户配置或
闭包内部状态。HMR 可以改变下次所选回调，而不改写已经运行的调用所保留的配方。
这是派发身份保证，不是模块加载、任意回调效果或最终返回的证明。

快照是显式审查操作：覆盖缺失时拒绝，不假设所有 JS 引用都存在。它不增加运行时
证明日志，也不在每次服务读取中扫描全表。它尚未构成对所有生产适配步骤的归纳定理；
最终步骤组合由第 4 包完成。

## 从论文到代码的审查路径

| 论文义务 | 本包建立的连接 | 明确限制 |
| --- | --- | --- |
| 定义 29／式 (31)，服务选择 | 既有 `reads::result` 与 read-lift 合同选择实际 publication；`Selected::interpretation` 证明凭据来自该次读取；`HostSnapshot::selected` 将它连接到真实保留引用堆。 | 引用身份不解释可变 JS 对象的内部状态。 |
| 定义 30，实际函数解释 | 真实 setup 派发保留所选 Fiber、回调与参数引用；第 1 包提供受支持托管 Rust 程序体的函数／效果定律。 | 一般 JS 回调仍需各自语义合同；保留函数引用不等于证明 Component 成员资格。 |
| Begin／Finish／Unload 与已提交依赖 | claim 验证真实账本中的待处理票据；完成调用沿用受验证生命周期协议；保留 publication 阻止在清理阻塞／失败时移除引用。 | 身份检查不证明 JS 公平调度、调用真实性或清理最终完成。 |
| 上下文、声明与读写 | 静态组装解析真实定义和导入；native／共享上下文检查使用 execution 的真实签发身份。 | 外部静态嵌入方仍须提供真实的 provider／租约权限；Node 嵌入路径从受验证图中取得选择。 |

动态接口、回调派发与 HMR 仍作为明确的实现扩展。本包不会因为生命周期投影未改变，
就把它们称为完整观察上的论文静默步骤。仍为部分完成的组合义务见
[论文映射](paper-refinement-map.md)。

可执行合同位于
[`node_bridge.rs`](../crates/cordis-kernel/src/node_bridge.rs)、
[`node_reads.rs`](../crates/cordis-kernel/src/node_reads.rs)、
[`static_values.rs`](../crates/cordis-kernel/src/static_values.rs) 和
[`host_context.rs`](../crates/cordis-kernel/src/host_context.rs)。生产调用者包括
[driver bridge](../crates/cordis-driver/src/objects.rs)、
[Node-API bridge](../crates/cordis-node/src/bridge.rs)、
[typed 适配层](../crates/cordis-node/src/typed.rs) 和
[静态宿主](../crates/cordis/src/runtime/static_host.rs)。

## 验收与验证边界

[开发记录](development-report.json) 以源码指纹绑定完整未修改内核证明、Rust／Node
回归和打包检查。运行 `python3 scripts/record-development.py --check` 可检查新鲜度。
运行案例覆盖引用身份、ABA 替换、撤回和清理重试、错误／旧派发、真实 setup 等待期间
替换回调、静态 realm 解析，以及共享 execution 被替换时的拒绝。

五个规范负例分别针对：返回错误对象、接受非待处理派发、释放仍保留对象、为其他
static owner 写入、忽略共享 execution 的域。定向检查要求新的同范围正例、完整
突变体编译以及准确命名的合同失败；不等同于全量负例、发布或整篇论文验收。

构建配套 addon 后，可复现定向运行案例：

```sh
source scripts/toolchain-env.sh
cargo test --locked --offline -p cordis-kernel --test host_bridge --test static_values
cargo test --locked --offline -p cordis-node --test plugin_runtime
cargo test --locked --offline -p cordis-verus association_tests
node scripts/build-node.mjs --offline
node --test --test-timeout=30000 tests/node-compat/host-bridge.test.mjs
```

完整开发验收直接运行 `python3 scripts/record-development.py --offline`，无需再手工
重复它的底层流程。全量负例通过 `python3 scripts/check-negative.py` 独立运行。

明确保留的审查／信任边界包括 Node-API 引用解引用、JS 引擎和私有 box 适配层、标准
`Arc`／`Mutex` 语义、TypeId／命名空间转换、不透明回调与载荷内部状态、panic／I/O
真实性、调度及外部静态宿主租约。受验证组装和运行时归属检查缩小了普通适配层的
义务，但没有证明这些外部运行时。独立 native Journal 与 Node 实例保留各自历史。
