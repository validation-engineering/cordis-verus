# 原版 Cordis 插件的原生兼容运行时

原版插件在 Node 中执行，生命周期由 Rust Driver 调用可执行 Verus 内核决定。对象、函数、Promise、Symbol 和循环引用保留在 JS 对象表中；Node-API JSON 只传递命令、动作凭证和不透明句柄。Rust 外部进程插件协议仍是另一个入口。

当前有两个显式 profile：锁定的 `cordis@4.0.0-rc.10` 和 `@deepseek-ai/cordis@4.0.4`。它们共享内核与驱动，分别处理配置、失败重试和更新返回值。原版核心完整测试、同源差分、宿主回归和 Verus 证明分别记录，不能互相替代。当前仍是实验项目，完整生态兼容与发布验收尚未完成。

## 构建与原版导入

本机验收基线为 Node 22.22.0 / macOS ARM64。其他平台、Node 版本和预编译包需要独立验收。

```sh
./scripts/install-verus.sh
npm ci --ignore-scripts
npm run build:native
npm run example:node
npm run test:node
```

```sh
# 独立 Cordis 原插件
node --import @cordis-verus/compat-cordis/register app.mjs
# Harness Cordis 原插件
node --import @cordis-verus/compat-harness/register app.mjs
```

引导器覆盖所选 bare 包名的 ESM、dynamic import、CommonJS、createRequire。两个入口不能在同一 environment 混用；不支持的 deep imports 会拒绝，不会回退到原版调度器。直接开发也可导入项目自己的包名。TS 应显式构建为 JS；注册入口不是 TS 编译器。

```js
import { Context, Service } from 'cordis'
class Greeting extends Service {
  constructor(ctx) { super(ctx, 'greeting') }
  hello(name) { return `Hello, ${name}` }
}
const ctx = new Context()
await ctx.plugin(Greeting)
await ctx.inject(['greeting'], ctx => {
  console.log(ctx.greeting.hello('Cordis'))
  return () => console.log('consumer cleanup')
})
await ctx.dispose()
```

本机生成的原生二进制为 `packages/compat-cordis/native/cordis.node`，不提交 Git。默认加载器根据 `native/manifest.json` 选择当前 OS/arch/libc/Node-API 的产物并校验二进制与 provenance 哈希；本地合包工具可组合不同 host 的真实构建，使用见[原生产物分发](native-distribution.md)。`target/node-compat/build.json` 绑定二进制、Rust 源码和锁文件；源码改变后必须重建。加载检查 ABI、profile、package 与值表示，越过旧 Plugin 执行器隔离、到达 Node 边界的 panic 会令该 domain 失效。`CORDIS_NATIVE_BINDING` 或 Context 的 `addon` 选项可指定构建，不会启用 JS 调度器回退。

## 生命周期与资源

| 合同 | 实现与边界 |
| --- | --- |
| 公共控制 | Rust Runtime 与 Node Driver 共用 `shared::LifecycleDriver`，统一状态决策和验证的 ActionLedger；各自保存 Future/JS callback 与值 |
| 动作身份 | domain、fiber、generation、action、kind 精确匹配、至多完成一次；取消不丢弃在途 setup |
| FFI 重入 | command 完成并释放 Rust 借用后才执行任意 JS |
| 动态服务 | 发布属于真实逻辑 fiber；撤销阻止新解析，旧消费者保留 committed publication lease 至清理完成 |
| 跨 owner 替换 | 新值可以发布；旧声明等旧消费者清理后转交，新消费者不能越过该屏障 |
| 服务检查 | `Service.check` 同步执行；ticket 绑定 publication、值 revision、通知 revision；重入产生的旧结果不能覆盖新结果 |
| `set` | 替换同一 publication 的值并安排旧槽回收，不隐式触发 check 或依赖重启；需要 `reflect.notify()` |
| 预注册 | reserve/own → `internal/plugin` → seal；观察器修改 inject 后才封闭声明；启动前资源也需要真实清理凭证 |
| 清理失败 | 保留失败 inverse、旧服务恢复视图与 provider 屏障；`fiber.retryCleanup()` 对 JS inverse 只重试未成功项；普通 SDK 会重新调用整个 cleanup hook，由插件记录已完成步骤；旧 typed Plugin 的 `FnOnce` 失败持续保留，不能重放 |
| 启动失败 | `await()` / `update()` 报告初始化错误；已完全排空的 `dispose()` 报告清理结果，不重复抛出历史启动错误 |
| 显式任务 | `ctx.task(fn)` 的 AbortSignal 只请求合作取消；任何业务 inverse 执行前等待任务真正落地 |
| 普通事件 | 同步返回、抛错和派发快照保持；普通 async listener 不自动变为清理屏障 |

清理失败由 native `cleanupFailed` 持久状态记录，先前的 `settle()` 或 readiness 错误观察不会把它变成成功。`dispose()` 会报告阻塞自身、owned 后代或 committed consumer 的失败；需要从实际失败节点开始显式 `retryCleanup()`。若父级 inverse 也已因子节点失败而失败，应自底向上分别重试。已真正排空的历史 setup 错误不会阻止正常 disposal。

`fiber.inertia` 在 native 接纳的 setup/cleanup 执行期间暴露实际等待句柄，完成后清除；官方 Loader 可以循环读取它，等待 cleanup → restart → setup 的完整变化。它只观察该 Fiber 的当前阶段，不等待整个 domain，也不把等待完成解释为启动成功。

`await ctx.plugin()` 在依赖缺失时可以返回 Pending，不能当作 ready 证明。`ctx.settle()` 等待图中启动/清理工作，不等待仍在运行的常驻 owned task；`task.join()` 显式等待结果，关闭则等待任务落地。任务只能在已获准的 activation 中启动，不能把 generation 0 的预注册任务默认为第一个 episode。

```js
const job = ctx.task(async signal => {
  await runUntilAborted(signal)
}, 'background worker')
job.cancel()               // 发出合作取消请求
await job.join()           // 等待真实完成
await ctx.dispose()        // 同样会等待所有 owned task，然后清理资源
```

自等待检查区分动作是否仍在执行与 continuation 所属的 episode：setup 已返回后启动的后续流程可以正常请求关闭；仍由 journal 持有的异步 effect、inverse 和 owned task 保留等待约束，不能关闭正在等待自身的祖先或 domain。已完成动作的后续回调仍带原 episode，重启或卸载后不能重新取得服务或登记资源。过期回调可以通过内置 logger 记录诊断；logger exporter 注册、派生 Context 的服务/资源访问仍会拒绝，不会清空 AsyncLocalStorage 权限信息。

任意永不完成的 Promise 可以阻塞相关清理。AsyncLocalStorage 检查框架托管 continuation 的 episode，无法推断任意逃逸 closure 的历史来源。框架可识别的自等待会明确拒绝；一般 Promise 等待环不保证可检测。

## 两个 profile

| 策略 | Cordis | Harness |
| --- | --- | --- |
| 初始配置 | mount 时同步校验 | 依赖齐备后，通过 `internal/config` 与 schema 解析 raw config |
| 重新激活 | 使用已解析配置 | 每次重新解析 raw config |
| update 返回 | awaitable，或 hook veto 后 undefined | void；通过 fiber.await 等待 |
| Failed 重试 | 显式 update/restart | 相关依赖通知也可重试；无通知不会无限自动重试 |
| 卸载观察器 | 原异常可见，但仍执行已提交的清理 | 分别记录同步/异步 observer 错误，继续清理 |

两种 profile 均支持方法/类 Inject、可调用 Service、traceable/shadow、accessor/mixin、LoggerService、事件与 effect。类型保留各自包名的 Context augmentation，Harness 声明由公共 API 生成，避免手工维护两份。类型 fixture 不是上游所有泛型合同的证明。

以下是明确的行为差异，完整上游测试不会跳过它们：

- `Fiber inertia lock 2`：上游可以在 Loading 中撤销后同 owner 重发布时恢复旧 epoch；内核已经执行的 withdrawal 不会被撤销，会先清理再重新激活。旧 lease 不被偷偷替换。
- `Fiber dispose error`：上游记录并吞掉 inverse 错误；这里保留失败资源并拒绝完成，等待显式 retry。返回成功会错误宣称资源已恢复。
- Harness 的 wrapped fiber update receiver 缺陷在本实现中修正，更新作用于实际 fiber。
- Service.check 重入旧值失效时不自动重新调用，必须由真实 notify 触发；通知环最多执行 256 次后报告诊断。

这些差异限制“完全替换”的声明；需要逐个目标应用验证。

## 同域外部变更事务

`domainMutation(ctx, callback)` 为同一 Context 域内的多个 JSON Loader、直接 Fiber
update/restart/dispose/retryCleanup 与最终 `Context.dispose()` 提供统一提交顺序。
它是兼容层扩展；同步 `ctx.plugin/provide/effect` 仍保留原调用形态，应用可以把外部批量
操作显式放进事务。原版官方 Loader 整条配置持久化事务、Worker supervisor 与模块图 HMR
仍需各自适配，不能把这里的 Fiber 级接入称为全部装载协议已经完成。

```js
import { domainMutation } from '@cordis-verus/compat-cordis'
await domainMutation(ctx, async steps => {
  await steps.update(existingFiber, { prefix: 'Welcome' })
  await ctx.plugin(anotherPlugin)
})
```

回调使用 `steps.update/restart/dispose/retryCleanup` 执行内部生命周期步骤；直接嵌套
外部 mutation 会拒绝 `REENTRANT_MUTATION`。steps 绑定当前事务和调用来源；受管理的
setup/cleanup/task/effect 回调及其完成后的续程不能借用，`internal/update` 回调也不能借用外层 steps，事务结束后能力失效。已发出的步骤必须落地；即使回调未等待它们，
其失败也不能变成成功提交。回调自身失败保留原错误及 Loader code/details，其他步骤错误
保存在 snapshot diagnostics。事务只保证排队和排空，不自动回滚已完成的 Fiber 变更或外部副作用；JSON Loader 的旧 recipe 恢复由 Loader 另行实现。

为保留官方 Include/Group 的调用方式，`internal/update` 的**同步调用栈**可以发起子插件或无关 Fiber 的 update/restart/dispose；这些操作加入当前事务，清理及失败仍由该事务收束。该调用栈不能等待自身、owner 或自己保留的 committed provider，也不能被新插件动作、effect 回调或异步续程借用。显式嵌套 `domainMutation` 仍被拒绝。这个兼容规则不把原版 Loader 的文件持久化、模块导入和整批配置变更变成原子事务。

失败 cleanup 阻止新的外部 revision；`{ recovery: true }` 仅用于 dispose/retryCleanup，
不能挂载插件或获取新资源。最终关闭一经接纳便关闭新外部准入，但已接纳事务内的
child/effect/completion 继续推进；关闭失败仍保留恢复入口。Harness update 仍返回 void，
`fiber.await()` 从事务外等待已排队的更新/卸载；Cordis 未排队的 veto 可直接返回 undefined；排队的 update 返回 Promise，veto 仍生效。
普通 JS 与 Rust 回调均拒绝等待自己仍保留的 committed provider。

## JSON Loader 与 Worker 代码更新

`@cordis-verus/compat-loader` 提供 JSON Include/group、稳定 entry ID、isolate/inject、模块解析、串行配置事务和失败恢复。配置更新先准备模块，按稳定 ID、factory/revision、配置和 realm 比较，只排空变化子树；未变 Fiber 保留，依赖触发的 episode 重启仍由 Driver 决定。候选失败必须先清理候选，再按保存的旧 factory/config recipe 恢复。内部 child/effect 注册不排在全局事务队列后面。

```js
import { Loader } from '@cordis-verus/compat-loader'
const loader = new Loader(ctx)
await loader.loadFile('./cordis.json')
await loader.update('greeting', { config: { prefix: 'Welcome' } })
await loader.dispose()
```

这是一套明确的 JSON API，尚未实现原版 Loader/Include API、YAML、lazy/volatile 配置或细粒度 HMR。当前 environment 的 reload 保留 Node 模块缓存。ModuleHost 的 loadModule adapter 可接收外部准备的稳定 factory 和 revision，但不负责清空 ESM/CJS 缓存。代码替换使用 `WorkerDomain`：捕获完整本地制品目录，新 Worker 加载新一代代码，失败时使用保存的旧制品恢复。查询参数不冒充 ESM 缓存清理。符号链接被明确拒绝；制品边界、依赖、资源与持久化目录需按 [Loader 说明](../packages/compat-loader/README.md) 配置。

正常关闭必须获得 shutdown 确认，且所有已登记调用和资源清理完成。Worker 异常退出、无确认的 exit(0)、超时强杀均记录为 abandoned，不能报告 clean rollback。跨 Worker 调用使用显式 JSON 边界，不保留任意 JS 对象身份。

运行 [配置示例](../examples/node-loader/main.mjs) 和 [Worker 示例](../examples/node-loader/worker.mjs)：

```sh
npm run example:node-loader
node examples/node-loader/worker.mjs
```

真实 Harness 差分直接构建锁定源码中的 SessionStore、SystemPrompt、ToolRuntime、SessionProjectionRegistry、tool-todo 与 createScope，global/scoped 两种场景比较 44 条原始有序观察，覆盖 schema、调用、会话投影、AbortSignal、作用域隔离和卸载重载。没有修改上游插件，也不调用外部 LLM。这仍不是完整 Harness 应用的验收。

## Rust 对象与回调的所有权

`MethodKind::Object`/`PluginObject` 导出固定类型名、方法白名单和 borrowed/owned 合同；JS 用私有品牌 wrapper 的 `call()` 和 `close()`，仅 `call` 接口的 callback 另有 `invoke()`。反向的 `adaptObject`/`adaptCallback` 由 Rust 的 `ctx.open_object()`/`open_callback()` 取得。borrowed close 只释放 adapter 引用；owned close 等待真实异步析构，失败保留资源供重试。所有对象方法仍只交换 JSON DTO。

consumer 普通 inverse 全部成功后，才按 acquisition LIFO 释放对象，再清理该 Fiber 的 Rust sessions。失败的普通 inverse 保留旧对象与 Rust 实例；对象释放失败保留它及更早取得的对象。provider 等待消费者完成，这使 nested effect 与 cleanup retry 能使用原代 handle。对象释放是独立晚阶段，不是与普通 inverse 交错的全局 LIFO。

`JsObject`/`JsCallback`/`JsStream` 都受取得它们的 Rust action 限制，clone 不延长 action。显式 `JsObject.close()` 在 pending method 时返回 `ObjectBusy`，显式 `JsStream.close()` 在 pending next 时返回 `StreamBusy`；框架 journal 仍等待真实方法回复，流取消仍先发 return 再 join。对象析构不会在方法尚未结束时执行。详见[调用、取消和清理合同](rust-node-plugins.md)。

## 证明与可信边界

[PublicationRegistry](../crates/cordis-kernel/src/publication.rs) 和 [ActionLedger](../crates/cordis-kernel/src/action_ledger.rs) 是 Cargo 与 Verus 编译的同一份代码。它们证明 visibility/lease/reclaim 及 action identity/exactly-once 的记录不变量；动态声明转交与初始预注册是显式 host extension，不能直接称作论文 Step。

[shared Driver](../crates/cordis-driver/src/shared.rs)、availability 版本协议、Rust/JS callback journal、配置/Loader 事务、N-API、Node/V8 与 I/O 仍具有各自未证边界。Rust Runtime 已共用控制 Driver，但 typed Rust 动态服务仍采用原来的 owner anchor/provider 节点表示；静态 `cordis::Plugin` 的 `get/provide/setup/cleanup` 已通过 [typed adapter](typed-rust-plugins.md) 接入同一 publication，动态 API 仍未迁移。新增 cordis-node::plugin SDK 则可通过显式 JSON 服务、双向 pull stream 和 opaque object/callback adapter，让用户编译的 Rust factory 与 JS 插件共享同一图；见 [Rust/JS 插件指南](rust-node-plugins.md)。对象和回调由 factory 方法取得，方法参数与结果仍为 JSON，不是任意句柄混入 DTO 的通道。Rust/Node 公共 trace 测试保护已对齐的场景，不证明两种 backend 的所有 effect 时序相同。

MIT 上游 utils/service/events/logger 语言层保留版权和许可证；生产路径没有导入原版 Fiber scheduler。

## 可重现验收

```sh
python3 scripts/record-development.py --offline
python3 scripts/record-development.py --check
npm run test:types
npm run test:distribution
```

开发 gate 包括全内核证明、Rust 回归、Node runtime/Loader/Worker/types、三个 Rust crate 的独立解包测试与三个 npm 包的离线独立安装。npm 验收不上传包，只记录实际执行的 OS/arch/Node/ABI。`--check` 要求保留本地默认 addon、interop-fixture.node、build.json、npm report 和三个 tgz；仅从 Git 克隆旧报告不能当作本机成功验收。包仍为 private；manifest、严格产物选择与本地合包已有工具，多平台实际构建结果、发布和完整 release gate 仍是另外的门槛。

需要本地锁定上游源码的额外验收：

```sh
npm run test:compat          # 原版 Timer 与六组同源核心 fixture
npm run test:profiles        # 两个 profile 的四路同源差分
npm run test:harness         # 未修改的 Harness session/tool/scope 插件图
npm run test:upstream-core   # 12 个原文件、87 项核心行为测试
```

报告分别在 `target/node-compat/`、`target/upstream-core/` 和 `target/release-artifacts/npm/`。它们绑定上游 commit/tree、实际输入和构建；输入变更、执行失败或差异不会被旧报告掩盖。完整核心 runner 严格返回已知差异的失败状态，不跳过或改写上游断言。默认 CI 不依赖上游研究缓存。

性能测量单独使用[基准工具](benchmarks.md)。它记录实际源码、二进制、环境与原始批次采样，并明确区分测量失败和基线退化；行为测试、证明或工具单元测试不能替代性能实测与平台预算验收。

## 长期方案的剩余门槛

| 阶段 | 当前交付 | 仍需完成 |
| --- | --- | --- |
| M0 | 两个政策清单、完整 core runner、同源 profile runner | 全部 deep imports、公开类型与完整微任务合同 |
| M1 | Rust/Node 公共控制、真实 verified action ledger、跨 backend trace | 全部宿主调用到论文步骤的 refinement |
| M2 | publication/lease、跨 owner 转交、check 版本协议、reserve/seal | availability 与宿主对象表的形式连接、动态接口的整条论文投影 |
| M3 | Native host、错误隔离、owned task、Worker 正常/异常关闭 | 全 environment teardown/引用管理证明与长期驻留成本验收 |
| M4 | Logger、Service.check、方法 Inject、两个 profile 和类型样例 | 未覆盖公开合同、已知行为差异的应用迁移验证 |
| M5 | 增量 JSON Loader、Include/group、稳定 Fiber、事务恢复、Worker 制品重启 | 原版 Loader API/配置持久化、完整包管理器安装图 |
| M6 | Harness 真实插件图差分；同图 Rust factory/JSON、双向背压流及显式 object/callback；真实旧 Plugin 静态 typed adapter；factory revision adapter | typed Runtime 动态能力迁移、更多跨语言接口与 ABI 合同、更广生态图、模块依赖图 HMR |
| M7 | 三个 Rust 制品、三个 npm 包的本机独立安装 gate；原生 manifest/哈希/平台选择与离线合包；源码绑定的性能测量工具 | 各预编译平台实际验收、实测基线与长期运行/性能预算、完整负控与 release acceptance |

论文 ledger 的已反驳命题和开放义务保持不变。当前不能宣称长期方案、完整 Cordis/Harness 兼容或整篇论文 refinement 已完成。
