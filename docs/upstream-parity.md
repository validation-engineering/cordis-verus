# Cordis 与 DeepSeek Harness 功能对照

本项目以 Rust 重现 Cordis 的生命周期、依赖和效果组合接口，DeepSeek Harness 提供真实使用场景。它不直接运行 TypeScript 插件，也不重写 Harness 的 UI、AgentLoop 业务、模型 API、持久化、权限或工具执行。论文安全语义用于约束恢复顺序；上游运行结果和 Rust 行为测试不能代替证明。[upstream.lock.json](../upstream.lock.json) 记录官方源码快照。

| 官方仓库 | 锁定 revision | 用途 |
| --- | --- | --- |
| [cordiverse/cordis](https://github.com/cordiverse/cordis) | `f8ea3cd50f1a5724e8e715995bcde131c9c12b2c` | 公共 API、fiber、service、effect、loader/HMR 对照 |
| [deepseek-ai/deepseek-harness](https://github.com/deepseek-ai/deepseek-harness) | `da00f7f5358f2949383b35c14f548bc20187d80c` | vendored Cordis 及 AgentLoop、Scope、LLM 等组合方式 |
| [cordiverse/paper](https://github.com/cordiverse/paper) | `0d43a6f18004a7b5bf9662c31aa08c3712d232ec` | 论文官方入口；正式语义固定到 arXiv v1 |

## 实现与证明覆盖

Verus 内核的 `wf` 包含 registry 结构、provision 唯一性、live binding 与声明的一致性、已安装组件所需依赖的完整 coverage，以及 provider 存活和清理守卫。live dependency chain 的 commitment 位置严格递减，从而排除已安装依赖环；resolve/target、begin/finish 与后续 lifecycle 转移具有相应契约。这里的 binding 类型一致性指 key/realm 的 require/provide 声明匹配，Rust payload 的具体 `T` 和 Arc 存储仍在宿主层。

`EffectStack` 证明 token 的精确 LIFO；`resources::Store` 提供具体可执行的 forward/inverse 和独立更新证明；`calculus` 条件证明有限效果序列的观测恢复、独立干扰与恢复的交换，以及独立组的交换。这些结果各有明确前提，不表示所有普通 Rust closure、future、文件或网络操作已经被证明可逆。验证和测试数量以当前检查报告为准。

| Cordis 能力 | Rust 侧实装 | 验证与边界 |
| --- | --- | --- |
| component 与父子 fiber 树 | Runtime::mount，Setup/AsyncSetup::mount/mount_in，ChildHandle，子树退休/删除 | 内核证明 parent 结构与删除守卫；请求队列和 callback 属于宿主 |
| 组件创建的 inverse | 在创建所属 effect 组中登记 child retirement | 对应 Def. 52：inverse 只请求 retire，不等待 child；父 remove 仍等待子节点消失 |
| required injection | requires + 固定 `(key, realm)` dependencies，自动 target/committed | 缺失依赖不开始 activation；installed coverage 与声明一致性进入 wf |
| 父依赖继承 | 子节点继承父实际 ports 与子 context 对应 realm 的 ports，排除自身 provisions | 宿主扩展为真实 kernel dependencies；parent 字段本身不添加服务依赖 |
| service provider | provides/provide，Active 后才参与新解析 | 唯一 provision 是已证明不变量；Loading payload 不提前发布由宿主保证 |
| provider identity | committed 保存具体 provider ID，贯穿 setup 与 cleanup | 内核；相同 payload 不能掩盖 provider revision |
| 四态与 reactive reload | Inactive、Loading、Active、Unloading；target 变化驱动撤回/恢复 | Loading 对应上游 Reloading；允许 Active 与 target 暂时不一致 |
| 异步 Service.init | Plugin::new_async，owned AsyncSetup，跨 await 初始化 | 行为测试；在途 setup 先完成可收集 inverse 的边界，再恢复 |
| effect iterator | Effect::step、EffectIterator、Inverse、EffectHandle | stage 前检查依赖；组内 LIFO，独立组可以并发恢复；调度和任意回调未证明 |
| effect cancel/join | handle cancel/dispose、initialized/finished/errors/join | 幂等取消；当前 stage 落地、后续 stage 停止；join 需要 runtime 持续驱动 |
| teardown barrier | provider 等仍 committed 的消费者，保留退休节点到完成清理 | 内核安全守卫 + 普通 Rust async 驱动；不保证任意 future 终止 |
| 失败与 panic | setup/stage 失败锁存并回滚，cleanup 错误/panic 记录后继续 | 宿主测试；未登记或不正确的 inverse 不会自动得到修复 |
| quiescence | Runtime::settle、目标化 Runtime::join，缺失依赖可保持 Inactive | join 驱动目标并避开无关 Pending；没有后台 executor 或全局 liveness 证明 |
| isolation 与 sharing | Context::isolate/share，固定 realm ports | 内核按 key/realm 区分；修改接口/realm 采用 fresh revision |
| typed service access/update | Setup/AsyncSetup::get/provide/set，Runtime::set，owner_context | Rust typed key/payload；外部 Arc 不形成 lifecycle consumer，旧 handle 不可写新 episode |
| plugin revision | Runtime::replace；Loader 差分配置/factory revision | 退休、清理、删除后 fresh ID；restart/update/update_async 保留 ID，属于宿主扩展 |
| 同步/异步事件 | Event/AsyncEvent，on/once/prepend/off，emit/bail/parallel/serial | 注册快照、once 原子 claim；parallel 等全部结果并汇总错误，serial 遇 Some/error 停止 |
| waterfall 与 scope filter | Waterfall/AsyncWaterfall，around next，EventScope 与 filtered predicates | next 最多一次，支持前后处理/短路；回调正确性及进行中 dispatch 不受 kernel 自动 drain 保护 |
| schema/context interception | Schema、ConfigScope::intercept/extend/extend_json | 默认值和严格字段校验；继承 patch 与 typed metadata 替代动态反射 |
| Loader/Group/Include | ConfigTree、Entry、FactoryRegistry、JSON 文件、group 启停、递归 Include | 全树预检、最小重建、include cycle 检查；取消与失败有显式 recover 协议 |
| 配置/代码 HMR | poll_reload 检查文件内容，register + reload 替换 Rust factory | 未变化节点不重启；旧 factory 快照支持回滚；不装载 JS/共享库或操作 Node cache |
| timer | timeout/interval/sleep/ticks/debounce/throttle，真实/手动 clock，owner bind | 普通 Rust worker 与取消/join；同 service callback 内 shutdown 只取消，外部 join 才是完成屏障 |
| 维护与诊断 | 稳定回收失效 binding/删除声明、snapshot JSON/DOT、shutdown 错误汇总 | 回收 primitive 经过 Verus；diagnostic/driver 是普通 Rust；identity tombstone 保留 |
| 具体 reversible resource | ReversibleStore、owner transaction、write/rollback、Setup::reversible | 实际调用已证明的 Store；Mutex/journal/owner 编排仍为宿主测试 |
| 观测恢复与独立性 | calculus 的 sequence recovery、interference recovery、independent groups | 条件定理；需要每一步 inverse witness、观测等价及交换前提，不是任意 plugin 的自动证明 |

使用方式与完整取消/错误边界见 [runtime.md](runtime.md) 和 [loader.md](loader.md)。

## Rust 接口选择及尚未覆盖的上游特性

Rust 类型和显式资源所有权构成这一版本的应用接口。`ServiceKey<T>`、Plugin builder、ConfigScope、EffectIterator、typed event 和 factory registry 分别承担动态 service、decorator、context 扩展、JS iterator、动态事件和 module import 的对应职责。JS Proxy/shadow、对象属性 reflection、npm/ESM/CJS 解析与模块缓存不在执行环境中；现有 TypeScript plugin 需要按这些接口迁移。

Include 支持 JSON 与显式 ID、继承 scope、递归来源和内容 polling。YAML/JS 表达式、匿名 ID 自动回写、上游 YAML/JS patch journal 不兼容；Rust JSON 已提供显式保存计划、按 ID/字段三方合并、Include 拓扑保留和部分失败重试。程序内 apply/set_enabled 默认只修改内存配置，显式 save 才写文件；保存不自动将外部合并内容应用到 runtime，后续 file polling 以文件内容为准。group 的 enabled=false 会禁用整个拥有的子树，这个明确的 Rust 接口不复刻上游内部 group marker 始终 enabled 的表达方式。

服务 payload 使用 Arc 快照与显式可变状态，不复刻 JS 同一对象的任意属性修改。事件的 off/dispose 只影响未来快照：已经捕获的普通 listener/future 可以继续，owner cleanup 不自动等待它们。普通 subscription 仍需应用自行协调；显式 on_owned/on_in 在实际调用前获取 admission，owner cleanup 等待已启动 handler、capture/future 析构与 continuation lease drain。它通过普通 Rust 测试保障协议，不把任意 callback 变成已证明的 kernel consumer。

Timer 提供自己的 std worker，不是 Node event loop 或 Tokio 全 API 兼容层。callback 内停止自己的 service 不等待其他 callback，避免互相 join；从 callback 外调用 shutdown/cancel_and_join 才提供结束屏障。异步执行、线程锁、调度公平性和任意外部 I/O 都不在当前形式证明的直接范围中。

## 上游阅读路径

Cordis 核心入口为 `upstream/cordis/packages/core/src/index.ts`，主要实现位于 `fiber.ts`、`registry.ts`、`service.ts`、`context.ts` 和 `events.ts`。Loader/Group、Include 和 HMR 还分别读取 `packages/loader/src/config/{entry,tree,group}.ts`、`packages/include/src/index.ts`、`packages/hmr/src/index.ts`。独立 Cordis 与 Harness vendored 版本必须分开审阅，不能假定实现相同。

固定快照中，Cordis `packages/core/src/fiber.ts` 包含 disposal 与 unload/recovery；Harness `vendor/cordis/src/fiber.ts` 还包含对 Unloading fiber 登记新 effect 的拒绝及 setup 前 wrapper 登记等加固。它们用于定位 API 与回归场景；provider 恢复仍依据论文 guarded L-Unload，而不是简单复制任意上游调用次序。

## Harness 使用场景

下表描述 Cordis 层可以表达的组合，未声称移植或验证对应 Harness 业务模块。

| Harness 固定快照文件 | 实际使用 | 已有 Rust 表达方式 |
| --- | --- | --- |
| `packages/core/agent-loop/src/index.ts` | 多 required services、owner effect cleanup | 多 requires、整组 committed provider bindings、异步 setup 与 owner effects |
| `packages/llm/llm/src/index.ts` | 生命周期绑定的 adapter registry | effect stage 返回注销 inverse；应用选择 typed registry 数据结构 |
| `packages/core/scope/src/index.ts` | 子 fiber、context metadata、依赖继承和 quiescent disposal | mount/mount_in、ConfigScope typed metadata、真实继承 bindings、dispose + join/settle |
| `packages/core/agent/src/dispatch.ts` | scoped emit/serial/waterfall | typed sync/async events、predicates、around middleware；应用提供自身 scope ancestry 路由 |
| `packages/workspace/workspace/src/index.ts` | 异步 Service.init | Plugin::new_async、AsyncSetup、effect iterator 的阶段化初始化与清理 |

[async_lifecycle.rs](../crates/cordis/examples/async_lifecycle.rs) 组合异步 provider、消费者 effect stages 和动态子插件；[config_reload.rs](../crates/cordis/examples/config_reload.rs) 组合隔离 group、Include、依赖重绑定和配置修订。事件、timer、loader 与资源测试覆盖各自的边界，但它们不是对整个 Harness 应用的端到端兼容声明。

## 与论文对齐时保留的边界

1. Active 与当前 target 暂时不一致是合法状态，不额外要求旧 TLA+ checker 的全局 `Active ⇒ target=committed`。
2. 服务从新解析中撤下和实际 inverse 执行是两个时刻；消费者清理仍使用原 committed provider。
3. ownership、服务依赖、child retirement inverse 和 registry removal 分别建模。child inverse 不等待子树，并不允许跳过父 remove 的子节点守卫。
4. 配置 revision 使用 fresh fiber；保留 ID 的 restart/update 是附加宿主操作。修改 realm/声明需要重建。
5. 条件 effect calculus、具体资源证明、生命周期证明、Rust 行为测试和上游 API 对应分别报告。没有 inverse witness 的任意 callback 不因通过测试而成为可逆操作。
6. 已安装依赖图的无环不自动证明整个异步 runtime 的 termination、fairness 或全局 confluence。相应前提和剩余论文义务见 [semantics.md](semantics.md)。
