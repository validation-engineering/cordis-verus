# Rust 原生应用 API

[English](rust-api.md)

**`cordis-verus 0.2.0`** 提供 typed 依赖输入、可选应用驱动和结构化回调错误。
执行 Rust 应用不需要安装 Node.js 或 Verus。

通过 `cargo add cordis-verus@0.2.0 --rename cordis --features tokio` 添加依赖。
`tokio` feature 为可选项；默认 features 已包含 typed 依赖和结构化错误。
在源码目录运行完整示例：

```sh
cargo run -p cordis-verus --features tokio --example managed_app
```

## 配置更新（未发布）

`ConfigUpdatePlan` API 保持不变；其真实正向／逆向 Future 现在由受验证 owner 持有。
Loader 跨取消保留实际计划，重试失败回滚，并只在更新完成后接受新版本。
更新目标包含运行域、激活代次和配方版本。插件仍须撤销部分执行并支持失败回滚重试。
详见[保证与证明边界](r2-configuration-execution.zh-CN.md)。

## Loader 运行时操作（未发布）

`loader.runtime()` 提供只读访问，`loader.runtime_mut()` 返回 `RuntimeAccess`，
保留运行时的可变操作和只读 `Deref`。它维持 Loader 与配置、源 Journal 的关联，
不再允许通过 `&mut Runtime` 替换整个宿主。

```rust,ignore
loader.runtime_mut().restart(id)?;
let pending = loader.runtime_mut().settle();
pending.await?;
let checkpoint = loader.execution_snapshot();
```

`settle`、`join`、`replace`、`shutdown` 消耗操作视图，使 Future 可以比临时视图
存活更久，并继续借用 Loader。原有直接操作调用仍可使用。要求 `&mut Runtime` 的
辅助函数需要改用独立持有的 Runtime 或 `RuntimeAccess` 参数。需要长期保留只读引用时，
使用 `loader.runtime()`，避免借用临时操作视图。快照包含原生／配置／
源的证明证据，历史会被擦除，不是可序列化审计日志。详见
[归属合同](r2-configuration-execution.zh-CN.md#loader-运行时归属与联合观察)。

## 混合原生函数体（尚未发布）

`Plugin::native_function(name, instructions)?` 存储有限函数体，支持
`ManagedInstruction::scalar(key, operation, branch)` 和
`ManagedInstruction::replace(key, value, branch)`。
带类型的构造器保持 Rust 键和值的类型对应。构造器自动声明全部引用服务，包括未选中的分支，
无需再手写这些键的 `.requires(...)`。两个分支都只能向后跳转或用 `None` 结束；
替换选择 `matched`，标量比较使用真实结果选择分支。

通过 `runtime.mount(...)` 加载；作为 Child 则使用 `setup.mount(...)`。
真实 root 准入、安装配方版本、效果参数、返回和成功前缀清理都连接到受验证解释器。
冲突 inverse 会阻塞并保留依赖，直到已有清理重试协议成功完成。

在当前源码目录运行 `cargo run -p cordis-verus --example managed_function --offline`
可复现完整冲突／恢复示例。[双语案例及证明审查路径](cases/managed-functions.zh-CN.md)
说明有限函数体、共享别名、跨 Journal 历史和回调边界。
不需要 Node 运行时；静态宿主会拒绝该原生函数体。

## 存储的多服务 root／Child 程序体（尚未发布）

`Plugin::native_service_program(name, instructions)?` 将完整有限程序体直接存入原生注册表，
从全部指令生成依赖。输入为 `Vec<ServiceInstruction>`，指令格式与下文一致。
通过 `runtime.mount(...)` 挂载 root，或通过 `setup.mount(...)` 挂载 Child。
注册时解析 realm，每条操作捕获当时的服务槽；程序体失败仍保留真实成功前缀的 inverse。
静态宿主会明确拒绝这个仅适用于原生运行时的程序体。

动态别名、跨 Journal 身份、严格恢复及证明边界见[函数到代码的审查路径](r2-function-semantics.zh-CN.md)。

## 跨服务的有限调用

在原生 root、Child 或效果回调中使用 `setup.run_service_program(&instructions)`。
每条 `ServiceInstruction` 提供 `key`、`operation`、`branch`。例如：

```rust,ignore
setup.run_service_program(&[
    ServiceInstruction { key: left, operation: ValueOperation::Add(2),
        branch: ValueBranch { matched: Some(1), unmatched: Some(1) } },
    ServiceInstruction { key: right, operation: ValueOperation::Add(3),
        branch: ValueBranch { matched: None, unmatched: None } },
])?;
```

所有引用键都须通过 `.requires(key)` 或 `.provides(key)` 声明，包括未选择的
分支。continuation 只能向后续的有效指令跳转。准入失败不执行写入；执行失败会
保留之前的 inverse，交给所有者的正常清理流程。每次调用捕获当前槽位，支持别名
和槽位替换；其他调用可在指令间交错，因此不是多对象事务。该 API 需要原生宿主，
有限步骤的证明不会自动覆盖外围任意回调或 Future。

## 一次声明依赖

```rust
use cordis::{Plugin, ServiceKey};

let greeting = ServiceKey::<String>::of();
let consumer = Plugin::with_dependencies("consumer", (greeting,))
    .setup(|ctx, (greeting,)| {
        println!("{greeting}");
        ctx.on_cleanup(|| Ok(()));
        Ok(())
    });
```

同一份描述生成运行准入条件和 setup 的 `Arc<T>` 参数。`setup_async` 接受异步闭包。
支持单个 key、`()`、最多八项的元组及嵌套元组。参数类型或元组形状错误不能编译；
缺少 provider 时仍需在运行时等待。

`key.with_config(json)` 为 provider 的可用性谓词提供输入。重复 key 共享一条 committed
绑定；同一 key 的多份显式配置必须一致，否则在注册或更新前拒绝。没有配置的重复项
共享这个 key 的显式配置（如果存在）。这里实现的是必需依赖；带独立重载规则的可选观察
不属于这套接口。

| key 构造方式 | 身份 |
| --- | --- |
| `ServiceKey::<T>::of()` | 按 Rust 类型共享 |
| `ServiceKey::<T>::named("name")` | 按类型和名称共享 |
| `ServiceKey::<T>::new("label")` | 每次独立；label 仅用于诊断 |

共享身份限于同一个链接宿主，不是跨动态库或进程 ABI。`Context::isolate` 和 `share`
仍决定 realm。`Dependencies` trait 是 sealed 的，第三方不能让声明与参数读取使用不同
的 key 集合。额外的手动读取仍由运行时检查。

## 运行应用

启用 Cargo feature `tokio` 后可使用 `App`。`App::new()` 要求当前位于 Tokio runtime 内；
`App::with_handle(&handle)` 可以显式提供 executor。一个任务独占并驱动原有 `Runtime`。
默认 crate features、typed builder 和手动 `Runtime` 仍不依赖具体 executor。

```rust
use cordis::{App, Plugin, ServiceKey};

async fn run() -> Result<(), Box<dyn std::error::Error>> {
    let app = App::new()?;
    let greeting = ServiceKey::<String>::of();
    let consumer = app.plugin(
        Plugin::with_dependencies("consumer", greeting)
            .setup(|_, text| { println!("{text}"); Ok(()) }),
    ).await?;
    let provider = app.plugin(Plugin::new("provider", move |ctx| {
        ctx.provide(greeting, "Hello, Cordis".to_owned())?;
        Ok(())
    }).provides(greeting)).await?;
    consumer.ready().await?;
    provider.update(move |ctx| {
        ctx.provide(greeting, "Updated greeting".to_owned())?;
        Ok(())
    }).await?;
    consumer.ready().await?;
    app.shutdown().await?;
    Ok(())
}
```

更新 provider 时，会先恢复受影响的 consumer episode，再释放旧 provider。consumer
随后可以用新的 committed provider 重新初始化；其清理过程仍读取旧绑定的值。
应用接口沿用现有生命周期协议，没有另建服务注册表或生命周期调度规则。

| 操作 | 完成条件／结果 |
| --- | --- |
| `app.plugin(plugin)` / `plugin_in(context, plugin)` | 完成注册，返回绑定到应用的句柄；不保证已 Active |
| `handle.settled()` | 当前初始化／恢复稳定，可能因缺少依赖而 Inactive |
| `handle.ready()` | 当前 episode 已 Active 且初始化稳定 |
| `handle.dispose()` | 退休、清理并完成 registry removal；保留型清理失败报错 |
| `handle.restart()` | 用已有定义重启并等待稳定 |
| `handle.update(...)` / `update_async(...)` | 替换 setup，保留服务声明并等待稳定 |
| `handle.update_plugin(plugin)` | 替换完整定义，包括 typed 输入和配置 hook；服务声明或注入配置变化在改动前被拒绝 |
| `handle.retry_cleanup()` | 显式重试保留的清理并等待稳定 |
| `handle.snapshot()` | 查询该插件；registry removal 后返回 `None` |
| `app.shutdown()` | 关闭准入，退休所有插件、清理并报告失败 |

`app.scoped(context)` 是同一应用使用不同默认 context 的视图。`handle.plugin(...)` /
`plugin_in(...)` 创建归属该插件的子插件；父插件退出时退休子插件，ownership 本身不授予
服务访问权限。`app.get(key)` / `get_in(context, key)` 读取外部快照，不取得依赖 lease。
所有作用域视图共享 shutdown 和准入状态。

方法调用时请求即入队；丢弃或超时只取消等待，不取消已提交操作。句柄等待当前状态，
并发更新可能合并，不是每次更新独立的版本事务；如需观察中间版本，应逐次等待更新。
缺少 provider 时 `ready()` 可以一直等待。callback 不应等待自身生命周期、整个应用
shutdown，或等待仍依靠该 callback 完成恢复的 provider 退出。推进还要求 Tokio 持续
运行且 callback 合作让出。停止 executor 前应显式等待 shutdown。

一次性清理失败会报告但继续排空；可重试清理失败保留资源，等待显式 retry。句柄报告
其等待期间自身的一次性清理错误，以及真正阻挡其完成的保留型清理失败；无关插件的失败
不会让该句柄失败。`app.cleanup_errors()` 检查自上次 shutdown 报告以来的全部历史清理
收据。shutdown 汇总并消费这些记录，包括句柄此前已报告的错误。报错不等于恢复成功。

## 可恢复的服务替换（未发布）

原生 root／Child 回调可以调用 `setup.replace_service(key, new_value)`，替换已声明
的非标量服务并自动保留逆操作。清理恢复原始载荷；后来的 managed 写入会阻塞恢复，
需要先恢复后来写入，再显式重试清理。恢复仍递增读取版本，旧可用性回复继续过期。
普通 `set` 冲突不保证可恢复。`ReversibleValue` 使用 `update_reversible`；静态存储和
任意内部可变状态不属于这个 API 的合同。
[证明与边界](r2-execution.zh-CN.md#可恢复的强类型载荷替换)。

## 可扩展可逆值（尚未发布）

当前源码为 `Setup` 和 `AsyncSetup` 增加 `update_reversible_with`，用于已声明的
`ReversibleValue` 服务。例如：

```rust
use cordis::{AsyncSetup, CallbackError, ReversibleValue, ScaleAdd, ServiceKey,
             ThenScalar, ValueOperation, ValueOutcome};

fn adjust(ctx: &AsyncSetup, key: ServiceKey<ReversibleValue>)
    -> Result<ValueOutcome, CallbackError>
{
    ctx.update_reversible_with(key, ThenScalar {
        first: ScaleAdd { scale: 2, offset: 1 },
        then: ValueOperation::Add(3),
    })
}
```

这里先计算 `2 * value + 4` 并检查溢出，再进行一次受管写入。`ThenScalar` 将前一
真实结果传给下一计算；`ChooseScalar` 根据 predicate 的实际 `matched` 标志选择
计算。受验证 owner 自动捕获并登记真实 inverse，既有清理路径执行恢复，或保留
干扰失败供显式重试。

计算在宿主和值锁外执行。提交时重新检查捕获的值／深度，以及 episode／group 是否
仍接受获取资源。状态变化就拒绝，显式重试会从新输入重新计算；完整恢复到捕获状态
则允许提交。被拒绝的外层调用不增加自己的受管写入或清理记录。计算 panic 转为
结构化 panic 错误；用户代码额外执行的副作用不会被隐式回滚。

原生路径在计算前由验证内核绑定声明与 owner，落地时再次检查 owner。计算期间的
槽替换影响后续调用；本次计算与 inverse 仍指向捕获对象，它可能继续通过另一别名
可见。不同服务名本身不表示独立性。精确论文映射见
[原生效果与别名](r2-execution.zh-CN.md#原生可扩展效果与别名感知的论文映射)。

新增原语可参照 [`ScaleAdd`](../crates/cordis-kernel/src/scalar_effect.rs)，实现并
验证 `ScalarEffect` 的模型／结果合同，无需扩展内核固定操作枚举或提供 inverse。
Verus 检查原语和泛型组合器；仅实现擦除后的 Rust trait 不会证明任意代码。
该 API 当前覆盖标量计算，不覆盖任意服务对象或外部 I/O。证明与剩余集成工作见
[R2 执行合同](r2-execution.zh-CN.md#可扩展标量效果与受管提交)。

## 保留错误原因

`CallbackResult` 现在是 `Result<(), CallbackError>`。`ctx.get(key)` 与
`ctx.require(key)` 都返回 `ServiceReadError`，使用 `?` 会将其保留到 setup、effect、
cleanup、`RuntimeError`、`ShutdownError` 和 `AppError`。

```rust
use cordis::{AppError, RuntimeError, ServiceReadFailure};

fn inspect(error: &AppError) {
    if let AppError::Runtime(RuntimeError::Setup { plugin, error }) = error {
        if let Some(read) = error.service_read() {
            assert_eq!(*plugin, read.plugin);
            if read.reason == ServiceReadFailure::Undeclared {
                eprintln!("{} was not declared at {}", read.service, read.location);
            }
        }
    }
}
```

读取错误包含失败分类、key/realm、服务与 Rust 类型、owner、episode generation、已知的
committed provider 和调用位置。分类为 `Undeclared`、`ClosedEpisode`、`MissingValue`、
`TypeMismatch`。

`CallbackError::kind()` 区分文本错误、服务读取、panic、合作取消、外部错误和多项失败。
外部库错误通过 `.map_err(CallbackError::new)?` 保留；通过标准 `Error::source()` 和
`downcast_ref` 检查原始类型。字符串错误用 `.into()`。effect join 发生多项失败时，
`errors()` 逐项保留原因。配置更新／回滚也通过 `LoaderError::Update` 保留原因，
恢复错误聚合仍保留 source 链。

错误是可克隆的收据：内置错误按值比较，不透明的外部原因按对象身份比较。
`failure()` / `cleanup_failure()` 保留文本视图；Runtime 的 `setup_error()` /
`cleanup_error()` 返回结构化原因。Node 与进程协议边界仍传输错误文本，Rust 错误类型
不会跨这些协议序列化。应用代码显式转成字符串也会丢失原因。

## 从 0.1 迁移

- `CallbackResult` 改为使用 `CallbackError`。将 `Err(String)` 改为
  `Err(message.into())`；已有的 `Result<(), String>` 可使用 `.map_err(Into::into)`。
  若需保留外部库错误的类型和 source 链，使用 `.map_err(CallbackError::new)`。
- `Setup::get` / `AsyncSetup::get` 现在返回 `ServiceReadError`。回调中优先使用 `?`；
  只在明确的文本边界调用 `.to_string()`。
- 匹配 `RuntimeError::Setup { plugin, error }`、`RuntimeError::Cleanup { plugin,
  error }` 与 `LoaderError::Update { entry, error }`；原 `message` 字段替换为结构化原因。
  配置更新和回滚回调也使用 `CallbackResult`。
- 原有 `Runtime`、`Plugin::new`、`.requires()` 和独立身份的 `ServiceKey::new` 仍可使用。
  需要共享 key 身份时显式选择 `of()` / `named()`；使用 `App` 时才需启用 `tokio` feature。

## 与已验证内核的对应关系

| API 步骤 | 现有实现路径 |
| --- | --- |
| 依赖描述 | `typed::Dependencies::declare` → Plugin 声明 → Context 端口 → 生命周期准入 |
| typed setup 参数 | `Dependencies::resolve` → `AsyncSetup::require` → 当前 episode 的 committed 绑定 |
| App／句柄操作 | 单一驱动任务 → 原 Runtime mutation／poll → 共享生命周期 driver 和内核 |
| 清理失败／重试 | 原 cleanup journal 与恢复收据；保留错误源不改变其恢复结果 |

这些适配接口没有获得新的生命周期权限。Verus 证明内核合同；编译失败测试及生命周期／
错误回归测试检查普通 Rust adapter。这不代表已证明 typed builder、Tokio 公平性、任意
插件代码、最终完成清理或外部持有的 `Arc` 的生命周期。参见[语义边界](semantics.md)、
[采纳计划](adoption-plan.zh-CN.md)，以及 `typed_dependencies`、`app`、`structured_errors`
集成测试。

## 可暂停的值程序（尚未发布）

`start_value_program(key, program)` 创建绑定当前 episode/group 和实际捕获对象的
`ValueProgramCursor`。每次 `advance_value_program` 执行一条实际指令：
`Ok(Some(outcome))` 表示完成一步，`Ok(None)` 表示程序结束；算术错误保留当前
指令，可显式重试。两次调用之间允许其他插件写入，下一条指令读取当时的真实值。
每个成功步骤的逆操作已经由运行时保留；丢弃游标不会撤销程序，也不会丢弃清理条目。

游标提供位置及最近观察，但不能修改代码、目标或 continuation。其他 episode/group
和已关闭的 owner 无法推进。`cursor.observe()` 刷新包括清理及重试的检查点；
快照只是一次观察，不保证之后的并发读取仍相同。需要原子执行有限程序时，已有的
`run_value_program` 会在整个运行期间持有值锁。两个 API 均可用于 `Setup` 和
`AsyncSetup`。

参见 [Child/交错写入/重试案例](../crates/cordis/examples/interleaved_program.rs) 和
[槽位／对象证明边界](r2-execution.zh-CN.md)。

`capture_reversible(key)` 返回已提交 provider、端口及带 `revision()` 和实际
`Arc<ReversibleValue>` 的捕获。`cursor.binding()` 保留启动程序时的选择。
`set` 和 `ServiceHandle::set` 替换实时槽位：之后的读取选择新对象，已存在的
游标及清理逆操作继续使用旧对象；另一个共享旧对象的端口也继续观察其写入
和恢复。捕获不代表生命周期租约或额外写权限，`refresh()` 返回新的选择，
不会改写旧捕获。捕获会持有槽位及原对象的引用，直到自身被丢弃。
对象／槽位的证明身份及历史编译后擦除，版本则是真实且
不回绕的运行时计数器，记录槽位替换，不记录所选对象内部的写入。

## 原生有限 root 与执行域（尚未发布）

使用 `runtime.reversible_value(10)` 在原生生命周期的执行域中创建受验证对象，
再通过现有 `provide` API 发布。`Plugin::native_value_program("adjust", key, program)`
将校验过的 `ValueProgram` 装成原生 root，可用 `Runtime::mount` 挂载，也可用
`Setup::mount` 装为 Child，声明依赖会自动添加。每条成功指令登记其真实逆操作；
后续失败保留成功前缀，由现有清理协议恢复。有限函数体直接保存于受验证注册表，
按实际登记依赖的 realm 和当前注册版本运行，root 完成由真实结果决定。
`update_plugin` 先恢复旧 episode，再运行新函数体。证明将每条有限指令对应到域轨迹中的位置。

`value.observe_execution()` 返回实际值与对应的联合证据；
`runtime.plugin_execution_snapshot(id)` 在同一次 Journal 读取区间观察该原生 episode
的 work、存活清理组与 publication 归属；Begin 前或 Unload 后返回 `None`。
宿主读取时持有既有 episode mutex。证明字段会被擦除，不会使旧服务值继续存活。

`binding.capture().execution_snapshot()` 保留准确的捕获版本与对象提交，槽替换后仍有效。
Begin 捕获共享槽引用，此后的读取可以看到新版本。两个 runtime 快照入口会在共同读锁前
收集真实 publication、imports 与 owned 槽凭据，不调用用户代码，也不保留载荷。
检查点的证明投影覆盖每个实际服务键：本域可逆槽解析到当前对象状态，不透明载荷、
外域槽与外域对象则保留明确类别。凭据收集与 Journal 读取之间发生替换时，投影仍
保持一致。保留捕获的旧本域对象在替换后仍可解析，当前槽选择和旧对象清理互不混淆。
这不表示随后发生的运行时读取与检查点原子执行。参见
[引用合同](r2-execution.zh-CN.md#本域对象引用与实际服务观察)。

`effect_handle.execution_snapshot()` 和 `service_handle.execution_snapshot()`
核对所属域中的真实取消／初始化／完成状态和错误记账。effect 完成来自受验证 runner
退休，服务完成则是具名宿主报告。服务终止错误可以让 `join()` 返回错误，同时
`finished()` 仍为 false。普通宿主关联与调度边界见
[共享状态合同](r2-execution.zh-CN.md#真实共享句柄状态接入执行轨迹)。原生效果轮询会核对
句柄的 Begin／work 来源与准确共享 Episode 分配。`restart(id)` 保留清理失败，成功
显式 `retry_cleanup(id)` 才清除此失败；成功 Unload 清除 restart，再进入下一次 Begin。
插件执行快照也包含真实失败／重启控制。参见
[Episode／控制合同](r2-execution.zh-CN.md#episode-归属与真实轮询控制)。

克隆的 `AsyncSetup` 与嵌套效果现在通过同一所有者共享不可变上下文和可变 Episode。
原生身份、声明及已提交 provider 来自内核的 Begin 上下文，效果准入由内核读取绑定。
元数据不含服务载荷，保留它不会延迟槽位释放；静态嵌入仍承担明确的宿主绑定合同。
原生 realm 表与 anchor 也来自同一登记 Begin；受验证回调 scope 标识实际存活队列，
并进入生产插件检查点。过期或异属 scope 无法通过 `AsyncSetup` 登记资源；Context
克隆共享不可变 realm 表。参见[上下文／scope 对应关系](r2-execution.zh-CN.md#注册-realm-与回调作用域)。


`runtime.execution_snapshot()` 观察生命周期所在域。历史会被擦除，它们是证明
检查点，不是可序列化的运行时审计日志。独立 `ReversibleValue::new` 仍使用独立域，
跨域替换保持为明确的外部引用。新构造器面向原生运行时。
参见[范围及剩余边界](r2-execution.zh-CN.md#同一原生执行域的统一轨迹)与
[可运行案例](../crates/cordis/examples/interleaved_program.rs)。

内核集成入口 `Execution::observe_execution()` 为原生 Begin 创建的执行返回
`Some(snapshot)`，独立／静态未连接的所有者返回 `None`。它在同一次读锁内核对
实际 work 与全部存活清理队列。`observe_execution_after(&earlier)` 还保留此前同域
程序／值历史。证明检查点涵盖真实票据、待完成阶段、失败清理和槽位占用；任意回调
语义及完整宿主状态仍在投影之外。

### 声明标量的读取与写入

`Setup` 和 `AsyncSetup` 提供 `observe_reversible(key)`，返回受验证的标量快照。
原生 `update_reversible` 与 `run_value_program` 在受验证 Execution 内解析真实
Begin 绑定。普通 root／Child 回调和效果组共用此路径，成功返回前将 inverse 登记到
调用者实际的清理组。原有 API 与静态宿主策略仍可使用。

```rust,ignore
let before = setup.observe_reversible(counter)?.value();
let change = setup.update_reversible(counter, ValueOperation::Add(1))?;
// change.before 是这次受守卫写入的真实输入；此前快照之后可能发生其他写入。
let after = setup.observe_reversible(counter)?.value();
```

互为别名的服务名观察同一对象。替换一个槽位可以分开这些别名，先前的 inverse
仍恢复旧对象。帧证明使用对象分配身份；更强的端口帧条件明确需要别名闭包前提。
这些受管调用没有证明外围回调体。`update_reversible_with` 仍使用既有的无锁用户
计算／受验证落地合同。见[声明调用合同](r2-execution.zh-CN.md#声明访问与生产函数步骤)。
