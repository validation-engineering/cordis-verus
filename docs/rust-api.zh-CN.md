# Rust 原生应用 API

[English](rust-api.md)

这些接口已在当前源码实现，**尚未包含在已发布的 `cordis-verus 0.1.0` 中**。
本轮完成 typed 依赖输入、可选应用驱动和结构化回调错误三部分。
执行 Rust 应用不需要安装 Node.js 或 Verus。

在源码目录运行完整示例：

```sh
cargo run -p cordis-verus --features tokio --example managed_app
```

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
