# 配置树、Schema、Include 与 Rust HMR

`cordis::config` 与 `cordis::loader` 是可运行的普通 Rust 宿主层。生命周期的退休、依赖守卫和 fresh identity 使用 Verus 内核；JSON 解析、schema、factory、文件 I/O、回滚与任意插件代码没有因此获得形式证明。

运行 `cargo run -p cordis --example config_reload` 可看到 Include 文件加载、服务隔离、依赖绑定、配置热更新、消费者先释放旧服务、group 禁用及等待完整清理。

`cordis_kernel::configuration_entry::Entry` 单独形式化论文 Definition 81 的六字段，
其构造、开关和配置编辑有 Verus 契约。`loader::Entry::as_paper_entry(resolve_url)`
提供具名插件叶节点的借用投影：调用方必须显式把 factory name 解析到 URL；group、
include、含 children 的条目或解析失败返回 `None`。投影保留原始 config、注解和
本条目自身的 `disabled = !enabled`，不混入父级有效状态或 schema/intercept 结果。
这不是整个 loader 的行为 refinement，也不会解析或加载该 URL。

## 配置与注册

`FactoryRegistry::register(name, schema, factory)` 注册 Rust factory。factory 接收已验证并应用默认值的 `serde_json::Value` 和 `ConfigScope`，返回一个 `Plugin`。再次注册同名 factory 会产生新的 revision；`Loader::reload()` 重建受影响的配置节点。旧节点保留原 factory 的 `Arc`，所以新版本 setup 失败时可以恢复旧版本。

factory 必须只构造插件，不应在 factory 中登记外部资源。资源获取放进插件 setup，并登记清理。一次有变化的配置更新会预先构造所有启用节点的候选插件，包括可能因依赖变更而被间接退休的子节点。配置完全不变时不调用 factory，也不重复 setup。

```json
{
  "entries": [
    {
      "id": "workspace",
      "isolate": ["model"],
      "metadata": { "tenant": "research" },
      "intercept": { "model": { "temperature": 0.2 } },
      "children": [
        { "id": "model", "name": "model", "config": { "name": "v4" } },
        { "id": "agent", "name": "agent", "inject": ["model"] }
      ]
    }
  ]
}
```

根节点可以是上述对象，也可以直接是 entries 数组。未知字段报错；`enabled` 默认为 true。没有 `name` 的节点是拥有实际 fiber 的 group，可以整体启用或禁用。子节点继承 enabled、metadata、interception、realm 与注入声明。`id` 在同一个父节点内唯一且不能包含 `/` 或 `:`；路径写作 `workspace/agent`。不同 group 可以有同名子节点。

`register_service("model", typed_key)` 将配置中的字符串映射到一个真实的 `ServiceKey<T>`。`inject` 建立实际依赖，缺失服务时节点保持 Inactive；服务出现后由 runtime 激活。它同时接受数组 `["model"]` 和对象 `{"model":{"capability":"chat"}}`：数组表示配置为 null 的必需依赖，对象值直接作为该服务的消费者配置，不另设 `required/config` 包装。子节点同名声明覆盖继承值；服务的 `provide_checked`/`publish_checked` 检查接收该值，factory 可通过 `scope.injection("model")` 读取。Rust builder 使用 `entry.inject.push("model".into())` 或 `entry.inject.insert("model", value)`。`isolate` 为该服务建立新 realm，子树继承。未变化的 group 会保留其 realm；被替换的隔离 group 获得新 realm。父子关系仍不等于服务依赖，显式注入与 runtime 的父依赖继承决定 committed bindings。

直接修改 `loader.tree().clone()` 后 `apply(tree).await` 可以增加、移动、删除或修改配置节点。节点移动到另一父路径会按新节点建立。`set_enabled(path, enabled).await` 是启用/禁用的便利入口。不同 mutation 通过 `&mut Loader` 串行化，单次操作内部的多个独立 cleanup 可以同时处于 Pending；完成返回前等待全部清理。

## 验证、配置拦截与类型化扩展

`Schema` 支持严格 object、required/optional/default 字段、数组、布尔、字符串、整数/数值范围、enum、nullable 与 Any。验证返回副本，默认值本身也经过验证，不修改输入。错误提供字段路径。整个目标树（包括禁用节点）必须通过 schema、ID、服务名和 factory 名检查，才会开始修改旧树。

`ConfigScope::intercept(plugin, patch)` 为一个插件名添加继承的配置覆盖。父 patch 与子 patch 按对象字段递归合并，子 patch 优先；最终 patch 覆盖节点配置，再进行 schema 验证。数组、标量和 null 整体替换，null 不代表删除字段。JSON 的 `intercept` 对当前节点和后代生效，节点 `config` 本身不会被当作所有后代的配置。

`ConfigScope::extend(value)` 使用 `TypeId` 保存 `Arc<T>` metadata，`metadata::<T>()` 取得最近的覆盖值；派生不会改写父 scope。`extend_json` 提供配置文件所需的字符串键 metadata。以 `Loader::with_runtime(runtime, scope, registry, parent)` 注入根 scope。工厂可以检查 scope 并将所需信息捕获进插件回调；运行时的服务访问仍通过 typed `Setup`/`AsyncSetup`。这些 Rust builder/类型接口替代 JS context decorator、动态反射属性与 Proxy，不执行 JavaScript。

## 更新与失败恢复

一次有效配置更新按以下顺序执行：

1. 检查整个目标树，解析继承、interception、schema 和 factory revision，预构造插件。
2. 配置之外的声明、factory、作用域或父子结构改变时，使用正常替换；仅 config 改变且仍 Active 的节点可以请求原地更新。
3. 仅退休需要替换或删除的旧节点，等待 cleanup 和 committed-dependent barrier，再以新 ID 挂载替代节点。
4. setup 达到 quiescence 后执行已经登记逆操作的原地更新计划；全部成功后原子安装以后重启所用的 setup recipe，提交配置快照和 revision。
5. 驱动新服务值或检查结果造成的依赖者状态变化，并重建因此退休的配置子节点。

插件通过 `Plugin::on_config_update(|setup, previous, next| ...)` 选择 `ConfigUpdate::Restart`，或者返回 `ConfigUpdate::Apply(ConfigUpdatePlan)`。`previous/next` 都是经过 schema/default/interception 处理的配置。默认没有 hook，仍执行正常替换。`ApplyReport::updated` 列出成功保留实例的原地更新节点；这些路径也属于 `changed`。

```rust,ignore
use cordis::config::{ConfigUpdate, ConfigUpdatePlan};

plugin.on_config_update(move |setup, previous, next| {
    let forward = setup.clone();
    Ok(ConfigUpdate::Apply(ConfigUpdatePlan::new(
        move || forward.set(settings_key, next),
        move || setup.set(settings_key, previous.clone()),
    )))
});
```

`ConfigUpdatePlan::new_async(apply, rollback)` 支持异步操作。**规划 hook 必须没有外部副作用**，因为 fallback 可能重新规划；实际修改放入 `apply`。逆操作在第一次 apply poll 之前登记，必须能够撤销部分执行、错误或 panic，并允许失败后的重试。Loader 不推断任意业务回调的可逆性；这些是插件作者的契约，不是 Verus 证明。正在运行的实例保留自己的 hook，新 factory 的 hook 只在下一次激活采用，避免连续原地更新误操作预构造的新实例状态。

如果同一批结构/factory/服务变化会通过 ownership 或 committed dependency 传递到候选节点，Loader 保守地改为正常替换。config 影响了 factory 生成的服务声明时也替换；不会在声明变化时强行保留 ID。执行前再次检查 activation generation，拒绝使用已经失效的更新计划。

提交前 setup、mount 或 apply 失败，会按逆序回滚已经开始的更新，再清理本次新建节点，并用捕获的旧 factory、配置和 scope 恢复上一个已提交树。未开始的 update 不执行 apply 或 rollback。已经退休的旧节点以新 ID 恢复；不受影响的节点保留 ID。`LoaderError::Apply { rollback: None, .. }` 表示恢复成功；`rollback: Some(error)` 表示恢复也失败、事务仍待恢复，之后可重试 `recover().await`。

提交前取消（drop）mutation 或 recover 的 future 只暂停驱动；pending transaction 保留旧快照、新建 ID、已经开始的 apply future 和逆操作。恢复先让已经开始的 forward future 落地，再执行逆操作，不会丢弃它的中途副作用。`recovery_pending()` 可检查状态；后续 mutation 先恢复旧配置。没有后台任务，无法保证一个永远 Pending 的插件操作完成。

**提交后传播失败使用不同结果：** `LoaderError::PostCommit { revision, cause }` 表示配置已经接受，但依赖者的生命周期传播失败，不能宣称配置已回滚。这时检查 `tree()/runtime()`，修复业务错误并继续驱动 `reload()` 或 runtime。提交后取消同样保留新配置；`recover()` 不会撤销已经提交的更新。文件来源的跟踪在此等待之前同步提交，因此取消 `load_json/load_file/dispose` 不会留下来源与已提交配置不一致的状态。传播引起的子节点修复有自己的可恢复事务；即使修复失败，已接受的配置仍是恢复目标。

配置不变的节点不会主动重新 setup；服务 provider 的变化仍可能触发其依赖者由 runtime 卸载/重新激活，这是依赖语义所要求的行为。仅持有一个外部 `Arc` 不延长 provider 的 lifecycle，也不能构成证明过的资源使用权限。

## Include 与文件热更新

`load_file(path).await` 读取 JSON。节点的 `include: "relative.json"` 以包含该节点的文件目录为基准，读取内容并追加为该节点的 children。路径先 canonicalize，活动来源栈检测循环；同一文件在不同 sibling group 被引用是允许的。深度超过 128 会报错。所有来源读取/解析与整个展开树的验证完成后，才修改运行时。

`watched_files()` 列出成功载入的所有来源。`poll_reload().await` 按文件内容重新读取配置树，同时检查 factory revisions；应用可用 timer 调用它，不需要专门的后台线程。内容等价、仅缩进变化或无关 factory 注册不会重启插件。非法 JSON、删除文件、schema 错误、include 环保持上个成功版本；修复文件后再次 poll 可以继续。单次读取会复用同一 canonical source 的内容，但多文件编辑并非文件系统原子事务。

`load_json()` 成功后切换为内存来源。`dispose().await` 停止全部 loader 节点并清除文件来源；此后 poll 不会复活旧配置。直接 `apply`/`set_enabled` 不回写文件；后续 file poll 以文件为准。JSON 文件的显式保存与三方合并见下一节。当前不执行上游 Include 的 YAML/JS 表达式，也不重现其内部 patch journal。

文件 HMR 指配置内容变化；代码 HMR 指调用 `register` 提供新的 Rust factory 再 `reload`/`poll_reload`。它不加载任意 `.rs`/`.so`，不重现 Node ESM/CJS 模块缓存、JS Proxy 或 npm 解析规则。编译后的 Rust plugin、可序列化配置和明确的生命周期边界是这一实现的对应接口。

## 显式保存、三方合并与文件故障

`Loader::save()` 同步保存上次成功 `load_file()` 之后已提交的内存配置。`apply`、`set_enabled` 和 `reload` 始终只修改运行时；文件写入必须显式调用保存。尚有待恢复的 runtime transaction 时保存返回 `RecoveryPending`，先完成 `recover().await`。`load_json` 和 `dispose` 会清除文件来源，因此之后不能保存到原文件。

需要审查输出时，先调用 `prepare_save()`，遍历 `plan.files()` 检查 `path()`、`json()`、`will_write()`、`requires_directory_sync()` 与 `includes_external_edits()`，再将 plan 交给 `commit_save(plan)`。planning 不写文件；准备期间读取、JSON/schema/factory/ID 验证或合并冲突都会在任何文件写入前失败。准备后配置、factory registry、保存 checkpoint 或磁盘内容/权限发生变化，会拒绝旧 plan。include 路径到 canonical 来源的映射在成功读取时固定，并在规划及每个文件提交前复查，重定向不会把编辑悄悄写到另一个已加载来源。错误仅描述路径与原因，冲突不打印配置值。

保存保留原来的文件边界和 `include` 字段，展开的 included children 不会重复写回父文件。数组形式的根仍为数组，对象形式仍为对象。可以修改原有节点字段、删除节点以及在没有 include 歧义的位置增加子节点。同一 canonical 文件被多次 include 时，各实例必须产生相同的文件内容，否则报告拓扑冲突；不会挑选某一个实例覆盖其他实例。include 节点下未知来源的新 child、跨 inline/included 分界的重排、外部修改 include anchor 或把 include symlink 改指另一个 canonical 来源都需要先在目标源文件中明确修改并 `poll_reload()`。删除整个 include 节点只移除引用，不删除对应文件。

合并使用三个版本：本地最后成功读取/保存的配置值 `base`、当前已提交内存配置 `ours`、保存时磁盘值 `theirs`。节点按稳定 `id` 对齐，普通对象按字段递归合并；不同字段的编辑可以共存。同一字段的不同修改、删除与修改并发、双方不同的节点顺序变更报告 `Conflict`。普通配置数组作为整体合并，null 是实际值，不代表字段删除。节点增删与顺序合并采取保守规则，不猜测双方排序意图。已合并的完整展开树也会检查 schema、factory、服务名与 ID，再允许写入；保存不执行新的 factory/setup。

`SaveReport` 提供：

- `written`：已完成原子替换的文件；`unchanged`：确认无需写入的文件。
- `remaining`：commit 阶段尚未完成的文件，成功时为空；planning 失败还没有可提交计划，因此该列表为空。
- `merged_external`：保存结果包含内存配置以外的磁盘编辑。
- `durability_uncertain`：替换已发生，但目录同步失败，无法确认断电后的持久性。

保存**不会更新 runtime**。`merged_external` 非空时，文件与运行时可能不同；显式 `poll_reload().await` 才会尝试应用磁盘版本，setup 失败仍遵循普通 loader 回滚契约。每个成功文件单独推进本地保存 checkpoint，checkpoint 保存本地版本而非包含外部编辑的合并版本。因此即使尚未 reload，后续保存也不会把先前保留的外部字段误当作本地删除；发生部分失败后可以修复原因，再调用 `save()`。

文件按 canonical 路径排序逐个提交。每个文件使用同目录 `create_new` 临时文件（Unix 初始权限 0600），写入后复制原文件 mode、`sync_all`，再次检查磁盘内容/权限，然后 `rename` 替换并同步目录。无变化的文件保留原始字节与格式。源文件必须仍是普通文件且保持原 canonical 路径；删除、改成目录/symlink、父目录被 symlink 重定向、不可读或非法 JSON 都报错，不会被重新创建或覆盖。成功替换保留 mode，但不承诺保留 inode、owner、ACL、扩展属性和 hard link 关系；临时文件通过 RAII 尽力清理。

这是**每文件原子替换，不是多文件事务**。错误中的 `report` 是实际进度，已经替换的文件不会偷偷回滚。目录同步失败也返回错误，其文件同时列在 `written` 和 `durability_uncertain`。同一个 loader 会记录未确认持久性的文件；再次 `save()` 即使内容没有变化也会重试目录同步，成功后才清除状态。目前 Unix 支持目录持久性同步；其他平台若完成替换但不能确认目录持久性，会如实返回错误。进程崩溃可能留下 `.cordis-save-*.tmp`，启动时不会把它当作源文件，也不擅自删除其他进程的临时文件。

计划与提交时的重读可以发现已发生的编辑，但标准文件系统没有跨普通编辑器的 compare-and-swap；最后一次检查与 rename 之间仍有竞争窗口。需要多个写入者同时编辑时，由应用提供独占的编辑/保存协调；不要把这个接口视为对不合作外部进程的锁。网络文件系统还取决于其 rename/fsync 语义。文件 I/O、JSON merge 和任意 plugin callback 均属于测试覆盖的宿主层，不在 Verus 证明内。

运行 `cargo run -p cordis --example config_persistence` 演示本地修改、保留外部字段、显式保存和再加载。

## 上游与检查

对照固定快照的 `packages/loader/src/config/{entry,tree,group}.ts`、`packages/include/src/index.ts`、`packages/hmr/src/index.ts`、`packages/core/src/context.ts` 与 Harness `packages/core/scope/src/index.ts`。配置分组、作用域注入、quiescent disposal 与 factory 替换能够表达 Harness 风格组合，不表示重写了 Harness 应用。

`cargo test -p cordis --test config --test loader --test loader_update --test service_configuration --test persistence` 覆盖 schema/default、metadata/interception、realm/inject、最小变更、setup 回滚、旧 factory 恢复、恢复失败后重试、并发 cleanup 屏障、取消期间恢复、Include 环/重复来源/源文件错误、文件 reload、include 拓扑保存、并发编辑冲突、部分提交重试、旧计划拒绝、权限与临时文件处理。正式验证及其他 runtime 检查通过项目根目录的 `./scripts/check.sh` 运行。
