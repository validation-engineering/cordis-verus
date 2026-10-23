# 原生操作合同

[English](native-operation-contracts.md) · [剩余义务](paper-mapping-inventory.zh-CN.md) · [受控效果](r3-controlled-effects.zh-CN.md)

当前[封闭数据 Session](r01-prewrite-replay.zh-CN.md)已支持 scalar／typed 混合调用、真实清理后继续执行、动态槽位与封闭引用值。[provider／consumer／Child 更新交付](cases/update-recovery.zh-CN.md)为独立限定成果；R01 和完整资源边界仍开放。下文 batch 小节记录较早、范围较窄的接口，其限制不应当作新版 Session 的限制。

[受守卫重放](r01-prewrite-replay.zh-CN.md)现包含 `batch::run_exclusive`：标量 batch 持有真实对象／槽位锁，写入前检查来源输入与分配映射，通过原 root 解释器推出对应结果。typed 基本操作游标和动态选择证书仍是独立路径；这闭合了一条标量执行连接，不代表 R01 或完整资源边界关闭。

独立入口 `batch::run_exclusive_typed` 现跨目标调用序列持有真实 typed 对象锁。
它检查来源连续性、初始逆操作债务、目标零修订号，以及实际 Episode 选择的分配。
调用前的容量检查为完整存储函数保留足够修订号空间，包括未走到的分支。
随后由**同一个原解释器**在准入后推出 typed 写入成功，并记录实际的值／head／depth／revision
区间；不会把来源版本写入目标。逆操作进入原清理队列，释放保护区锁后由普通清理路径恢复。
typed inverse 在真实写入时保留分配身份，因此捕获重放输入不会再次获取已持有的锁。

typed batch 还会自动组合**完整调用之间的源／目标对应关系**。
每次调用前，`Tracker::prepare` 通过真实历史检查点确认保留的源输入，不要求 `T: Eq`，
也不重新读取活动源对象。随后从原解释器的实际报告推出程序位置、payload 身份与深度对应，
并为每个共享分配扩展单射 head 映射。`Batch::typed_replay_matches` 导出该关系及调用间
映射的连续性；`Certificate::inverse` 关联任意相关语义状态上的严格逆操作定义域。
映射和证书会擦除，真实历史检查点与清理 owner 仍保留运行时所有权。

该入口覆盖持锁的前向 typed 调用序列。混合 scalar／typed 受保护函数、序列内部恢复及
恢复后的受保护执行仍需组合；独立基本操作游标已有历史恢复支持。
标量与 typed 两个 batch 入口保留各自明确的支持范围。


本审查表把原生操作族对应到真实入口、状态观察和恢复责任，服务于固定清单中的
S01／S02／P01／P03、R01／R08 和 G02。它不关闭这些单元，也不改变原论文台账。
Node 协议的恢复仍由 R07 跟踪。

## 状态与观察

沿用 [R1](r1-semantics.zh-CN.md) 的 `finite-strict-context/v1` 解释。分配地址由实际
Journal 实例与分配键构成。服务端口是查找名称；多个端口可以指向同一对象。
替换端口绑定不会重定向已经捕获的对象。独立 Journal 的数字标签不产生共同顺序。

标量观察包括 `(值, 逆操作深度)`。类型化载荷观察保留 `Arc<T>` 身份、语义 head 和
逆操作深度；revision 是独立的防旧回复版本，恢复时也可能增加。保留的 `Arc<T>`
相等，不包含对 `T` 内部任意可变状态的证明。

生命周期状态还包含注册、父子关系、已提交 provider、当前 target、Episode／work
所有者、publication、pending 动作、清理槽、已发票据和失败／重启标志。
即使服务表不变，准入也可能依赖这些字段。S02 必须保留 R1 已建立的准入观察与
恢复观察的区别。

## 实际访问与恢复路径

每行将公开操作与其共用实现归为一族。单项合同是该操作的证据；跨行的完整组合仍需
证明。Ghost 来源历史和收据会从普通 Rust 产物中擦除。

| 操作族与实际代码 | 读取与修改 | 定义域和恢复责任 |
| --- | --- | --- |
| [分配与快照](../crates/cordis-kernel/src/reversible_value.rs)：`new_in`、`snapshot`；[类型化分配](../crates/cordis-kernel/src/shared_payload.rs)：`new_in`、`capture` | 在真实 Journal 分配对象；在对象锁内读取状态及对应历史。 | 新标量的逆操作深度为零。快照描述获取时刻，不冻结未来值。`new_in_following` 另返回晚于先前截面的真实出生收据。 |
| [标量操作](../crates/cordis-kernel/src/reversible_value.rs)：`apply`、`apply_pending_following` | 读取并修改选定对象的值／深度，产生真实逆操作和 Journal 条目。 | 检查算术与深度容量；逆操作只在捕获的 after-state 有定义。原始逆操作的持有者负责恢复或登记它。 |
| [受控托管标量](../crates/cordis-kernel/src/controlled_effect.rs)：`apply_controlled_effect`；[原生选择](../crates/cordis-kernel/src/native_effect.rs)：`apply_native_controlled` | 检查声明选择和执行所有者，在值锁内运行数据指令，将真实逆操作登记到该所有者的清理队列。 | 准入关闭时在写入前拒绝；其他失败遵循实际原语定义域。成功调用不会把逆操作记到虚构的对象或队列。 |
| [可扩展计算](../crates/cordis-kernel/src/scalar_effect.rs)：`prepare_effect`、`commit_calculation`；[原生落地](../crates/cordis-kernel/src/native_effect.rs)：`apply_native_effect` | 观察保留对象，执行 `ScalarEffect::compute`，再检查并提交捕获的输入。 | 已有返回值合同和干扰拒绝合同；trait 不禁止 `compute` 内额外共享写入。受控重放入口会拒绝这条路径。 |
| [类型化替换与逆操作](../crates/cordis-kernel/src/payload_inverse.rs)：`apply_captured_following`、`restore_following`；[原生捕获](../crates/cordis-kernel/src/native_payload.rs)：`capture_native_payload`、`land` | 保留选定载荷所有者，检查实际存活／版本／栈状态，替换值并记录真实逆操作。 | 明确检查旧捕获、retirement 和容量；恢复所需语义状态时，防旧回复 revision 可以递增。`T` 内部及析构需要独立边界合同。 |
| [槽位替换与别名](../crates/cordis-kernel/src/value_slot.rs)：`capture`、`replace`、`capture_binding` | 修改版本化槽位当前对象，已有 capture 保留此前对象。 | [别名投影](../crates/cordis-kernel/src/value_alias.rs)同时更新指向同一对象的全部名称。字面单端口语义需要明确的单绑定条件；不同端口名不能推出独立性。 |
| [发布](../crates/cordis-kernel/src/publication.rs)及[撤回](../crates/cordis-kernel/src/publication_cleanup.rs) | 修改所属 Episode 的服务发布与清理义务；consumer 保留已提交 provider。 | 需要组合发布、撤回、consumer 保留与真实载荷所有权。publication 消失不等于所有外部资源已释放。 |
| [root 解释](../crates/cordis-kernel/src/managed_root.rs)：`run_managed_root`；[函数执行](../crates/cordis-kernel/src/managed_function.rs)：`run_function` | 首个效果前解析全部声明端口，执行真实参数、按真实结果选分支，并登记成功前缀的逆操作。 | 检查有限存储函数及分支下标；受控准入也检查未访问的回调分支。任意回调效果仍不能被当作完整观察不变。 |
| [Child 所有权](../crates/cordis-kernel/src/lifecycle_state/registration/shared_child.rs)及[原生注册](../crates/cordis-kernel/src/lifecycle_state/native/runtime.rs)：`register_shared_child`、`retire_shared_child` | 修改出生／父子／注册记录及真实父所有者的清理义务。 | 注册准入有服务表之外的守卫。retirement、Child 终态和注册删除不同。R04 仍需组合 consumer 和重复 Episode 恢复。 |
| [清理与重试](../crates/cordis-kernel/src/cleanup_groups.rs)：`dispatch`、`complete`、`retry`；[原生清理](../crates/cordis-kernel/src/lifecycle_state/native/runtime.rs)：`begin_cleanup`、`retry_managed_execution` | 发出真实动作，保留被阻塞的逆操作，区分失败，并在推进前匹配当前票据。 | 可重试失败保留动作；已消耗的 `FnOnce` 失败合同不同。宿主成功确认是协议事实，不证明任意外部资源已恢复。 |
| [异步落地](../crates/cordis-kernel/src/cleanup_queue/landing.rs)及[轮询／重启控制](../crates/cordis-kernel/src/poll_control.rs) | 记录实际所有者、pending 结果、失败和重启状态，根据当前状态接收或转移结果。 | 旧所有者／票据检查是安全性条件。Future 最终完成及宿主调度属于独立的 G04 条件。 |
| [配置执行](../crates/cordis-kernel/src/lifecycle_state/native/runtime/configuration.rs)及[普通宿主适配器](../crates/cordis/src/runtime.rs) | 将配置／来源记录与真实宿主调用连接到验证内核。 | 复用 R2 生产映射；文件持久性、任意 factory 和外部效果保留明确合同；C01 仍需证明适用的最终配置等价。 |

## 本轮接通的身份关系

实际生产路径为：

```text
batch::run / batch::run_controlled
  -> Bank::bind（真实 Input）
  -> Input::seed_following（上次分配收据）
  -> 标量或类型化 new_in_following
  -> Journal::allocate_following（原分配器和原锁）
  -> Bank 保留真实对象并发布它的实际槽位
  -> 原 registered root 解释器
```

`Bank::wf` 同时建立源身份唯一与目标身份唯一。frontier 是会擦除的真实 Journal
收据；此前目标键都存在于该截面。下一次分配扩展这段真实历史，并且必须选择新键。
其他 Journal 使用者可以在两次分配间分配或修改：旧键仍然存在，所以新鲜性无需
假设中间没有其他步骤。

`Bank::mapping_entry` 和 `mapping_injective` 从真实 Bank 导出映射；`aliases` 证明
双向关系：同一源对象共享目标，不同源对象保持不同。源数字身份耗尽时，既有
`Unnamed` 错误仍会拒绝，不会把未知身份误判为别名。这些性质无需新增运行时身份
扫描，也无需调用方提供预期分配编号或目标状态。

映射覆盖标量和类型化分配身份。类型化种子仍保留实际源 `Arc<T>`，并不声称载荷内部
已经深拷贝；这层区别明确保留。

## 严格标量迁移与恢复式

[堆迁移证明](../crates/cordis-kernel/src/managed_replay_heap.rs)通过这个单射映射关联源与
目标标量堆。关系包含缺失条目，以及完整的 `(值, 深度)` 观察。
`Bank::scalar_contract` 证明保留的数据指令具有相同的正向定义域、结果选择分支和
对应的更新状态；对任意一对相关恢复输入，捕获的两份逆映射也具有相同定义域，
成功时继续保持状态关系。

`Source::captured_scalar_contract` 将该定律接到真实成功源步骤保留的指令、分支、地址
及结果上，从源报告与明确的输入关系推出目标原语的可执行性、输出和延续。调用方不
提供替换代码或预期目标结果；完整目标调用能否到达这样的相关输入，仍需继续证明。

`Bank::scalar_independence` 从源对象分离推导目标对象分离，再应用已有的完整正向／
逆向迭代器独立性定理。它不会因为两个共享对象操作的算术结果偶尔可交换，就证明
它们独立。

这些是 R08 和 G02 需要的局部连接。**每次后续调用开始时的状态关系，仍是迁移定理
的前提。** R01 还需要从真实执行、资源访问和此前结果中推导它。
式 (55) 的源固定映射、目标函数重新执行和合法 Episode 删除仍是不同义务，以上引理
不会自动把它们等同。

## 检查来源连续性与真实标量观察

[`continuity::check`](../crates/cordis-kernel/src/managed_replay_continuity.rs)
按给定调用顺序检查从真实逆操作所有者保留的成功步骤；batch 使用已有的认证来源排序器
产生此顺序。对每次重复访问的分配，下次实际输入必须等于前次实际输出。标量比较包含
逆操作深度；typed 比较由持久历史推出 value／head／depth 相等，不调用 `T::eq`、
转换指针或重新读取可变的源对象。不一致会标明前后两次来源调用及步骤的位置。

`Checked::recovery` 从检查结果推出这段有限来源操作词有定义且可以往返恢复，不再要求
调用方提供输入可组合或逆操作成功的前提。初始映射由每个对象首次捕获的输入组成，
不宣称它们来自同一个全局瞬时快照。检查识别的是状态不连续，并不识别每个遗漏事件：
如果中间操作返回了同一完整观察，仍需要另行组合完整历史 census。

[`batch::run_checked_scalar`](../crates/cordis-kernel/src/managed_replay_batch.rs)
将来源检查接入真实标量目标执行：

1. 检查完整保留函数，包括未走到的分支。这个入口接受已成功且全部指令为 `Kernel`
   的来源调用；来源顺序和连续性错误在目标登记之前返回。
2. 复用现有 batch 的 provider 构造、登记、Begin、root 解释器和 Finish 实现；
   没有另建解释器，也不由调用方提供期望目标结果。
3. 在 Finish 和下一次调用之前，将目标的**真实保留逆操作**所捕获的输入与源输入核对。
   `check_scalar_observations` 检查指令位置和 value／depth，证明再从这些观察及保留
   函数推出输出、选中分支和严格逆操作状态相等。`scalar_inverse` 导出完整逆操作状态
   相等，但不会转移或复制任一所有者的逆操作权限。

入口返回 `Result<CheckedScalarBatch<_, _>, PreflightError>`。返回 `Ok` 后仍需检查
`result.batch.failure`，因为目标准入或执行仍可能失败。`Failure::Observation` 指出
某次已执行调用的观察不匹配；其原报告、所有者和已经入队的逆操作保留在 `batch.calls`
中，后续调用不会启动。**这是调用后的核对，不是每次写入前的原子守卫，也不是自动回滚。**
失败可能已经产生真实效果，需要走原有清理／重试协议。

当返回且 batch 无失败时，实际标量输入对应已成为后置条件，不再由调用方提供相等前提。
这仍不证明所有通过来源检查的执行都必然重放成功。下述选择检查进一步证明被接受的
标量调用实现了 Bank 分配映射。typed 目标版本迁移、动态绑定、完整生命周期调度和式 (55) 仍未关闭。
`run` 及支持标量／typed 混合操作的 `run_controlled` 保持现有范围；更强的标量入口按需使用。

显式重放捕获现保留标量逆操作的真实后状态，以及每次目标调用的实际输入；普通 managed
执行不收集这个重放列表。来源检查临时借用观察列表，额外空间为线性，同分配向后查找的
最坏时间为平方级。历史和证明证书会擦除，可执行输入则由显式重放捕获持有。

## 真实 provider 与分配对象选择

[`check_scalar_replay`](../crates/cordis-kernel/src/managed_replay_selection.rs)
在状态核对之外增加分配对象对应。`run_checked_scalar` 会在每次实际调用返回后、Finish 前
执行它。证据沿真实生产路径传递：

1. `Bank::find` 将捕获的来源分配定位到已有 Bank 条目。
2. 实际 provider Finish 发布 Bank 的槽位。服务表、宿主和记录型 owner 的合同保证后续
   Finish 保留已有发布项；`preserve_providers` 将此事实组合到整个 batch。
3. `Source::instantiate` 将原执行器的 Begin 捕获绑定到这张真实发布表。报告中的服务绑定
   指出调用使用的 Episode 已提交 provider，以及当时捕获的槽位版本。
4. 检查器核对 provider，并要求捕获版本为零。`Capture::initial_selection` 随后证明实际
   选中的分配就是 Bank seed，包含其 Journal 身份。

这里使用发布所有权和不可变捕获证据，不假设任意命名空间中的相同分配编号代表同一对象。
来源排序与 Bank 查找已有的来源命名空间条件仍然显式保留。替换成另一 Journal 的对象也会
被槽位版本检查拒绝。检查不会重新读取目标对象或当前槽位。
独立调用这个辅助检查器需要已证明的 provider 捕获对应；生产 batch 从真实发布与 Begin
调用中推出该前提。

当返回且 batch 无失败时，`scalar_replay_matches` 证明真实来源到目标的分配映射，同时包含
相同的标量输入、输出和分支。`mapped_inverse` 包含实际严格逆操作状态；
`Batch::scalar_aliases` 证明跨实际调用的双向别名保持。这些保证针对已经记录的执行，因此
调用完成后再替换槽位，不会改变该调用保留的选择。

`Failure::Selection` 报告缺少 Bank/provider 绑定、已提交 provider 不符或捕获槽位版本非零。
状态／控制流不一致仍使用 `Failure::Observation`。两者都保留真实报告和清理 owner，并停止
后续调用。检查仍发生在**调用之后**，被拒绝的调用可能已经改变了资源。

当前范围保守拒绝所有非零槽位版本，包括换回原分配的情形。动态重绑定需要独立的迁移合同，
不能静默当作静态重放。每一步查找会扫描 Bank 和 provider 列表。新增发布／捕获证明元数据
全部擦除，普通 `run`／`run_controlled` 不执行这些新增检查。

回归测试覆盖同一及另一 Journal 中的同值／同深度替换、拒绝调用保留的真实清理，以及成功
调用后的槽位替换。临时副本的变异实验删除非零版本守卫后，Verus 在
`Capture::initial_selection` 处拒绝证明，因为无法推出版本为零。这是定向证据；本轮未运行
全套负例或整个项目的集成验收。

## 剩余工作与验证

- P01：落实完整资源访问边界。现有原始共享句柄、回调、可变载荷内部和外部 I/O，仍需
  分类合同或阻止未计入的效果。
- R01：从实际运行推导跨调用状态对应、类型化 head／revision 迁移和动态绑定变化。
  身份单射本身不完成这些义务。
- R02／R08：组合完整目标生命周期和精确恢复式。
- S01／S02：将选定的上下文／定义域解释及必要修订贯穿到最终定理。这张操作表是实现
  审查输入，不是原文无限制上下文的证明。

局部验证需覆盖本轮改动的分配模块、Bank／heap 模块及已有 managed replay 测试。
后续集成负例应拒绝：复用前一个目标分配、丢失源别名关系，以及从恢复定义域中遗漏
逆操作深度。求解超时和编译失败不能算作有效的负例拒绝。
整核开发验证及整篇验收继续单独记录。

使用固定本地工具链复现本轮局部检查：

```sh
source scripts/toolchain-env.sh
"$VERUS" crates/cordis-kernel/src/lib.rs \
  --crate-name cordis_kernel --crate-type=lib --edition=2021 --no-cheating \
  --verify-only-module execution \
  --verify-only-module lifecycle_state::services \
  --verify-only-module lifecycle_state::native \
  --verify-only-module lifecycle_state::native::managed \
  --verify-only-module lifecycle_state::native::runtime \
  --verify-only-module reversible_value::slot \
  --verify-only-module reversible_value::managed::interleaving::history::lifecycle::native \
  --verify-only-module reversible_value::managed::interleaving::history::lifecycle::host \
  --verify-only-module reversible_value::managed::replay \
  --verify-only-module reversible_value::managed::replay::inputs \
  --verify-only-module reversible_value::managed::replay::inputs::payload_history \
  --verify-only-module reversible_value::managed::replay::continuity \
  --verify-only-module reversible_value::managed::replay::observation \
  --verify-only-module reversible_value::managed::replay::selection \
  --verify-only-module reversible_value::managed::replay::order \
  --verify-only-module reversible_value::managed::replay::scalar \
  --verify-only-module reversible_value::managed::replay::transport \
  --verify-only-module reversible_value::managed::replay::bank \
  --verify-only-module reversible_value::managed::replay::bank::heap \
  --verify-only-module reversible_value::managed::replay::batch \
  --num-threads 2 --triggers-mode silent
cargo test -p cordis-kernel --test managed_replay --test native_runtime \
  --test managed_function --locked --offline
python3 -B scripts/check-paper-mapping.py
```
