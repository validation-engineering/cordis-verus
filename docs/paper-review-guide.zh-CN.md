# 从论文主张审查可执行 Verus 代码

[English](paper-review-guide.md) | 简体中文

本指南从 *A Programming Paradigm for Spatiotemporal Composability*
（[arXiv:2608.25512v1](https://arxiv.org/abs/2608.25512v1)）中的五项主张出发，
追踪其合同、实际执行调用和回归测试。它是独立审查的入口，不代表整篇论文或异步宿主
已经得到验证。

各项状态仍以 [paper-obligations.json](paper-obligations.json) 及其生成的
[覆盖表](paper-coverage.md) 为准。这些审查案例不改变任何条目的状态。
所选定义的状态为 `formalized`（已形式化），引理 62 为 `refuted`（已反驳），
定理 80 为 `partial`（部分完成）。对定义进行编码，不等于证明所有使用该编码的代码
都满足某个定理。

## 如何使用本指南

1. 阅读固定版本的论文及所引用的条款。下文页码是从 1 开始计数的 PDF 页码，
   与本地提取文本的分页标记一致。数学公式的排版以 PDF 为准。
   PDF 哈希见 [upstream.lock.json](../upstream.lock.json)，固定的工具链版本见
   [toolchain.lock.json](../toolchain.lock.json)。
2. 阅读函数的**完整 `requires` 和 `ensures`**、不变式及其投影，并沿实际执行路径
   找到对该函数的调用。仅仅链接到一个定理，并不能说明应用满足该定理的前提。
3. 运行选定的 Cargo 回归测试。它检查实际执行行为；它不会调用 Verus，也不能证明
   所有调度都具有相同行为。
4. 使用 `./scripts/verify.sh` 验证源码。该脚本使用固定的验证器，对实际内核源码启用
   `--no-cheating` 进行验证，并编译这份源码。工具链配置见
   [CONTRIBUTING.md](../CONTRIBUTING.md)。普通 Rust 宿主有独立的测试边界。
5. 报告问题时，记录提交号（`git rev-parse HEAD`）、命令、工具链和原始结果。
   在 GitHub 源码页面按 **y** 可得到固定到提交的永久链接。本指南使用相对链接，
   以便跟随当前受审查的检出版本。

以下命令均在仓库根目录运行。`--offline` 要求 Cargo 所需依赖已经缓存；首次下载
依赖时可省略该选项。`--exact` 用于精确选择具名回归测试，避免仅按子串匹配。
请确认输出显示实际运行了一个测试。

简明的[案例索引](paper-review-cases.json) 记录了论文位置、清单状态、源码符号和
测试名称。无需构建项目即可检查：

```sh
python3 scripts/check-paper-review.py
```

这是一项文档一致性检查。它不能确立语义对应关系，不会运行测试，也不会刷新证明证据。
如果本地存在被 Git 忽略的论文文本，它还会检查锁定的哈希、页码与标题标记。
本仓库不重新分发论文全文，参见 [reference/README.md](../reference/README.md)。

第 73 条的对应另见[进展要求与真实代码合同](progress-contracts.zh-CN.md)：
包括精确成功条件、运行时调用路径、同步 Mixed/Fresh 单步与跨调用已接纳落地域。
这些实现合同也对应引理 57。真实 Fresh 循环推出单个 actor 在终态或首个错误处有限
返回，并条件化延伸其输入已表示的源状态。`run_from_empty` 通过真实准备脚本建立
该输入，证明一条从 empty 出发、同时表示准备后与返回机器的源执行，每态均良构且
资源安全。`SetupFailed` 在自主循环前停止，并不表示 actor 被阻塞。Insert/Begin/Step
现由 `preparation_enabled` 给出精确实现接纳域；该范围内的失败命令在真实失败状态不
满足定义域，即使此前缀含其他命令也成立，不要求全部命令最初就使能。
Retire/Depart/Unload/Remove 仍受支持，但不在该准备范围内。实际 Mixed/Fresh
Unload dispatcher 分支另有清理守卫加 inverse 的精确域；真实源历史还导出实际
完整具体 Unit/Child/Provision/Xor 日志的 inverse 有定义性，见 PR-02。其余命令与 dispatcher 的域、
具体错误枚举、整个系统进展、任意 Future 完成及宿主调度仍有独立义务。这些合同修复不需要引入
时序逻辑依赖。

## PR-01: episode 保留其已提交的 provider 身份

**论文位置：** §4.2.2，定义 53，第 35 页，式 (48) 和 (49)；定义 54，
第 36 页，式 (50)；L-Begin，第 36 页；L-Unload，第 37 页。

**行为：** 当前依赖解析结果发生变化，不会悄悄改写已安装 consumer 所提交的 provider。
只要还有 consumer 在其已提交视图中持有某个 provider，该 provider 的清理就必须等待。
处于 Active 状态的 consumer 可以暂时与其当前目标不一致。

**审查路径：**

- [semantics.rs](../crates/cordis-kernel/src/semantics.rs)：`target` 和 `quiet`
  使用实际发布表的定义域，对完整状态模型中的定义进行编码。
- [refinement.rs](../crates/cordis-kernel/src/refinement.rs)：`target`、`relied`
  以及 `step` 中的 `Begin` / `Unload` 分支规定控制投影。该投影将发布行为限定为
  完整发布所有声明的服务，并擦除载荷、迭代器和累积器。同一文件还明确区分了宿主的
  `Restart` 与论文的九条规则。
- [lib.rs](../crates/cordis-kernel/src/lib.rs)：`Kernel::begin` 要求 `wf()`。
  成功时，它保持 `wf()`，建立 `committed_from(old(self), id)` 和
  `refinement::step(..., Rule::Begin)`。其可执行循环记录当前目标返回的绑定。
  `begin_cleanup` 在保持绑定的同时建立 `restoration_guarded(id)`；
  `finish_cleanup` 建立 `Rule::Unload`，并清空该 episode 的已提交视图。
- [driver.rs](../crates/cordis-kernel/src/driver.rs)：`Driver::unload` 调用
  `begin_cleanup`，恢复真实的资源日志，然后调用 `finish_cleanup`。其后置条件
  同时包含控制规则，以及将 `resource(id)` 恢复为 `initial(id)`。
- [mixed_driver.rs](../crates/cordis-kernel/src/mixed_driver.rs) 和
  [fresh_driver.rs](../crates/cordis-kernel/src/fresh_driver.rs)：公共 `unload` 在且仅在
  `unload_enabled` 时成功，将 Kernel 清理许可与实际 journal 的 `restore_receipts`
  有定义性合取。`undo_one` 执行对应的 strict inverse，循环保持 restoring 并递减
  journal 长度。公共错误保持完整机器，内部草稿则可能已经恢复部分前缀。它将守卫
  接到真实有限清理；`!relied` 本身不保证任意 inverse 有效。对应引理 57、推论 69
  和定理 73 的范围仍为 partial：执行有定义的恢复，不等于一般 foreign replay
  观察等价或整个系统进展。下文 PR-02 为完整具体 Unit/Child/Provision/Xor 日志导出
  inverse 条件，不改变清理守卫。
- [lifecycle_actions.rs](../crates/cordis-kernel/src/lifecycle_actions.rs)：
  `LifecycleActions` 将精确动作票据、清理结果和实际的
  `Kernel::finish_cleanup` 调用连接起来。失败结果保留阻塞凭据；显式重试获得新票据。
  共享 Driver 与 Node 路径调用这一可执行协议。合同、reservation 扩展、可重试 Rust
  inverse 以及普通 Rust 对已消耗 `FnOnce` 失败采用的 `Drained` 策略，见
  [清理协议审查](cleanup-protocol.zh-CN.md)。
  宿主报告是否真实、外部 inverse 的效果仍在证明之外。
- [lifecycle_state.rs](../crates/cordis-kernel/src/lifecycle_state.rs)、
  [cleanup_release.rs](../crates/cordis-kernel/src/cleanup_release.rs) 与
  [publication_cleanup.rs](../crates/cordis-kernel/src/publication_cleanup.rs)：
  实际共享 owner 一起持有 Kernel/协议。受管 finish 检查 domain、凭据、资源来源和
  清单完整性；原子注册表批次先于 commitment 释放。拒绝保持 finish 输入，成功则
  清空该 episode 的受管资源并返回精确 slot。回调真实性、获取路由和值句柄删除仍在边界外。
- [cleanup_protocol.rs](../crates/cordis-kernel/src/cleanup_protocol.rs)：生产
  `execute_cleanup` 为这些真实调用提供统一转换合同；`run_cleanup` 从实际循环
  构造可擦除历史。`consumed_ticket_never_returns` 拒绝之后所有重放；`binding_at`
  保留实际 provider 直到释放；`permission_origin` 与 `release_has_accepted_report`
  在入口没有释放许可的前提下定位匹配的已接受报告。从失败凭据出发，
  `failed_prefix_retains_dependencies` 覆盖没有新接受授权报告时的任意有限次数重试
  及其他 owner 操作。受管资源 finish 也满足相同转换关系。具体命令集合与真实入口
  状态前提见清理指南；它们不涵盖任意回调，不证明应用启动或清理最终结束。
- [cleanup_journal.rs](../crates/cordis-kernel/src/cleanup_journal.rs)：实际 Rust
  inverse 日志保留失败的选中 token，仅在显式重试时签发新凭据。更早的待处理操作和
  晚到登记持续被记录；重复、旧尝试及外域报告不能清除选中操作。Runtime 和静态
  typed 宿主在回调执行前后调用这些经过验证的函数。
- [cleanup_queue.rs](../crates/cordis-kernel/src/cleanup_queue.rs)：日志同时拥有
  宿主实际的载荷向量。`register`/`land` 将精确值关联到分配的 token；`pop` 只移出
  一次；`complete` 原样保存传入的重试值，被拒绝时则原样返回。`retry` 要求值仍然
  保留；`is_empty` 排除遗漏的已保存或已交付工作。执行器返回哪个工厂及工厂实际
  做了什么，仍是宿主义务。
- [runtime.rs](../crates/cordis/src/runtime.rs)：普通 Rust 中的
  `Runtime::poll_settle` 在执行宿主回调前后调用共享生命周期 Driver。
  这是实际的集成路径，不是对任意回调或 Future 行为的证明。

**执行检查：**

```sh
cargo test --offline -p cordis-kernel --test refinement strict_departure_preserves_committed_views_until_guarded_unload -- --exact
cargo test --offline -p cordis-kernel --test driver provider_resources_remain_live_until_consumer_recovery -- --exact
cargo test --offline -p cordis --test runtime provider_waits_for_async_consumer_cleanup -- --exact
cargo test --offline -p cordis-driver --test cleanup_outcomes failed_cleanup_retains_provider_until_an_exact_fresh_retry_succeeds -- --exact
cargo test --offline -p cordis-driver --test cleanup_resources failed_report_retains_resources_until_fresh_retry_releases_only_its_batch -- --exact
cargo test --offline -p cordis-driver --test cleanup_resources late_invalid_manifest_items_cannot_partially_release_an_accepted_cleanup -- --exact
cargo test --offline -p cordis-driver --test cleanup_resources a_foreign_registry_with_identical_local_ids_cannot_use_this_cleanup_receipt -- --exact
cargo test --offline -p cordis-driver --test cleanup_resources a_remaining_consumer_lease_blocks_the_entire_publication_batch -- --exact
cargo test --offline -p cordis-driver --test cleanup_resources reservation_cleanup_releases_generation_zero_only_after_a_successful_retry -- --exact
cargo test --offline -p cordis-kernel --test cleanup_journal failure_retains_selected_token_and_retry_rejects_old_or_foreign_receipts -- --exact
cargo test --offline -p cordis --test retry_cleanup failed_retryable_cleanup_pins_provider_and_resumes_lifo_without_replaying_success -- --exact
cargo test --offline -p cordis-node --test plugin_runtime typed_retryable_cleanup_recovers_only_on_a_new_host_attempt -- --exact
cargo test --offline -p cordis-kernel --test cleanup_queue retained_payload_returns_from_the_same_slot_before_late_and_earlier_work -- --exact
cargo test --offline -p cordis-kernel --test cleanup_queue foreign_and_duplicate_completions_return_payloads_without_overwriting_live_work -- --exact
cargo test --offline -p cordis --test retry_cleanup distinct_failed_groups_keep_their_own_factories_and_drop_each_only_after_success -- --exact
cargo test --offline -p cordis-kernel --test cleanup_protocol repeated_failed_prefixes_pin_the_provider_while_another_consumer_finishes -- --exact
cargo test --offline -p cordis-kernel --test cleanup_protocol setup_reply_and_wrong_ticket_fields_cannot_authorize_cleanup -- --exact
cargo test --offline -p cordis-kernel --test cleanup_protocol generation_zero_reservation_uses_its_own_release_guard_after_retry -- --exact
cargo test --offline -p cordis-kernel --test cleanup_protocol completed_receipts_stay_rejected_after_real_episode_reactivation -- --exact
```

第一个测试观察到：当前目标不可用时，consumer 原有的已提交绑定仍然保留，
过早清理 provider 会被拒绝。第二个测试运行真实的资源恢复。第三个测试检查异步宿主，
属于**测试证据**，不能证明每个宿主 Future 都会终止或保持其外部资源。
第四个测试通过生产共享 Driver 检查失败后保留依赖，直到新的精确重试票据成功并显式完成卸载。
队列另行证明不透明清理载荷的移动；类型化服务存储、已逃逸的 `Arc` 值和回调执行
仍不在此控制投影之内。

**负控候选：** `provider-lifetime-guard` 移除实际的 provider 守卫。
变异测试套件中存在该候选，不等于当前已经取得通过的负控结果；参见下文的证据边界。

## PR-02: 子插件退役要求被引用的身份继续保留在注册表中

**论文位置：** §4.2.1，定义 52，第 35 页：创建子插件的迭代返回所创建的名称，
并将其退役操作捕获为逆操作。定义之后的讨论使用了 O-Retire 要求名称已注册这一前提。

**分类：** 已形式化的原语，加上**明确修订的移除策略**。子插件已退役，不代表尚未执行
的逆操作不再需要它的身份。不受限制的 O-Remove 可能过早移除该身份。

**审查路径：**

- [paper_instantiation.rs](../crates/cordis-kernel/src/paper_instantiation.rs)：
  `typed_instantiate` 和 `captured_retirement` 在给定上下文解释及编辑器定律的前提下，
  表达原始原语的条件性合同。必须审查这些前提；下述可执行 driver 不会自动实例化
  论文中完整的递归上下文与 Component 模型。
- [child_history.rs](../crates/cordis-kernel/src/child_history.rs)：`retained`
  表示任何实际累积器引用的每个子插件都仍在注册表中。`remove_unreferenced` 提供
  额外的移除条件。`retained_recovery` 在原语逆操作合同成立的前提下，证明恢复的
  定义域与类型性质；`retention_protocol_refines` 为修订后的协议证明执行、引用保留
  和良构性。它并不是在没有前提的情况下推导任意表值都能恢复。
- [child_driver.rs](../crates/cordis-kernel/src/child_driver.rs)：`ChildDriver`
  私有地持有自己的 Kernel 和各个 episode。`wf` 包含每份日志所引用身份均已注册的
  条件。`refines_retention` 将这些**真实日志**投影到 `child_history::retained`，
  而非使用一份无关的 ghost 历史。
- `land_child` 调用实际的子插件 episode，并捕获其逆操作。`remove` 首先通过
  `has_reference` 扫描每份日志；成功时保证 `remove_unreferenced`，返回 `Retained`
  则意味着确实存在引用。`unload` 调用 `ChildEpisode::finish_restore`；成功时
  保证 `ownership::child_unload` 且日志为空。
- [mixed_driver.rs](../crates/cordis-kernel/src/mixed_driver.rs) 和
  [fresh_driver.rs](../crates/cordis-kernel/src/fresh_driver.rs)：
  [`unit_child_recovery.rs`](../crates/cordis-kernel/src/unit_child_recovery.rs)
  将已表示的良构源状态中保留的 child 身份接到实际 receipts。
  `history_sound` 本身只保证当初落地时 inverse 有定义；retention 才给出当前事实。
  对已登记 actor 的 `unit_child_journal`，Unit 恒等操作与 Child retirement 均保持
  registry 成员，因而整个真实 LIFO journal 的恢复有定义。实际 `run_script` 返回
  机器具有此性质；`run_from_empty` 也在准备及返回处建立它。不新增运行时 history
  buffer、替代恢复实现或强化 `wf`。
- `unit_child_unload_domain` 再于上述恢复性质和日志分类下，证明 `unload_enabled`
  等于 `cleanup_permitted`。公共 Unload 与实际 `apply` 分支将该域接到执行。
  脚本若在仅含 Unit/Child 的 Unload 处停止，则该停止状态不允许清理。退休 child
  在合法 Remove 前仍已登记；parent 所有权不产生服务依赖，也不要求 child 先完成
  清理才能执行 parent 的 inverses。下述源不变式将该结论扩展到 Provision 与 Xor。这是定义 52、引理 57 和定理 73 的受限桥，不是推论 69 的一般
  foreign replay 恢复方程；引理 57 和定理 73 仍为 partial。

- [`provision_history.rs`](../crates/cordis-kernel/src/provision_history.rs) 与
  [`provision_recovery.rs`](../crates/cordis-kernel/src/provision_recovery.rs)
  进一步覆盖真实 Unit/Child/Provision 日志。从 empty 的实际执行导出
  `live_provisions`：每条保留的 Provision 都对应 owner 中有值的槽，同一 owner
  活跃日志中的 Provision key 互异。外部 Xor 可修改 payload，但保持槽占用。
  receipt 桥导出 `provision_recovery`，`provision_unload_domain` 再连接同一个
  Kernel 清理守卫；Mixed/Fresh 脚本和 bootstrap 返回值从真实历史建立该性质。
  下述更强结论也覆盖自身含 Xor 的日志。
- [`operation_history.rs`](../crates/cordis-kernel/src/operation_history.rs) 与
  [`journal_recovery.rs`](../crates/cordis-kernel/src/journal_recovery.rs)
  为全部四种具体 receipt 建立 `journal_recovery`。`live_operations` 导出当前仍
  解析到捕获的 provider、provider 与值保留，以及较后 Provision 不删除较早 operation
  所需槽的顺序条件。与 Provision 唯一性及 child retention 组合后，`restore_all`
  证明实际 LIFO 日志恢复有定义。Provider 事实连接定义 53/54 与 PR-01 的 commitment
  守卫：退休或 target 漂移不会替换 Xor 捕获的 provider。实际脚本返回及两份 bootstrap
  机器均带有更强性质；`journal_unload_domain` 不再需要 receipt 分类来化简清理域。
  脚本在 Unload 处失败意味着停止状态不允许清理。范围是具体的同步 `u64`/Xor 语言，
  不包括任意 scalar 效果、宿主回调、一般 foreign replay 方程或全局终止；owner 表空
  结论由下述覆盖桥建立。
- [`provision_coverage.rs`](../crates/cordis-kernel/src/provision_coverage.rs) 与
  [`owner_table_recovery.rs`](../crates/cordis-kernel/src/owner_table_recovery.rs)
  将推论 69 的 owner 表空结论接到真实恢复。`provided_journals` 用保留的 Provision
  逆记录覆盖每个当前 owner 槽，与保证每条已记录 Provision 的值仍存在形成反向对应。
  `owner_table_recovery_from_source` 把覆盖接到实际 receipts：若整个恢复有定义，
  其结果的 owner 表为空。`journal_recovery` 另外提供有定义性。两项性质均在实际
  脚本及 bootstrap 返回处成立；调用前具备 `owner_table_recovery` 时，公共 Unload
  及其 `apply` 分支成功后保证实际输出表为空。各个单独 mutator 未统一公开该性质的
  保持合同。没有新增运行时清空操作或历史缓冲；Child inverse 仍只退休 child，不清空
  其独立表。一般 foreign replay 方程、任意宿主效果及全局进展仍是独立义务，推论 69
  继续保持 partial。
- [`terminal_replay.rs`](../crates/cordis-kernel/src/terminal_replay.rs) 将终态值
  方程接到实际 **Mixed** `ScriptReport` 输出。`transitions` 中匹配的 Begin、末条
  成功 owner Unload 及无中途 owner Unload 直接标识 episode。
  `terminal_recovery(bank)` 自动提供真实源执行、空 owner 表以及
  `value_observation() == foreign_replay(...)`，证明方法 `terminal_replay` 提取
  见证，无须调用者提供源轨迹。
  [`xor_recovery_algebra.rs`](../crates/cordis-kernel/src/xor_recovery_algebra.rs)
  为真实 Xor library 证明 scalar 交换。重放从 Begin 紧后开始，排除 owner landings，
  foreign Unload 使用实际捕获的 inverses。定义 51 的值投影包含 Loading 表，不是
  只发布 Active 的投影。允许 owner Child，后续命令失败不排除成功前缀结论。值重放
  中缺 key 的操作是恒等，因此**不**声称删除 owner 步骤后仍有合法生命周期执行，
  也不声称 registry 身份恢复。Fresh 动态 choice 重放、任意宿主效果及整篇恢复仍是
  独立义务；定理 68／推论 69 保持 partial。

**执行检查：**

```sh
cargo test --offline -p cordis-kernel --test paper_vestige retiring_an_already_removed_child_requires_an_idempotent_extension -- --exact
cargo test --offline -p cordis-kernel --test child_driver retired_inactive_child_is_retained_until_real_inverse_is_consumed -- --exact
cargo test --offline -p cordis-kernel --test child_driver all_actual_journals_retain_their_children_through_nested_recovery -- --exact
cargo test --offline -p cordis-kernel --test unit_child_recovery fresh_history_retains_retired_children_until_parent_recovery -- --exact
cargo test --offline -p cordis-kernel --test unit_child_recovery mixed_history_retires_captured_children_without_running_their_journals -- --exact
cargo test --offline -p cordis-kernel --test unit_child_recovery failed_script_retained_removal_keeps_a_recoverable_actual_prefix -- --exact
cargo test --offline -p cordis-kernel --test unit_child_recovery bootstrap_terminal_publication_failure_keeps_a_recoverable_child_receipt -- --exact
cargo test --offline -p cordis-kernel --test provision_recovery mixed_history_recovers_distinct_provisions_and_only_its_captured_child -- --exact
cargo test --offline -p cordis-kernel --test provision_recovery foreign_xor_preserves_a_real_provision_until_dependency_cleanup_allows_recovery -- --exact
cargo test --offline -p cordis-kernel --test provision_recovery duplicate_provide_failure_keeps_the_actual_provision_and_child_prefix_recoverable -- --exact
cargo test --offline -p cordis-kernel --test provision_recovery bootstrap_missing_publication_still_recovers_committed_provision_and_child -- --exact
cargo test --offline -p cordis-kernel --test xor_recovery mixed_script_recovers_self_xors_before_removing_their_provisions -- --exact
cargo test --offline -p cordis-kernel --test xor_recovery retired_provider_stays_available_to_the_consumers_captured_xor_inverses -- --exact
cargo test --offline -p cordis-kernel --test xor_recovery interleaved_consumers_recover_only_their_xors_and_keep_the_provider_value -- --exact
cargo test --offline -p cordis-kernel --test xor_recovery bootstrap_failure_recovers_its_self_and_foreign_xors_from_the_real_prefix -- --exact
cargo test --offline -p cordis-kernel --test owner_table_recovery failed_bootstrap_clears_all_owner_values_before_reprovide_without_clearing_child -- --exact
cargo test --offline -p cordis-kernel --test owner_table_recovery mixed_script_republishes_same_registration_after_dispatcher_unload -- --exact
cargo test --offline -p cordis-kernel --test terminal_replay terminal_owner_unload_absorbs_consumers_of_its_new_service_but_keeps_child_values -- --exact
cargo test --offline -p cordis-kernel --test terminal_replay failed_command_after_terminal_unload_keeps_foreign_replay_of_the_successful_prefix -- --exact
```

第一个测试暴露了公开 Kernel 路径上因名称不存在而失败的情况。持有内部状态的
ChildDriver 测试展示了额外的保留策略如何防止过早移除，并消耗已捕获的退役操作。
公开 Kernel 原有的 O-Remove 没有被悄悄收紧。其他适配器必须各自建立相应的保留行为；
本案例不能证明任意 JS 子插件回调的行为。

新 Unit/Child 测试通过公共脚本检查退休身份的保留、parent 恢复不执行 child 自身
日志，以及 Retained 错误后成功前缀仍可恢复。外部插入、只有同一 parent 而未被
receipt 捕获的 child 不会因此退休。它们是行为回归；Unit 恒等操作本身不能让测试
观察出逆操作先后顺序，LIFO 与有定义性仍须审查证明合同。Xor 案例使顺序可观察：
自身 Xor 必须先恢复，其 Provision 才能删值。另检查 provider 退休后的 consumer 恢复、
保留另一 consumer 的交错效果，以及启动 publication 失败后的成功前缀恢复。测试都
从公开历史构造状态，没有注入私有 journal。Owner 表案例进一步在恢复后的同一注册
上开始下一轮 episode：成功 Provide 检查旧值无残留，另行检查 child 表和 foreign
provider 的值。终态重放测试将最终值与明确的 foreign-only 计算对比：owner 新建 key
的 consumer 在值重放中可变为缺 key 的恒等操作，但原 consumer 命令已未必可运行。
另一案例包含中途 foreign 清理及终态 Unload 后失败的命令。这些是具体观察的测试，
不是任意效果或合法生命周期删除的证明。

**负控候选：** `child-removal-ignores-retained-token` 弱化对已退役子插件的保留条件。
当前检出版本的验收证据仍需单独取得。

## PR-03: 残留条目仍可能影响父节点的守卫条件

**论文位置：** §4.3，引理 62，第 42 页，第 (1) 和 (2) 款。

**分类：** 对论文原文引理的反例，不是在上游 Cordis 中发现了内存安全缺陷。
仅仅观察不到服务，并不能让一个条目对所有控制规则都不可见。

**审查路径：**

- [semantics.rs](../crates/cordis-kernel/src/semantics.rs)：
  `vestigial_parent_counterexample` 建立一个已退役、非活跃且为空的子插件，
  删除该子插件后其父节点就可以被移除。这与第 (2) 款声称在所列例外之外仍具有
  反向可应用性相矛盾。`vestigial_insert_counterexample` 建立的反例说明，新插入
  可以使用一个残留条目作为父节点；擦除该父节点会阻止相同的插入，而保留它则会使
  它不再没有子节点，与第 (1) 款矛盾。
- `counterexample_reachable_full` 证明：在 idle 模型下，这个父子节点反例可以从
  空状态经过四次完整规则转换到达。请阅读这些函数实际的 `ensures`：它们证明的是
  反例所需的事实，而不是那个不成立的引理。
- [paper_vestige.rs](../crates/cordis-kernel/tests/paper_vestige.rs) 在真实 Kernel
  值上执行 `Kernel::insert → retire → remove`。第一个回归测试先得到
  `Error::Children`，然后移除残留子插件，再移除父节点。第二个测试对比保留与移除
  父节点两种情况下的插入行为。
- [deletion.rs](../crates/cordis-kernel/src/deletion.rs)：`full_step_bisimulation`
  和 `suffix_deletion` 是限定范围的修正，包含父节点、名称新鲜性和服务提供方面的
  例外，以及原语擦除与保留的假设。它们不是原文中不受限制的引理 62。

**执行检查：**

```sh
cargo test --offline -p cordis-kernel --test paper_vestige erasing_a_vestigial_child_changes_the_parent_removal_guard -- --exact
cargo test --offline -p cordis-kernel --test paper_vestige vestigial_parent_is_observable_to_new_child_insertion -- --exact
```

复现这些控制规则层面的现象不需要任何宿主回调。“任意外部效果都遵守修正后的擦除定律”
这一更强的主张仍不在本案例范围内。完整论证，以及它与第 78–80 项尚未解决的、
基于 Child 的异议之间的区别，参见 [paper-audit.md](paper-audit.md)。

**负控候选：** `erasure-drops-parent-read` 针对修正后的转移条件。
这与前述两个反例的正向证明不同：证明一个反例，不等于得到一个变异测试结果。

## PR-04: 固定的可执行程序语言在静止状态下的合流性

**论文位置：** §4.3.5，定理 80，第 54 页：第 (1) 款要求规范排序；第 (2) 款
比较相同编排输入下的静止结果。

**分类：** 与第 (2) 款相关、已经证明的受限结论。原条目状态仍为 `partial`；
这条路径既没有证明原文中的规范排序，也没有证明不受限制的动态子插件合流性。

**审查路径：**

- [program.rs](../crates/cordis-kernel/src/program.rs)：`ProgramDriver` 固定程序代码、
  初始私有单元、所有者、声明和布局。可执行路径为
  `insert → begin → admit → land → finish`，两次激活之间可以执行退役、离开、
  恢复和移除。`land` 根据固定代码计算；若目标发生漂移，完成该步时直接进入
  Unloading。调用者不能任意提供下一个值或后续执行内容。
- [program_refinement.rs](../crates/cordis-kernel/src/program_refinement.rs)：
  `wf` 和 `project` 将实际快照、程序前缀与日志深度连接到完整状态模型。
  深度只计算实际指令，排除了程序终止后的虚构阶段。
- [program_trace.rs](../crates/cordis-kernel/src/program_trace.rs)：
  `raw_execution` 描述成功的 API 调用历史；`driver_trace_refinement` 在由实际
  历史构造的模型下，产生一次完整规则执行。
- [program_normal_form.rs](../crates/cordis-kernel/src/program_normal_form.rs)：
  `trace_inputs` 从提取出的 Insert / Retire / Remove 输入推导最终配置。
  `driver_quiet_confluence` 要求两条这样的历史具有相同的初始输入、相同的已提取
  编排输入，最终状态都静止，且第一条历史的最终控制状态具有 `precedence_ranking`。
  它保证两者的 `project` 结果相等，并且两条历史都具有完整规则可达性。
  最终载荷相等、中间调度相同，都不是该定理的前提。

**执行检查：**

```sh
cargo test --offline -p cordis-kernel --test program_normal_form quiet_values_agree_after_different_schedules_and_provider_replacement -- --exact
```

这个回归测试比较了包含 provider 替换和执行中的 consumer 转向在内的不同调度。
请通过阅读定理判断其全称主张；测试仅提供具体执行。该实现范围使用有限、仅向前执行的
指令，以及私有的服务提供单元。跨 provider 的任意载荷操作、动态子插件指令、
所有失败调用轨迹，以及任意 Rust / JS 回调，均不在这一合流性定理之内。
为某条轨迹构造的模型也不会自动满足原始完整上下文 Component 的全部前提。
API 详情见 [verified-programs.md](verified-programs.md)。

**负控候选：** `normal-form-counts-phantom-stages` 弱化实际深度不变式。
只有取得新的、结论明确的拒绝结果，才能将它作为受审查源码的已接受证据。

## PR-05: 配置条目包含六个彼此独立的字段

**论文位置：** §5.2.1，定义 81，第 65 页：关于 `id`、`url`、`isolate`、
`intercept`、`config` 和 `disabled` 的六个条目。

**分类：** 对记录的可执行编码，以及普通宿主中的叶节点投影。这并不证明后续段落中的
协调主张；那些主张还依赖更广泛的元理论。

**审查路径：**

- [configuration_entry.rs](../crates/cordis-kernel/src/configuration_entry.rs)：
  泛型 `Entry` 是由 Verus 验证、也由 Cargo 编译的同一个可执行类型。
  `new` 精确保留其六个输入；`enabled` 保证结果为 `disabled` 的否定；
  `set_config` 和 `set_disabled` 保证其他字段不变。
- `reconciliation_key` 将所在父节点与条目的 `id` 配对；父节点不是第七个字段。
  `sibling_keys` 证明兄弟节点的键相等，当且仅当其标识符相等。
  `bound_effect` 表示将所选模块应用于该配置；当 URL 和配置相同时，
  `binding_ignores_administration` 成立。这项规约不会执行任意模块回调。
- [loader.rs](../crates/cordis/src/loader.rs)：`Entry::as_paper_entry` 调用一个由
  调用者明确提供的模块 URL 解析器，再调用已经验证的
  `configuration_entry::Entry::new`。它接受具名插件叶节点，拒绝未解析的名称、
  组、include 以及带子节点的条目。它保留拦截与 schema 归一化之前的原始配置，
  以及条目自身的启用管理位；后者独立于其父节点实际生效的启用状态。

**执行检查：**

```sh
cargo test --offline -p cordis --test loader paper_leaf_projection_requires_resolution_and_preserves_raw_configuration -- --exact
```

该测试解析一个已禁用但包含已启用子节点的父节点，检查子节点自身的启用位，
区分原始配置与拦截元数据，并检查应被拒绝的投影。解析器、URL 解析器、宿主投影本身、
模块执行、整棵树的协调和持久化均属于普通 Rust。验证六字段构造器，不能确立这些行为。

**负控候选：** `configuration-enabled-polarity` 在保持合同不变的情况下修改实际执行
的布尔返回值。仅仅声明该变异，不能证明变异测试套件已经通过。

## 证据边界与审查贡献

上述五个具名变异候选均定义于
[scripts/check-negative.py](../scripts/check-negative.py)。当前被接受的发布证据
必须来自 [verification-report.json](verification-report.json)，不能以存在候选为据。
本指南引入时，该报告记录的是**尚无成功的完整发布验收运行**。超时、求解器资源失败、
编译错误或失败的实验性局部运行，都不是通过的负控结果。开发验证单独记录在
[development-report.json](development-report.json) 中。

发布验收命令为 `./scripts/quality.sh --offline`，其中包含针对完整 crate 的负控。
它的检查范围和成本都高于上述选定回归测试。开发检查通过，不能替代发布验收或整篇论文
完成的证据。

有帮助的审查报告应指出案例 ID、提交号和确切函数，并说明问题属于：编码有误、
前提缺失、实际执行路径未连接、证据无效，还是应用行为存在差距。尽可能附上简短轨迹或
复现命令。原生 ABI 限制、资源计数等纯工程补充，应继续明确标注为工程合同，
除非已经建立与论文的实际对应关系。
