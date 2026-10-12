# 原生产物分发

[English](native-distribution.md) | 简体中文

Node 兼容层在源码目录和解包后的 npm 安装中使用同一个清单选择器。GitHub Releases 分发三个预编译 npm 压缩包，并附带证明、运行测试和源码记录。npm 使用统一的 `@validation-engineering` scope；核心包将四个平台的预编译库放入同一个归档。发布前验证四个平台实际安装，发布后再从公共注册表下载并核对归档完整性。

## 从 npm 安装

```sh
npm install @validation-engineering/cordis
# 按需添加 Loader 或 Harness profile：
npm install @validation-engineering/cordis-loader @validation-engineering/cordis-compat-deepseek
```

准备 Node.js 22.22+。npm 包自带四个平台的原生库，运行时自动选择当前平台；不使用安装脚本，也不需要本机编译。仅运行纯 Rust 应用无需 Node。
原版 Cordis 插件使用 `node --import @validation-engineering/cordis/register app.mjs`；Harness 插件使用 `@validation-engineering/cordis-compat-deepseek/register`。
两个 profile 共用原生内核，`cordis-compat-deepseek` 包是兼容适配层，完整应用在独立的 Harness Verus 仓库。

历史 `v0.1.0-preview.1` 的产物仍保留 `@cordis-verus/compat-*` 包名；不要在同一个应用中混用新旧发布系列。

## 无需编译，安装已发布的运行时

准备 **Node.js 22.22+ 和 npm**，然后运行：

```sh
curl -fLO https://github.com/validation-engineering/cordis-verus/releases/download/v0.2.0/install-cordis.mjs
node install-cordis.mjs --release v0.2.0 --project my-cordis-app
cd my-cordis-app
npm start
```

Windows PowerShell 请将 `curl` 写成 `curl.exe`。无需 Rust、Verus、GitHub CLI、源码检出或 C/C++ 编译器。安装器通过 HTTPS 从公开 Release 下载产物；私有镜像可通过已认证客户端下载，再使用下文的 `--from-directory`。

安装器根据当前环境选择 macOS ARM64/x64、Linux x64 GNU 或 Windows x64 目标，下载现有的三个 npm
压缩包及其验证记录，校验大小与 SHA-256，然后使用 `npm --offline --ignore-scripts` 安装。
它会验证安装后的原生清单与构建来源记录，并实际加载两种 Cordis profile，之后才创建指定目录。
安装器不会覆盖已有项目。下载、哈希校验、软件包安装或原生加载失败时，会移除临时目录，
不会留下目标目录。目标目录的父目录必须已经存在。

生成的项目包含可运行的 `app.mjs`、软件包锁文件、保留在 `.vendor/cordis/` 中供离线
`npm ci` 使用的压缩包，以及记录源码提交、目标平台和清单哈希的 `cordis-release.json`。
可以从 `@validation-engineering/cordis` 导入，也可以通过
`node --import @validation-engineering/cordis/register app.mjs` 启动现有 Cordis 插件。
Loader 和 Harness profile 软件包一并安装，并使用同一个原生生命周期驱动。

此处交付的是 **Node 兼容运行时**，不包含完整 Harness 应用或自定义 Rust 插件。
纯 Rust 应用仍通过 Rust crate 使用内核，其应用代码需要编译。
Node 始终是为兼容现有 JavaScript/TypeScript 插件而提供的可选适配层。

离线机器需要下载所选平台的 `cordis-runtime-*.json`、其中引用的三个 `.tgz` 产物和验证记录 JSON，
以及 `install-cordis.mjs`。在本地使用同一个安装器和校验流程：

```sh
node ./release-assets/install-cordis.mjs \
  --from-directory ./release-assets --project ./my-cordis-app
```

请只安装可信发布者提供的产物：安装检查会执行软件包中的 JavaScript 和原生扩展。
哈希可以检测字节是否变化，不能确认发布者身份。GitHub 访问权限和发布审查仍是信任边界；
目前尚未实现签名与证明声明（attestation）的验证。
当目标平台、依赖或二进制不可用时，不会尝试网络回退或源码编译。

## 声明的目标平台与验证记录

| 目标 ID | 操作系统 / 架构 | 所需原生接口 |
| --- | --- | --- |
| `darwin-arm64-napi8` | macOS / ARM64 | Node-API 8 |
| `darwin-x64-napi8` | macOS / x64 | Node-API 8 |
| `linux-x64-gnu-napi8` | Linux / x64 / GNU libc | Node-API 8 |
| `win32-x64-napi8` | Windows / x64 / MSVC | Node-API 8 |

每次运行时发布必须包含这四个平台。验收环境为 Ubuntu 24.04、macOS 15（Apple Silicon 和 Intel）、Windows Server 2025 x64，以及 Node 22.22.0。Node-API 8 不代表旧版 Node 已获得支持；更早的操作系统、较低版本 glibc、Windows ARM64、Linux ARM64 和 musl 不在当前验收范围内。Node 24 虽满足包的版本范围，仍需单独认证。

每份原生产物记录实际执行的操作系统、Node 版本、Node-API 和模块 ABI，以及真实构建配置；不会将开发构建重新标记为优化构建。

## 构建、选择与验证

```sh
node scripts/build-node.mjs --offline
node scripts/check-npm-package.mjs
```

第一条命令获取 Cargo 的实际输出路径，检查普通内核扩展和单独构建的 Rust SDK 测试产物，
随后写入：

- `packages/compat-cordis/native/cordis.node`
- `packages/compat-cordis/native/manifest.json`
- `packages/compat-cordis/native/provenance/<target>.json`
- `target/node-compat/build.json`

清单将目标平台、Node-API 策略与二进制大小、二进制哈希和构建来源记录哈希绑定。
构建来源记录进一步绑定软件包、profile、驱动 ABI、源文件哈希、Cargo 与工具链锁文件、
构建报告哈希、构建 profile，以及在实际宿主环境中的加载结果。
一个新的 Node 子进程会加载独立的字节快照；已有 `require` 缓存不能为被替换的文件提供验证。
默认内核分发包不允许包含已注册的 SDK 工厂。
生成的原生元数据不纳入整个源码的证明指纹，但会纳入 npm 分发指纹。

```js
import { selectNativeArtifact, verifyNativeManifest } from '@validation-engineering/cordis/native-artifacts'
const selected = selectNativeArtifact()
console.log(selected.path, selected.entry.target, selected.manifestSha256)
const inventory = verifyNativeManifest() // 计算清单中所有产物的哈希，不执行任何产物
```

选择器会在使用产物前检查平台、架构、GNU/musl libc 和 Node-API。
无效清单、发生变化的二进制或构建来源记录、重复目标、不安全路径和符号链接都会明确失败。
驱动还会验证运行时 ABI/profile 握手。选择器不会自动下载，也不会回退到 JavaScript 调度器。
缺少目标产物会报错，不会进行跨平台模拟。

`new Context({ addon: '/explicit/custom.node' })` 和 `CORDIS_NATIVE_BINDING`
仍是显式指定自定义扩展的方式，沿用现有运行时握手。
这些路径不会自动获得默认清单的认证。
SDK 测试产物保留在 `target/node-compat/`；自定义 Rust 工厂需要单独分发和审查。
软件包检查要求每一个打包的 `.node` 文件在默认内核清单中恰好出现一次。

## 汇总本地提供的产物

```sh
node scripts/package-native.mjs --output /tmp/cordis-native-bundle /path/to/first/native /path/to/second/native
```

只应使用构建输入与预期源码版本一致的产物。每份输入清单和字节哈希都会被检查。
重复目标、混合源码快照、已存在的输出，以及输出与输入目录重叠等情况都会被拒绝。
新目录包含 `manifest.json`、`provenance/` 和 `prebuilds/<target>/cordis.node`。
汇总操作保留输入的构建来源记录；不会执行其他平台的二进制，也不会产生新的平台测试证据。
它不执行下载、上传或注册表操作。

开发工作流与发布验证工作流会汇总每个成功任务的本地原生目录，并将
`target/release-artifacts/native/` 与构建报告、npm 软件包报告一同保留。
下载这些任务产物并传给上述命令，是后续需要显式执行的步骤。
仅添加工作流步骤，不代表任何远端任务已经运行或通过。

在同一源码快照的新打包检出目录中，将汇总内容放入 `packages/compat-cordis/native/`，
并保留与当前宿主匹配的 `target/node-compat/build.json`，然后运行
`scripts/check-npm-package.mjs`。选择器同时支持原始的单层二进制路径和汇总后的 prebuild 路径。
打包目录中不能残留其他二进制；清单未列出的二进制会导致门禁失败。
在该目录重新构建会生成一份只包含当前宿主目标的新清单。

## 独立安装与边界

离线软件包门禁暂存并打包全部三个软件包，将其压缩包安装到独立的临时项目中，
随后加载选中的原生产物。
检查内容包括 ESM/CommonJS 身份一致性、原版 Cordis 导入、JSON Loader 更新、Worker 加载
和 Harness profile。它会移除源码路径、预加载及自定义扩展的环境覆盖，
确认安装结果来自解包，而不是指向工作区的符号链接。
安装后的清单必须与源码检出目录中的清单一致。
报告包含实际宿主目标、清单哈希、源码与构建哈希，以及全部三个压缩包的哈希。

开发记录的 `--check` 只重新读取验证记录并计算哈希，不执行 Node、npm 或证明。
它要求本地原生文件、SDK 测试产物、构建与软件包报告，以及压缩包仍然存在。
仅有已提交的开发报告并不足够。

SHA-256 提供字节完整性与源码绑定，不提供发布者身份认证。
构建来源记录仍是构建环境生成的未签名声明；验证该记录，不能证明任意提供的原生程序安全。
签名与 attestation、最低操作系统/libc 的发布资格，以及通过多个平台的发布矩阵，
仍属于单独的验收工作。JavaScript 和原生 FFI 的行为不在生命周期内核的 Verus 证明覆盖范围内。

## Release 产物生成

[发布工作流](../.github/workflows/release-validation.yml)在 Linux 上运行完整质量门禁，包括固定 Verus 工具链的全量证明与编译。其余三种平台运行[本机验收](../.github/workflows/runtime-platforms.yml)：Rust 测试、示例、原生/Node 兼容测试，以及独立解包后的软件包检查。`record-runtime.py` 明确记录 `proofExecuted: false`，不能单独授权发布。

共享证明策略目前只允许内核中的测试条件与 Verus ghost 条件编译；新增平台/feature 分支或生成代码引入会被发布收集器拒绝，必须先审查证明的可移植性。当前四个运行时目标均为 64 位。

收集器要求完整证明与每个平台的运行记录绑定同一提交和完全一致的源码哈希。`runtime-release/v3` 分开保留两类证据；Linux 运行测试通过不能替代 Windows 或 macOS 的通过结果。收集器在打包前核对原生产物来源与压缩包哈希。四个平台随后在名称带空格的新目录中安装同一批产物，运行示例，再离线执行 `npm ci` 并重新运行。安装任务没有源码检出或编译步骤。

[整 crate 负控](full-negative-validation.md)保持独立，在发布记录中明确标注 `not_run`。证明合同和范围不变：平台测试不等于对 Node、FFI 或任意插件的证明。

使用 `create_draft=true` 与新的 `release_tag` 触发工作流；只有所有必需任务通过，才会创建**预发布草稿**。草稿包含四个平台的产物、独立安装器与 `SHA256SUMS`，不允许复用已有标签。检查结果后发布草稿，工作流本身不会自动公开发布。详见[发布流程](releasing.md)。
