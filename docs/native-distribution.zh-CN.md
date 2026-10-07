# 原生产物分发

[English](native-distribution.md) | 简体中文

Node 兼容层在源码检出目录和解包后的 npm 安装中使用同一个清单选择器。
三个 npm 包可以作为预编译产物通过 GitHub Release 分发。
**目前尚未发布运行时 Release**；以下命令需等维护者发布通过验证的运行时草稿后才能使用。
源码仓库已公开，npm 软件包尚未发布；注册表发布和签名属于单独的工作。

## 无需编译，安装已发布的运行时

前置依赖为 Node.js 22.22+、npm 和 [GitHub CLI](https://cli.github.com/manual/gh_release_download)。
访问私有仓库还需要通过 `gh auth login` 登录具有读取权限的账号。
不需要 Rust、Verus、源码检出目录或 C/C++ 编译器。
请从仓库的 Releases 页面选择一个明确的已发布运行时标签；工具链归档标签不是运行时 Release。

```sh
# 将占位符替换为已发布的运行时标签。目前尚无此类标签。
CORDIS_RELEASE_TAG='<published-runtime-tag>'
gh release download "$CORDIS_RELEASE_TAG" \
  --repo validation-engineering/cordis-verus \
  --pattern install-cordis.mjs --dir ./cordis-installer
node ./cordis-installer/install-cordis.mjs \
  --release "$CORDIS_RELEASE_TAG" --project ./my-cordis-app
cd my-cordis-app
npm start
```

安装器根据当前环境选择 macOS ARM64/x64 或 Linux x64 GNU 目标，下载现有的三个 npm
压缩包及其验证记录，校验大小与 SHA-256，然后使用 `npm --offline --ignore-scripts` 安装。
它会验证安装后的原生清单与构建来源记录，并实际加载两种 Cordis profile，之后才创建指定目录。
安装器不会覆盖已有项目。下载、哈希校验、软件包安装或原生加载失败时，会移除临时目录，
不会留下目标目录。目标目录的父目录必须已经存在。

生成的项目包含可运行的 `app.mjs`、软件包锁文件、保留在 `.vendor/cordis/` 中供离线
`npm ci` 使用的压缩包，以及记录源码提交、目标平台和清单哈希的 `cordis-release.json`。
可以正常从 `@cordis-verus/compat-cordis` 导入，也可以通过
`node --import @cordis-verus/compat-cordis/register app.mjs` 启动现有 Cordis 插件。
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

这些是允许的产物目标，不代表整个测试矩阵已经通过。
软件包要求 Node 22.22 或更高版本；Node-API 8 不构成对更早 Node 版本的验证。
Node 24、Windows、Linux ARM64 和 musl 尚未通过本实现的验收。
操作系统部署版本和最低 glibc 兼容性需要单独的发布测试。
每个实际产物都会记录加载它时使用的宿主操作系统版本、Node 版本、Node-API 和模块 ABI。
构建 profile 也会被记录，不会将开发构建悄悄标为经过优化的发布构建。

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
import { selectNativeArtifact, verifyNativeManifest } from '@cordis-verus/compat-cordis/native-artifacts'
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

## 生成 Release 产物

[`package-runtime-release.py`](../scripts/package-runtime-release.py)
复用现有的三个已独立安装验证的压缩包及原生构建来源记录。
它只接受与当前源码一致的完整发布验证记录，检查准确且有序的负控清单，绑定所有软件包与构建输入，
并要求源码提交保持干净；唯一允许的已跟踪文件差异是新生成的验证报告。
它保留真实的原生构建 profile，不会将开发构建悄悄称为优化构建。

[完整发布工作流](../.github/workflows/release-validation.yml)在三个平台上运行，
将每个暂存的运行时安装到新项目中，再执行一次离线 `npm ci` 并运行示例。
当显式使用 `create_draft=true` 和新的 `release_tag` 触发时，
工作流会收集三个平台上源码提交一致的产物，添加 `SHA256SUMS`，并创建**预发布草稿**。
任何平台失败都会阻止该任务运行。它拒绝使用已有标签，也不会自动发布草稿。
开发工作流不能上传运行时 Release。

工作流定义不等于执行证据。第一个运行时 Release 仍需要在其准确提交上通过完整质量验证，
并经过维护者审查。其余发布检查项见[发布流程](releasing.md)。
