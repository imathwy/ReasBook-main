# ReasBook

[English](README.md) | **简体中文**

**ReasBook** 是一个使用 Lean 4 对数学教材和研究论文进行形式化的项目。它在保留原始文献结构的同时，生成可由机器检查的命题与证明。你可以浏览已生成的[文档与项目目录](https://optpku.github.io/ReasBook/)，也可以按照下方的快速开始说明，仅检出一个形式化项目，而无需下载所有工具链分支。

许多 ReasBook 项目由 [M2F](https://github.com/optsuite/M2F.git) 初始化，随后在 Lean 中进行检查和完善。你也可以试用公开的自动形式化系统 [Quokka](https://quokka.reaslab.io/)；它可以将长篇数学文献转化为可编译的 Lean 4 项目。

## 工具链分支

| 分支 | Lean/mathlib | 注册状态 | 书籍/论文 |
| --- | --- | --- | ---: |
| `v4.32.0` | `v4.32.0` | 空 | 1 / 0 |
| `v4.32.2` | `v4.32.2` | 活跃 | 0 / 1 |
| `v4.30.0` | `v4.30.0` | 活跃 | 10 / 2 |
| `v4.26.0` | `v4.26.0` | 活跃 | 4 / 2 |

`main` 是跨版本目录。源代码保留在已注册的版本分支上；下方的轻量链接目录使每个条目都可以从 `main` 分支找到。

注册状态包括：`空`（不纳入活跃发布）、`活跃`（接受 PR 并纳入发布计划）、`冻结`（保留但不再接收新书）和 `归档`（仅保留历史记录）。数量统计的是源代码目录，因此 `空` 分支上的数量也可能不为零。

## main 分支索引目录

这些索引中的每个目录都是一本书或一篇论文的入口页。打开目录后，可以通过醒目的源代码链接进入精确的版本分支和项目目录。

- [书籍](https://github.com/optpku/ReasBook/tree/main/ReasBook/Books/)
- [论文](https://github.com/optpku/ReasBook/tree/main/ReasBook/Papers/)
- [定理依赖图](https://optpku.github.io/ReasBook/theorem-maps/)（当前 Pages 部署包含 TR-LALM）

## 架构

ReasBook 将带版本的数学源代码、跨版本工具和生成产物分开管理：

| 路径 | 职责 |
| --- | --- |
| `ReasBook/` | 位于对应版本分支上的 Lean 源代码 |
| `ReasBookWeb/` | Verso 站点外壳和目录生成 |
| `sdk/` | 可复用的构建、Verso、定理图、比较器和部署 API |
| `scripts/` | 仓库专用的轻量构建与 Pages 适配器 |
| `config/` | 工具链注册表、canonical 版本、发布配置和 schema |

生成的站点、Lake 产物、日志和发布状态均位于检出目录之外的指定缓存根目录中。Git 历史只保存源代码和配置，不保存生成站点。不可变发布与回滚模型记录在 [ADR-0001](docs/decisions/0001-static-release-pipeline.md) 中；SDK 依赖图和命令见 [sdk/README.md](sdk/README.md)。

## 快速开始：使用单个项目

你无需下载全部 ReasBook 项目，也无需获取每个工具链分支的完整历史。先在下方表格中找到目标书籍或论文，并记下其版本分支和项目目录；随后使用单分支稀疏检出，只下载共享 Lean 项目文件和选定的源代码目录。

以下示例从 `v4.30.0` 使用 *First-Order Methods in Optimization*：

```bash
git clone --depth 1 --filter=blob:none --no-checkout --single-branch \
  --branch v4.30.0 https://github.com/optpku/ReasBook.git
cd ReasBook
git sparse-checkout init --no-cone
git sparse-checkout set \
  '/ReasBook/lakefile.lean' \
  '/ReasBook/lean-toolchain' \
  '/ReasBook/lake-manifest.json' \
  '/ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/**'
git checkout v4.30.0
cd ReasBook
lake exe cache get
lake env lean Books/FirstOrderMethodsOptimization_Beck_2017/Book.lean
```

请将分支、`Books`/`Papers` 目录、项目标识符和 Lake 根文件替换为目标条目对应的值（书籍使用 `Book.lean`，论文使用 `Paper.lean`）。稀疏检出会避免下载该分支上的其他 ReasBook 源代码；Lake 仍会下载所需的 mathlib 依赖和编译缓存。正常克隆本仓库可以获取所有官方版本分支，但不会包含 GitHub forks 网络中的独立仓库。

## 书籍

点击标题可打开目录页；点击版本可直接打开 Lean 源代码。

| 形式化项目 | 源代码 | 贡献者 | 资源 |
| --- | :---: | --- | --- |
| **[A Concise Course in Algebraic Topology](ReasBook/Books/AlgebraicTopology_May_1999/)**<br><sub>J. Peter May (1999)</sub> | [`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/AlgebraicTopology_May_1999/) | Ze Yuan, Zichen Wang | [文档](https://optpku.github.io/ReasBook/docs/ReasBook/Books/AlgebraicTopology_May_1999/Book.html)<br>[Verso](https://optpku.github.io/ReasBook/sites/algebraictopology_may_1999/pages/) |
| **[Analysis II](ReasBook/Books/Analysis2_Tao_2022/)**<br><sub>Terence Tao (第 4 版，2022)</sub> | [`v4.26.0`](https://github.com/optpku/ReasBook/tree/v4.26.0/ReasBook/Books/Analysis2_Tao_2022/)<br>[`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/Analysis2_Tao_2022/) | <details><summary>9 位贡献者</summary><sub>Chenyi Li, Min Cui, Qiming Dai, Shu Miao, Wanli Ma, Yi Yuan, Zichen Wang, Ziyu Wang, Zaiwen Wen</sub></details> | [文档](https://optpku.github.io/ReasBook/docs/ReasBook/Books/Analysis2_Tao_2022/Book.html)<br>[Verso](https://optpku.github.io/ReasBook/sites/analysis2_tao_2022/pages/) |
| **[Combinatorial Group Theory](ReasBook/Books/CombinatorialGroupTheory_Magnus_2004/)**<br><sub>Magnus、Karrass 与 Solitar (2004)</sub> | [`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/CombinatorialGroupTheory_Magnus_2004/) | Zichen Wang | [文档](https://optpku.github.io/ReasBook/docs/ReasBook/Books/CombinatorialGroupTheory_Magnus_2004/Book.html)<br>[Verso](https://optpku.github.io/ReasBook/sites/combinatorialgrouptheory_magnus_2004/pages/) |
| **[Convex Analysis](ReasBook/Books/ConvexAnalysis_Rockafellar_1970/)**<br><sub>R. Tyrrell Rockafellar (1970)</sub> | [`v4.26.0`](https://github.com/optpku/ReasBook/tree/v4.26.0/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/) | <details><summary>21 位贡献者</summary><sub>Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, Zaiwen Wen</sub></details> | [文档](https://optpku.github.io/ReasBook/docs/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Book.html)<br>[Verso](https://optpku.github.io/ReasBook/sites/convexanalysis_rockafellar_1970/pages/) |
| **[Convex Analysis and Monotone Operator Theory in Hilbert Spaces](ReasBook/Books/ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017/)**<br><sub>Bauschke 与 Combettes (第 2 版，2017)</sub> | [`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017/) | Yifan Bai, Zichen Wang, Zaiwen Wen | [文档](https://optpku.github.io/ReasBook/docs/ReasBook/Books/ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017/Book.html)<br>[Verso](https://optpku.github.io/ReasBook/sites/convexanalysismonotoneoperators_bauschkecombettes_2017/pages/) |
| **[First-Order Methods in Optimization](ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/)**<br><sub>Amir Beck (2017)</sub> | [`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/) | Shu Miao, Zichen Wang, Zaiwen Wen | [文档](https://optpku.github.io/ReasBook/docs/ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/Book.html)<br>[Verso](https://optpku.github.io/ReasBook/sites/firstordermethodsoptimization_beck_2017/pages/) |
| **[Integer Programming](ReasBook/Books/IntegerProgramming_Conforti_2014/)**<br><sub>Conforti、Cornuejols 与 Zambelli (2014)</sub> | [`v4.26.0`](https://github.com/optpku/ReasBook/tree/v4.26.0/ReasBook/Books/IntegerProgramming_Conforti_2014/) | <details><summary>38 位贡献者</summary><sub>Binghe Huang, Chenglin Li, Chenrui Yang, Chenxi Liu, Congyuan Lei, Dongye Song, Fuzhi Wang, Haodong Zhang, Jiangnan Song, Jinmin Song, Junze Qiao, Junzhe Lai, Kaiwen He, Liming Han, Lurong Yang, Meng Zhou, Pengqi Lei, Renran Luo, Siyan Chen, Wangqi Liu, Wenxin Zeng, Wanli Ma, Wenxuan Wu, Xinru Zhu, Xu Han, Xutianshi Tao, Yichao Guo, Youyou Qin, Yuhan Zhang, Yushen Guo, Yutong Zhang, Ze Zhai, Zheng Ma, Zhiyong Chen, Zichen Wang, Zichen Xu, Zihao Liu, Zaiwen Wen</sub></details> | [文档](https://optpku.github.io/ReasBook/docs/ReasBook/Books/IntegerProgramming_Conforti_2014/Book.html)<br>尚未发布 Verso |
| **[Introduction to Real Analysis, Volume I](ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/)**<br><sub>Jiri Lebl (v6.2，2025)</sub> | [`v4.26.0`](https://github.com/optpku/ReasBook/tree/v4.26.0/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/)<br>[`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/) | Zichen Wang, Zaiwen Wen | [文档](https://optpku.github.io/ReasBook/docs/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Book.html)<br>[Verso](https://optpku.github.io/ReasBook/sites/introductiontorealanalysisvolumei_jirilebl_2025/pages/) |
| **[Introductory Lectures on Convex Optimization](ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/)**<br><sub>Yurii Nesterov (2004)</sub> | [`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/) | Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long | [文档](https://optpku.github.io/ReasBook/docs/ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/Book.html)<br>[Verso](https://optpku.github.io/ReasBook/sites/introductorylecturesonconvexoptimization_nesterov_2004/pages/) |
| **[Optimization Theory and Methods: Nonlinear Programming](ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/)**<br><sub>Wenyu Sun 与 Ya-xiang Yuan (2006)</sub> | [`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/) | Chenyi Li, Wanli Ma, Zichen Wang | [文档](https://optpku.github.io/ReasBook/docs/ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/Book.html)<br>[Verso](https://optpku.github.io/ReasBook/sites/optimizationtheoryandmethods_sunyuan_2006/pages/) |
| **[Probability Theory: A Comprehensive Course](ReasBook/Books/ProbabilityTheory_Klenke_2020/)**<br><sub>Achim Klenke (第 3 版，2020)</sub> | [`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/ProbabilityTheory_Klenke_2020/) | Xuanzhi Ren, Zichen Wang | 仅源代码（不包含在当前发布配置中） |
| **[Lectures on Riemann Surfaces](ReasBook/Books/RiemannSurfaces_Forster_1981/)**<br><sub>Otto Forster (1981)</sub> | [`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/RiemannSurfaces_Forster_1981/) | Zichen Wang | [文档](https://optpku.github.io/ReasBook/docs/ReasBook/Books/RiemannSurfaces_Forster_1981/Book.html)<br>[Verso](https://optpku.github.io/ReasBook/sites/riemannsurfaces_forster_1981/pages/) |
| **[Computational Methods for Inverse Problems](ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/)**<br><sub>Curtis R. Vogel (2002)</sub> | 未分配到活跃发布分支 | Yifan Bai, Wanli Ma, Zichen Wang | 仅源代码（不包含在当前发布配置中） |

## 论文

点击标题可打开目录页；点击版本可直接打开 Lean 源代码。

| 形式化项目 | 源代码 | 贡献者 | 资源 |
| --- | :---: | --- | --- |
| **[A Fixed-Penalty Linearized Augmented Lagrangian Method with Classical Multiplier Updates](ReasBook/Papers/TR_LALM_theory/)**<br><sub>Benqi Liu、Kangkang Deng、Zichen Wang 与 Zaiwen Wen</sub> | [`v4.32.2`](https://github.com/optpku/ReasBook/tree/v4.32.2/ReasBook/Papers/TR_LALM_theory/) | Zichen Wang, Zaiwen Wen | [文档](https://optpku.github.io/ReasBook/docs/ReasBook/Papers/TR_LALM_theory/Paper.html)<br>[Verso](https://optpku.github.io/ReasBook/sites/tr_lalm_theory/pages/)<br>[定理图](https://optpku.github.io/ReasBook/theorem-maps/papers/tr_lalm_theory/) |
| **[Smooth Minimization of Non-Smooth Functions](ReasBook/Papers/SmoothMinimization_Nesterov_2004/)**<br><sub>Yurii Nesterov (2004)</sub> | [`v4.26.0`](https://github.com/optpku/ReasBook/tree/v4.26.0/ReasBook/Papers/SmoothMinimization_Nesterov_2004/)<br>[`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Papers/SmoothMinimization_Nesterov_2004/) | Wanli Ma, Zichen Wang, Zaiwen Wen | [文档](https://optpku.github.io/ReasBook/docs/ReasBook/Papers/SmoothMinimization_Nesterov_2004/Paper.html)<br>[Verso](https://optpku.github.io/ReasBook/sites/smoothminimization_nesterov_2004/pages/) |
| **[On Some Local Rings](ReasBook/Papers/OnSomeLocalRings_Maassaran_2025/)**<br><sub>Mohamad Maassarani (2025)</sub> | [`v4.26.0`](https://github.com/optpku/ReasBook/tree/v4.26.0/ReasBook/Papers/OnSomeLocalRings_Maassaran_2025/)<br>[`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Papers/OnSomeLocalRings_Maassaran_2025/) | Liang Xiao, Haochen Ju, Zichen Wang, Zaiwen Wen | [文档](https://optpku.github.io/ReasBook/docs/ReasBook/Papers/OnSomeLocalRings_Maassaran_2025/Paper.html)<br>[Verso](https://optpku.github.io/ReasBook/sites/onsomelocalrings_maassaran_2025/pages/) |

## 贡献指南

参见 [CONTRIBUTING.md](CONTRIBUTING.md)。

- 书籍和论文代码位于与其 Lean/mathlib 工具链相匹配的已注册版本分支；仅接受已注册的稳定 `vX.Y.Z` 版本。
- **书籍和论文代码不合并到 `main`。** `main` 始终作为跨版本目录，其中的链接目录指向对应版本分支。
- PR 的目标分支、PR 标题中的版本、`ReasBook/lean-toolchain` 和书籍元数据（如适用）必须完全一致。

## 构建

完整的多版本 Lean 和文档构建在 SiFlow 上运行，并且只写入外部缓存。以下本地命令适用于针对性开发和预览，不用于生成公开发布：

```bash
./scripts/build/all.sh                 # 缓存、核心和可选文档
BUILD_DOCS=0 ./scripts/build/all.sh    # 快速、仅构建核心
./scripts/build/site.sh                # 完整流水线及 Verso 站点
./sdk/common/bin/python ./scripts/preview/serve.py 18000
                                        # http://127.0.0.1:18000/ReasBook/
```

部署工具要求 Python 3.11 或更高版本。如果 `python3` 指向较旧的系统解释器，请先运行 `./sdk/deploy/bin/reasbook-deploy ci verify-python`，然后在本地命令中使用其报告的 `REASBOOK_PYTHON_BIN`。

### 一条命令部署选定书目

在工作区根目录运行部署命令，可以对一到两个项目进行可复现的本地构建：

```bash
./sdk/deploy/bin/reasbook-deploy \
  --book IntroductiontoRealAnalysisVolumeI_JiriLebl_2025 \
  --book Analysis2_Tao_2022 \
  --no-build \
  --serve
```

该命令会选择匹配的稳定版本分支，在 `/volume/math/users/zcwang/ReasBook_Reviewer/cache/reasbook/sources/` 下创建 detached 稀疏 worktree，按需安装分支工具链，并将所有 Lake、package 和 native 产物存放在 `/volume/math/users/zcwang/ReasBook_Reviewer/cache/reasbook/lake/` 下。它只向同级 reviewer 写入轻量评审索引，并在 `/volume/math/users/zcwang/ReasBook_Reviewer/cache/reasbook/manifests/` 下记录原子 manifest。如使用其他磁盘，请通过 `REASBOOK_CACHE_ROOT` 或 `--cache-root` 显式覆盖缓存根目录。

首次运行建议使用 `--no-build`：它只生成轻量声明索引，不要求 Lean 缓存。需要本地 Lean 构建时再移除该选项。使用 `--dry-run` 可查看计划；仅在需要文档时传入 `--build-docs`；使用 `--serve` 可在构建后启动基于 Python 3.11+ 的 reviewer。Stacks 条目默认进入索引，但其大型 Lean 构建只有在传入 `--build-stacks` 时才会执行。使用 `--serve` 时，默认 host 和 port 从 reviewer 的 `.env` 读取；可用 `--host`/`--port` 覆盖。

如需静态 Docker 部署，请运行 `./sdk/deploy/bin/reasbook-deploy docker`。该命令会先构建并验证生成站点，再以 `--remove-orphans` 启动 Compose，并持续检查公开端口，成功后才退出。站点默认位于 `http://127.0.0.1:3200/ReasBook/`。`--skip-build` 可复用现有站点，`--port` 可更改宿主机端口。

### 不可变静态发布

在不构建的情况下解析所有活跃版本分支和显式 canonical 项目：

```bash
./sdk/deploy/bin/reasbook-deploy release plan \
  --profile github-pages --new-release --fetch
```

生产发布流程会锁定每个输入，在 SiFlow 上运行项目构建和分支 finalizer，然后在本地组装一个经过验证的站点。打包阶段从同一次构建派生两类制品：

| 制品 | 内容 | 部署目标 |
| --- | --- | --- |
| `pages` | 目录、canonical 项目、可达的项目模块 API 文档、Verso、定理图和依赖占位页 | 临时 GitHub Pages 主机 |
| `full` | 所有项目版本，以及采用相同边界且链接闭合的项目模块文档 | 项目自有静态服务器 |

`release-set.json` 将两个归档及其站点树摘要绑定到同一个不可变 `ReleaseSpec`。GitHub Actions 只下载、验证和部署较小的 `pages` 归档，绝不构建 Lean 或文档。参见 [ADR-0001](docs/decisions/0001-static-release-pipeline.md) 和 [ADR-0002](docs/decisions/0002-target-specific-release-artifacts.md)。

对于每个配置的入口根模块，API 文档只沿 import 遍历项目自身的 Lean 模块，每批最多处理 128 个模块。Mathlib、Lean 和其他外部库均不包含在内；被引用的外部 HTML 页面会变成显式占位页，使静态站点的链接保持闭合。不可变的 `project-modules-v2` 缓存身份使重试能够复用完全相同的先前结果。

以下命令假设 `RELEASE_ID` 在发布缓存中已经完成 aggregate 的 `site` 阶段。默认缓存为 `/volume/math/users/zcwang/ReasBook_Reviewer/cache/reasbook`；可通过 `REASBOOK_CACHE_ROOT` 或 `--cache-root` 覆盖。只有分支级 Lean 缓存还不能打包为发布制品：必须先完成 aggregate 阶段，并使用 `release status` 确认。

```bash
RELEASE_ID="${RELEASE_ID:?set RELEASE_ID to the generated release ID}"
./sdk/deploy/bin/reasbook-deploy release status "$RELEASE_ID"
./sdk/deploy/bin/reasbook-deploy release package "$RELEASE_ID"
./sdk/deploy/bin/reasbook-deploy release validate "$RELEASE_ID" \
  --browser-mode required
./sdk/deploy/bin/reasbook-deploy release preview "$RELEASE_ID" --artifact pages
./sdk/deploy/bin/reasbook-deploy release publish "$RELEASE_ID" \
  --target github-pages --wait
```

必需的验证步骤不会重新构建 Lean 或文档。它会检查受限的 Pages 归档、完整的 full 归档和一次原子自托管安装，其中包括有代表性的桌面端与移动端浏览器路由。在使用这一发布门禁前，请按照[部署 SDK 指南](sdk/deploy/README.md)安装可选浏览器运行时。

发布需要已认证的 GitHub CLI。`release deploy` 命令仍可用于通过一个或多个 `--only` 选项选择的小型本地 canary，但不得用它执行完整的公开多版本构建。对所有活跃项目执行非 dry-run 本地构建时，默认会拒绝继续，除非操作员显式添加 `--allow-local-all-active-build`。使用 `--no-publish` 可在本地打包后停止；使用 `--dry-run` 可只解析 spec 而不创建发布状态。详见 [`sdk/deploy/release/README.md`](sdk/deploy/src/reasbook_deploy_sdk/release/README.md)。

#### 预览精确的发布制品

打包完成后，CLI 会在提供服务前同时验证归档 checksum 和站点树摘要，不会重新构建任何内容：

```bash
export REASBOOK_CACHE_ROOT=/path/to/reasbook-cache
RELEASE_ID="${RELEASE_ID:?set RELEASE_ID to the generated release ID}"
./sdk/deploy/bin/reasbook-deploy release preview "$RELEASE_ID" \
  --artifact pages --host 127.0.0.1 --port 18000
```

打开 `http://127.0.0.1:18000/ReasBook/`。这里提供的是经过验证并打包的 Pages 站点树，而不是某个中间分支构建。使用 `--artifact full` 可以检查精确的自托管候选版本。通过工作区代理访问时，请添加 `--host 0.0.0.0 --public-prefix /path/to/proxy/18000`。发布预览与验收使用严格的生产路由：不带前缀的 `/books/`、`/papers/`、`/docs/` 和 `/static/` 路径返回 404，`/ReasBook` 永久重定向到 `/ReasBook/`。

#### GitHub Pages 容量与发布

如果 `pages` 制品在本地打包时超过 850 MB、60,000 个文件、180,000 个归档成员或压缩后 950 MB，打包会失败。本地打包、验收和发布 workflow 都从仓库中的 `github-pages` profile 加载这些限制；workflow 不会使用更宽松的硬编码成员上限，并会在解压前重复检查归档目录。`.nojekyll` 和 `.well-known/` 等隐藏站点内容会被保留并计入经过验证的站点树摘要。路径中精确的 `.git` 和 `.github` 段会被拒绝，因为 Pages 上传 action 会排除它们，否则上传后的站点树将不同于本地验证结果。这些余量确保站点低于 GitHub Pages 的 1 GB 和 10 分钟部署限制；仅靠压缩不能让过大的站点变得合规。

当部署 workflow 已进入默认分支后，执行一次仓库边界配置和审计：

```bash
./sdk/deploy/bin/reasbook-deploy release configure-pages \
  --profile github-pages --dry-run
./sdk/deploy/bin/reasbook-deploy release configure-pages \
  --profile github-pages
```

该命令只补充缺失的 workflow-based Pages 设置，启用仓库不可变 Release，并只允许精确的默认分支使用 `github-pages` environment。因此，用于审计的 token 需要仓库 Administration 读取权限，用于启用设置时还需要写入权限。命令不会隐式改写现有自定义域名，也不会删除额外的分支策略。如果检查发现精确的默认分支策略之外只有一条过时策略，请同时提供该记录的三个不可变预期值来仅删除这一条记录；先执行 dry run，再原样执行：

```bash
./sdk/deploy/bin/reasbook-deploy release configure-pages \
  --profile github-pages --remove-policy-id 123456 \
  --expected-policy-name v4.30.0 --expected-policy-type branch --dry-run
./sdk/deploy/bin/reasbook-deploy release configure-pages \
  --profile github-pages --remove-policy-id 123456 \
  --expected-policy-name v4.30.0 --expected-policy-type branch
```

命令会先获取并精确比较数字 ID、名称和类型，然后才调用单策略 DELETE 端点。它拒绝删除默认分支，拒绝歧义或多策略清理，并会再次获取策略以证明最终只剩默认分支。仓库设置可能具有最终一致性：启用不可变 Release 后，命令会每五秒轮询一次，最多等待 300 秒，超时则安全失败。可使用 `--immutable-convergence-timeout-seconds` 和 `--immutable-convergence-poll-seconds` 调整这一有界等待；两者都必须为正有限值，轮询间隔不得小于一秒且不得大于超时时间。

```bash
./sdk/deploy/bin/reasbook-deploy release publish "$RELEASE_ID" \
  --target github-pages --wait
```

该命令首先读取 `cache/reasbook/validation/<release-id>/latest.json` 中成功且启用必需浏览器检查的验收记录，dry run 也使用同一门禁。随后，它将 Pages 归档、manifest、checksum 和 ReleaseSet 上传到不可变 GitHub Release；只有 GitHub 报告该 Release 已不可变后，才触发锁定版本的纯发布 workflow。workflow 会先使用 GitHub Release 和逐制品验证命令，再部署包含隐藏文件的精确站点树。其 verify job 仅具有只读级别的 contents、Pages 和 artifact-attestation 权限，并且只安装固定版本的 PyYAML 验证依赖。

使用 `--wait` 时，成功不仅意味着 Actions workflow 为绿色：发布器还会等待公开的 `/ReasBook/release-spec.json` 收敛，并精确匹配预期 release ID、ReleaseSpec 摘要和 registry commit。Actions 默认最多等待 1,800 秒，之后的 CDN 收敛默认最多等待 300 秒；后者可用 `--pages-health-timeout-seconds` 调整。公开站点陈旧或不可访问时会安全失败，且不会被记录为 `published`。

本地上传和 GitHub workflow 都不会运行 Lean、Verso、doc-gen 或 theorem-graph，也不会传输任何 Lean 缓存。因此，墙钟时间主要由 Pages 归档大小与上行带宽、Actions 排队、一次下载/解压/上传以及 GitHub Pages 部署决定；CPU 只用于哈希、验证和解压。workflow 的 30 分钟 verify 和 10 分钟 deploy 限制是失败上限，而非预期耗时。本地 Release 上传另有两小时超时，因此接近 950 MB 上限的有效归档不会被常规五分钟 GitHub API 命令上限终止。

这是在完成打包、必需验证、认证和一次性 `configure-pages` 设置之后的一条命令晋级流程。它有意不提供从源码到生产的一键构建：完整 SiFlow 构建和 aggregate 阶段仍保持显式，并可独立重试。

对于新 Release，还要求检出目录干净，且 `HEAD` 同时精确匹配 GitHub 默认分支和 ReleaseSpec 的 `source.registry_commit`。因此，请先合并并拉取部署变更，再执行发布。带 dirty 标记的 tooling revision 仍可用于本地 canary，但 GitHub 发布器只接受干净的 `COMMIT+tooling-sha256:DIGEST` 形式。发布器先创建精确 Git ref，再使用 Releases REST API 创建并发布 draft，并在上传、发布和 dispatch 之前重新核对完全解引用后的 tag。这样无需依赖仓库所支持 GitHub CLI 2.4 中不存在的 release flags。已存在或并发创建的 tag 只有在解析到同一 commit 时才会被接受。

workflow 会从归档内的 ReleaseSpec 再次检查源 commit 和干净 tooling，并根据检出的默认分支版本中可信的 profile 重新计算制品策略摘要。因此，策略变化后不能再次 dispatch 原有 release；应创建并验证新的 ReleaseSpec。除此之外，再次 dispatch 现有不可变 tag 不依赖调用者当前所在分支。参见官方 [GitHub Pages 限制](https://docs.github.com/en/pages/getting-started-with-github-pages/github-pages-limits)和 [GitHub Release 限制](https://docs.github.com/en/repositories/releasing-projects-on-github/about-releases)。

#### 在自有服务器上部署完整站点

先进行一次 Web 服务器配置，将 `/srv/reasbook/current/public` 设为 document root；仓库提供了可直接使用的 Nginx 示例：[`config/deploy/nginx-self-hosted.conf`](config/deploy/nginx-self-hosted.conf)。然后可以直接从共享发布缓存部署：

```bash
./sdk/deploy/bin/reasbook-deploy release publish "$RELEASE_ID" \
  --target self-hosted --deploy-root /srv/reasbook \
  --health-url http://127.0.0.1/ReasBook/release-spec.json
```

也可以传输 full 归档和 `release-set.json`。传输之前，在可信构建主机上记录该归档针对当前 release 的 SHA-256，并通过独立的认证通道将该值交给操作员，例如带签名的部署记录。同时记录经过审核的 profile 所对应的制品策略摘要：

```bash
POLICY_SHA256="$(./sdk/deploy/bin/reasbook-deploy release \
  --repo-root . policy-digest --profile github-pages)"
CACHE_ROOT="${REASBOOK_CACHE_ROOT:-/volume/math/users/zcwang/ReasBook_Reviewer/cache/reasbook}"
FULL_BUNDLE="$CACHE_ROOT/releases/$RELEASE_ID/$RELEASE_ID.site.tar.zst"
FULL_SHA256="$(sha256sum "$FULL_BUNDLE" | awk '{print $1}')"
printf 'release=%s\nfull_sha256=%s\npolicy_sha256=%s\n' \
  "$RELEASE_ID" "$FULL_SHA256" "$POLICY_SHA256"
```

目标服务器不需要源代码检出目录或发布缓存：

```bash
RELEASE_ID="${RELEASE_ID:?set RELEASE_ID to the generated release ID}"
POLICY_SHA256="${POLICY_SHA256:?set the trusted sha256 artifact-policy digest}"
FULL_SHA256="${FULL_SHA256:?set the independently authenticated full-bundle SHA-256}"
FULL_BUNDLE="${RELEASE_ID}.site.tar.zst"
reasbook-deploy release install \
  "$FULL_BUNDLE" --expected-bundle-sha256 "$FULL_SHA256" \
  --release-set release-set.json \
  --artifact-policy-sha256 "$POLICY_SHA256" \
  --deploy-root /srv/reasbook \
  --health-url http://127.0.0.1/ReasBook/release-spec.json
```

这里传输并安装的是与 Pages bundle 同时生成的同一个 `full` bundle。Web 服务器和信任输入配置完成后，只需一次 `release install` 调用即可完成验证和原子激活；它不会重新构建站点。

两个信任输入都应在可信构建/发布端记录；不要根据随归档一起传输的 `SHA256SUMS` 文件推导 `FULL_SHA256`。共同传输的 checksum 只适合诊断，不能认证 release。`POLICY_SHA256` 用于验证部署策略，但它通常在不同 release 间保持稳定，因此也不能认证 release 身份。安装程序会先根据 `release-set.json` 绑定并验证独立认证的 full-bundle checksum、站点摘要、数量、ReleaseSpec 和制品策略，之后才创建部署根目录。随后它会写入带版本目录，原子切换 `current`；健康检查失败时恢复上一个 release。无需重新构建即可回滚：

```bash
./sdk/deploy/bin/reasbook-deploy release rollback \
  --target self-hosted --deploy-root /srv/reasbook --to "$RELEASE_ID" \
  --health-url http://127.0.0.1/ReasBook/release-spec.json
```

对于 `publish --target self-hosted` 和 `rollback --target self-hosted`，CLI parser 要求精确提供 `--health-url` 或 `--filesystem-health-only` 二者之一，即使 dry run 也不例外。这样在读取发布状态之前，就可以明确看到预期的切换后验证模式。

对于容器化服务器，先使用 `--filesystem-health-only` 完成首次安装，再启动专用的生产 Compose 项目；无需重新构建站点：

```bash
RELEASE_ID="${RELEASE_ID:?set RELEASE_ID to the generated release ID}"
POLICY_SHA256="${POLICY_SHA256:?set the trusted sha256 artifact-policy digest}"
FULL_SHA256="${FULL_SHA256:?set the independently authenticated full-bundle SHA-256}"
FULL_BUNDLE="${RELEASE_ID}.site.tar.zst"
reasbook-deploy release install \
  "$FULL_BUNDLE" --expected-bundle-sha256 "$FULL_SHA256" \
  --release-set release-set.json \
  --artifact-policy-sha256 "$POLICY_SHA256" \
  --deploy-root /srv/reasbook \
  --filesystem-health-only
REASBOOK_DEPLOY_ROOT=/srv/reasbook \
  docker compose -f docker-compose.self-hosted.yml up -d --wait
```

容器挂载稳定的部署根目录，因此后续原子切换 `current` 后无需重启 Nginx 即可生效。该配置独立于 `docker-compose.yml`；后者仍用于本地生成站点预览。

### 实现布局

仓库适配器按职责归类在 `scripts/` 下，不存在顶层脚本 wrapper。可复用的 Python、Lake、工具链、外部缓存、重试、心跳、定理图和部署行为均位于 `sdk/` 下。CI 和本地自动化直接调用 SDK 入口。

可复用构建工具分别维护在 `sdk/` 下：`build`、`verso`、`theorem_graph` 和 `comparator` 各自提供 typed API、CLI、测试和 README。它们都依赖 `sdk/common` 中与平台无关的基础能力；`sdk/deploy` 是多阶段构建的编排层。依赖图和安装顺序见 [sdk/README.md](sdk/README.md)，仓库适配边界见 [scripts/README.md](scripts/README.md)。

## 赞助单位

- 北京大学北京国际数学研究中心
- 大湾区大学
- 华为
- iQuest Research
- 中俄数学中心
- 国家自然科学基金委员会

## Lean 项目

### 形式化平台

- [ReasLab](https://reaslab.io)
  - 用于协作式定理开发和验证的在线 Lean 形式化平台。

### 形式化项目

- [Optlib](https://github.com/optsuite/optlib)
  - 面向数学优化的 Lean 4 库，涵盖凸分析、最优性条件和算法收敛性。
- [ReasBook](https://github.com/optpku/ReasBook)
  - 面向教材和论文形式化的 Lean 4 项目，同时覆盖定理证明和计算问题。

### 基准测试

- [AMBER](https://github.com/optsuite/AMBER)
  - 面向应用数学形式化中构造与验证任务的 Lean 4 基准，同时覆盖定理证明和计算问题。
- [CAM-Bench](https://github.com/optpku/CAM-Bench)
  - 面向计算与应用数学形式化定理证明的 Lean 4 基准。

### 自动形式化与定理证明系统

- [M2F](https://github.com/optsuite/M2F)
  - 将自然语言数学教材转换为可进行形式化的 Lean 项目的工具包。
- [SITA](https://github.com/chenyili0818/SITA)
  - 一种结构到实例的自动形式化框架，利用验证反馈生成 Lean 定义和定理。
- [lean-tools-mcp](https://github.com/optsuite/lean-tools-mcp)
  - Lean MCP 服务器，在重型 import（尤其是 Mathlib）场景中提供更高并行吞吐和更低内存占用。

## 研究成果

### 数学形式化

- Wanli Ma, Zichen Wang, Zaiwen Wen, *A Unified Framework for Formalizing Matrix Decomposition Proofs*. [(论文)](https://arxiv.org/abs/2607.05874)
- Chenyi Li, Ziyu Wang, Wanyi He, Yuxuan Wu, Shengyang Xu, Zaiwen Wen. *Formalization of Complexity Analysis of the First-order Optimization Algorithms*, Journal of Automated Reasoning. [(论文)](https://arxiv.org/abs/2403.11437)
- Chenyi Li, Zichen Wang, Yifan Bai, Yunxi Duan, Yuqing Gao, Pengfei Hao, Zaiwen Wen. *Formalization of Algorithms for Optimization with Block Structures*, Science in China Series A: Mathematics. [(论文)](http://arxiv.org/abs/2503.18806)
- Chenyi Li, Shengyang Xu, Chumin Sun, Li Zhou, Zaiwen Wen. *Formalization of Optimality Conditions for Smooth Constrained Optimization Problems*. [(论文)](https://arxiv.org/abs/2503.18821)
- Chenyi Li, Zaiwen Wen. *An Introduction to Mathematics Formalization Based on Lean*. [(论文)](http://faculty.bicmr.pku.edu.cn/~wenzw/paper/OptLean.pdf)

### 自动形式化与自动定理证明

- Wentao Long, Yunfei Zhang, Chenyi Li, Zaiwen Wen, *MECA: A Mechanism-Centered Agent for Constructing Well-Specified and Valuable Mathematical Conjectures*. [(论文)](https://arxiv.org/abs/2607.27709)
- Chenyi Li, Yanchen Nie, Zhenyu Ming, Gong Zhang, Kun Yuan, Zaiwen Wen. *OptProver: Bridging Olympiad and Optimization through Continual Training in Formal Theorem Proving*, ICML 2026. [(论文)](https://arxiv.org/abs/2604.23712)
- Zichen Wang, Wanli Ma, Zhenyu Ming, Gong Zhang, Kun Yuan, Zaiwen Wen. *M2F: Automated Formalization of Mathematical Literature at Scale*. [(论文)](https://arxiv.org/abs/2602.17016)
- Ziyu Wang, Bowen Yang, Chenyi Li, Yuan Zhang, Shihao Zhou, Bin Dong, Zaiwen Wen. *Translating Informal Proofs into Formal Proofs Using a Chain of States*. [(论文)](https://arxiv.org/abs/2512.10317)
- Chenyi Li, Wanli Ma, Zichen Wang, Zaiwen Wen. *SITA: A Framework for Structure-to-Instance Theorem Autoformalization*, AAAI 2026. [(论文)](https://arxiv.org/abs/2511.10356)

### 定理证明检查

- Ziyu Wang, Qiming Dai, Yishan Wu, Zaiwen Wen. *FaithSieve: Fine-Grained Evaluation of Math Proofs with Faithful Formal Evidence*.
- Ziyu Wang, Qiming Dai, Chenyi Li, Zaiwen Wen, *Beyond Formal Correctness: Structure-Aware Evaluation of Informal–Formal Proof Correspondence*

### 前提选择

- Zichen Wang, Anjie Dong, Zaiwen Wen. *Tree-Based Premise Selection for Lean4*, NeurIPS 2025. [(论文)](https://neurips.cc/virtual/2025/loc/san-diego/poster/116011)
- Shu Miao, Zichen Wang, Anjie Dong, Yishan Wu, Weixi Zhang, Zaiwen Wen. *Directed Multi-Relational GCNs for Premise Selection*.

### 基准测试

- Bowen Yang, Yi Yuan, Chenyi Li, Ziyu Wang, Liangqi Li, Bo Zhang, Zhe Li, Zaiwen Wen. *Construction-Verification: A Benchmark for Formalizing Applied Mathematics in Lean 4*. [(论文)](https://arxiv.org/abs/2602.01291)
- Wentao Long, Yunfei Zhang, Chenyi Li, Li Zhou, Chumin Sun, Zaiwen Wen. *CAM-Bench: A Benchmark for Computational and Applied Mathematics in Lean*. [(论文)](https://arxiv.org/abs/2605.17255)

## 贡献者

- Chenyi Li，北京大学数学科学学院，中国（`lichenyi@stu.pku.edu.cn`）
- Wanli Ma，北京大学北京国际数学研究中心，中国（`wlma@pku.edu.cn`）
- Zichen Wang，北京大学数学科学学院，中国（`zichenwang25@stu.pku.edu.cn`）
- Ziyu Wang，北京大学数学科学学院，中国（`wangziyu-edu@stu.pku.edu.cn`）
- Zaiwen Wen，北京大学北京国际数学研究中心，中国（`wenzw@pku.edu.cn`）
- Yifan Bai, Anjie Dong, Yunxi Duan, Xinyi Guo, Pengfei Hao, Yuhao Jiang, Gongxun Li, Yantao Li, Wentao Long, Zebo Liu, Zhenxi Liu, Siyuan Ma, Guangxuan Pan, Siyuan Shao, Weiran Shi, Junren Si, Xuran Sun, Xuan Tang, Feiming Wang, Yijie Wang, Zhiyan Wang, Zixi Wang, Suwu Wu, Mingyue Xu, Lurong Yang, Yunfei Zhang, Jian Yu, Changyun Zou

## 引用

如果你使用 ReasBook，请同时引用 M2F 论文和本仓库。

M2F 论文：

```bibtex
@misc{wang2026m2f,
  author        = {Zichen Wang and Wanli Ma and Zhenyu Ming and Gong Zhang and
                   Kun Yuan and Zaiwen Wen},
  title         = {{M2F}: Automated Formalization of Mathematical Literature at Scale},
  year          = {2026},
  eprint        = {2602.17016},
  archivePrefix = {arXiv},
  primaryClass  = {cs.AI},
  doi           = {10.48550/arXiv.2602.17016},
  url           = {https://arxiv.org/abs/2602.17016}
}
```

ReasBook 软件：

```bibtex
@software{reasbook2026,
  author  = {{ReasBook Contributors}},
  title   = {{ReasBook}: Formalizations of Mathematical Textbooks and
             Research Papers in {Lean 4}},
  year    = {2026},
  url     = {https://github.com/optpku/ReasBook},
  license = {Apache-2.0}
}
```

引用某个具体形式化项目时，还应引用原始书籍或论文，并记录 ReasBook 项目目录、版本分支和完整 commit SHA。例如：`v4.30.0`、`ReasBook/Books/<project>/`，以及 `git rev-parse HEAD` 的输出。本仓库还提供 [`CITATION.cff`](CITATION.cff)，供引用工具和 GitHub 引用界面使用。

## 许可证

ReasBook 使用与 mathlib 一致的 [Apache License 2.0](LICENSE)。除非单个文件另有声明，该许可证适用于 ReasBook 在所有官方分支上的内容，以及由本仓库派生的所有副本和 fork。各 fork 的新增内容和第三方依赖仍受其各自许可证声明约束。
