# ReasBook

**ReasBook** is a Lean 4 project for formalizing mathematics from textbooks
and research papers. It preserves the structure of the original references
while producing machine-checkable statements and proofs. Browse the generated
[documentation and project catalog](https://optpku.github.io/ReasBook/), or
use the quick start below to check out one formalization without downloading
every toolchain branch.

Many ReasBook projects are initialized with
[M2F](https://github.com/optsuite/M2F.git) and then checked and refined in
Lean. You can also try [Quokka](https://quokka.reaslab.io/), the public
automated formalization system for turning long-form mathematical literature
into compilable Lean 4 projects.

## Toolchain Branches

| Branch | Lean/mathlib | Registry status | Books/Papers |
| --- | --- | --- | ---: |
| `v4.32.0` | `v4.32.0` | Empty | 1 / 0 |
| `v4.32.2` | `v4.32.2` | Active | 0 / 1 |
| `v4.30.0` | `v4.30.0` | Active | 10 / 2 |
| `v4.26.0` | `v4.26.0` | Active | 4 / 2 |

`main` is the cross-version catalog. The source code stays on the registered version branches; the lightweight link folders below make each entry discoverable from this branch.

Registry status: `Empty` (not included in active releases) · `Active`
(accepting PRs and included in release planning) · `Frozen` (kept, no new
books) · `Archived` (historical only). Counts describe source directories and
therefore may be nonzero on an `Empty` branch.

## Main-branch Link Folders

Each directory in these indexes is a landing page for one book or paper. Open a directory and follow its prominent source link to the exact version branch and project folder.

- [Books](https://github.com/optpku/ReasBook/tree/main/ReasBook/Books/)
- [Papers](https://github.com/optpku/ReasBook/tree/main/ReasBook/Papers/)
- [Theorem dependency maps](https://optpku.github.io/ReasBook/theorem-maps/)
  (the current Pages deployment contains TR-LALM)

## Architecture

ReasBook separates versioned mathematical sources from cross-version tooling
and generated output:

| Path | Responsibility |
| --- | --- |
| `ReasBook/` | Lean sources on their matching version branches |
| `ReasBookWeb/` | Verso site shell and catalog generation |
| `sdk/` | Reusable build, Verso, theorem-graph, comparator, and deployment APIs |
| `scripts/` | Thin repository-specific build and Pages adapters |
| `config/` | Toolchain registry, canonical versions, release profiles, and schemas |

Generated sites, Lake artifacts, logs, and release state live outside the
checkout under the configured cache root. Git history contains source and
configuration, not generated sites. The immutable release and rollback model
is recorded in [ADR-0001](docs/decisions/0001-static-release-pipeline.md); the
SDK dependency graph and commands are in [sdk/README.md](sdk/README.md).

## Quick Start: Use One Project

You do not need to download every ReasBook project or the history of every
toolchain branch. First find the book or paper in the tables below and note its
version branch and project directory. A single-branch sparse checkout can then
download the shared Lean project files and only the selected source directory.

For example, to use *First-Order Methods in Optimization* from `v4.30.0`:

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

Replace the branch, `Books`/`Papers` directory, project identifier, and Lake
root file with those of the selected entry (`Book.lean` for a book and
`Paper.lean` for a paper). Sparse checkout avoids downloading the other
ReasBook sources on that branch; Lake still downloads the required mathlib
dependencies and compiled cache. A normal clone of this repository can fetch
all official version branches, but it does not include independent repositories
in GitHub's forks network.

## Books

Titles open their catalog pages; version links open the Lean source directly.

| Formalization | Source | Contributors | Resources |
| --- | :---: | --- | --- |
| **[A Concise Course in Algebraic Topology](ReasBook/Books/AlgebraicTopology_May_1999/)**<br><sub>J. Peter May (1999)</sub> | [`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/AlgebraicTopology_May_1999/) | Ze Yuan, Zichen Wang | [Docs](https://optpku.github.io/ReasBook/docs/ReasBook/Books/AlgebraicTopology_May_1999/Book.html)<br>[Verso](https://optpku.github.io/ReasBook/sites/algebraictopology_may_1999/pages/) |
| **[Analysis II](ReasBook/Books/Analysis2_Tao_2022/)**<br><sub>Terence Tao (4th ed., 2022)</sub> | [`v4.26.0`](https://github.com/optpku/ReasBook/tree/v4.26.0/ReasBook/Books/Analysis2_Tao_2022/)<br>[`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/Analysis2_Tao_2022/) | <details><summary>9 contributors</summary><sub>Chenyi Li, Min Cui, Qiming Dai, Shu Miao, Wanli Ma, Yi Yuan, Zichen Wang, Ziyu Wang, Zaiwen Wen</sub></details> | [Docs](https://optpku.github.io/ReasBook/docs/ReasBook/Books/Analysis2_Tao_2022/Book.html)<br>[Verso](https://optpku.github.io/ReasBook/sites/analysis2_tao_2022/pages/) |
| **[Combinatorial Group Theory](ReasBook/Books/CombinatorialGroupTheory_Magnus_2004/)**<br><sub>Magnus, Karrass, and Solitar (2004)</sub> | [`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/CombinatorialGroupTheory_Magnus_2004/) | Zichen Wang | [Docs](https://optpku.github.io/ReasBook/docs/ReasBook/Books/CombinatorialGroupTheory_Magnus_2004/Book.html)<br>[Verso](https://optpku.github.io/ReasBook/sites/combinatorialgrouptheory_magnus_2004/pages/) |
| **[Convex Analysis](ReasBook/Books/ConvexAnalysis_Rockafellar_1970/)**<br><sub>R. Tyrrell Rockafellar (1970)</sub> | [`v4.26.0`](https://github.com/optpku/ReasBook/tree/v4.26.0/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/) | <details><summary>21 contributors</summary><sub>Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, Zaiwen Wen</sub></details> | [Docs](https://optpku.github.io/ReasBook/docs/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Book.html)<br>[Verso](https://optpku.github.io/ReasBook/sites/convexanalysis_rockafellar_1970/pages/) |
| **[Convex Analysis and Monotone Operator Theory in Hilbert Spaces](ReasBook/Books/ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017/)**<br><sub>Bauschke and Combettes (2nd ed., 2017)</sub> | [`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017/) | Yifan Bai, Zichen Wang, Zaiwen Wen | [Docs](https://optpku.github.io/ReasBook/docs/ReasBook/Books/ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017/Book.html)<br>[Verso](https://optpku.github.io/ReasBook/sites/convexanalysismonotoneoperators_bauschkecombettes_2017/pages/) |
| **[First-Order Methods in Optimization](ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/)**<br><sub>Amir Beck (2017)</sub> | [`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/) | Shu Miao, Zichen Wang, Zaiwen Wen | [Docs](https://optpku.github.io/ReasBook/docs/ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/Book.html)<br>[Verso](https://optpku.github.io/ReasBook/sites/firstordermethodsoptimization_beck_2017/pages/) |
| **[Integer Programming](ReasBook/Books/IntegerProgramming_Conforti_2014/)**<br><sub>Conforti, Cornuejols, and Zambelli (2014)</sub> | [`v4.26.0`](https://github.com/optpku/ReasBook/tree/v4.26.0/ReasBook/Books/IntegerProgramming_Conforti_2014/) | <details><summary>38 contributors</summary><sub>Binghe Huang, Chenglin Li, Chenrui Yang, Chenxi Liu, Congyuan Lei, Dongye Song, Fuzhi Wang, Haodong Zhang, Jiangnan Song, Jinmin Song, Junze Qiao, Junzhe Lai, Kaiwen He, Liming Han, Lurong Yang, Meng Zhou, Pengqi Lei, Renran Luo, Siyan Chen, Wangqi Liu, Wenxin Zeng, Wanli Ma, Wenxuan Wu, Xinru Zhu, Xu Han, Xutianshi Tao, Yichao Guo, Youyou Qin, Yuhan Zhang, Yushen Guo, Yutong Zhang, Ze Zhai, Zheng Ma, Zhiyong Chen, Zichen Wang, Zichen Xu, Zihao Liu, Zaiwen Wen</sub></details> | [Docs](https://optpku.github.io/ReasBook/docs/ReasBook/Books/IntegerProgramming_Conforti_2014/Book.html)<br>Verso not published |
| **[Introduction to Real Analysis, Volume I](ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/)**<br><sub>Jiri Lebl (v6.2, 2025)</sub> | [`v4.26.0`](https://github.com/optpku/ReasBook/tree/v4.26.0/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/)<br>[`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/) | Zichen Wang, Zaiwen Wen | [Docs](https://optpku.github.io/ReasBook/docs/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Book.html)<br>[Verso](https://optpku.github.io/ReasBook/sites/introductiontorealanalysisvolumei_jirilebl_2025/pages/) |
| **[Introductory Lectures on Convex Optimization](ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/)**<br><sub>Yurii Nesterov (2004)</sub> | [`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/) | Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long | [Docs](https://optpku.github.io/ReasBook/docs/ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/Book.html)<br>[Verso](https://optpku.github.io/ReasBook/sites/introductorylecturesonconvexoptimization_nesterov_2004/pages/) |
| **[Optimization Theory and Methods: Nonlinear Programming](ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/)**<br><sub>Wenyu Sun and Ya-xiang Yuan (2006)</sub> | [`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/) | Chenyi Li, Wanli Ma, Zichen Wang | [Docs](https://optpku.github.io/ReasBook/docs/ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/Book.html)<br>[Verso](https://optpku.github.io/ReasBook/sites/optimizationtheoryandmethods_sunyuan_2006/pages/) |
| **[Probability Theory: A Comprehensive Course](ReasBook/Books/ProbabilityTheory_Klenke_2020/)**<br><sub>Achim Klenke (3rd ed., 2020)</sub> | [`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/ProbabilityTheory_Klenke_2020/) | Xuanzhi Ren, Zichen Wang | Source only (excluded from the current release profile) |
| **[Lectures on Riemann Surfaces](ReasBook/Books/RiemannSurfaces_Forster_1981/)**<br><sub>Otto Forster (1981)</sub> | [`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/RiemannSurfaces_Forster_1981/) | Zichen Wang | [Docs](https://optpku.github.io/ReasBook/docs/ReasBook/Books/RiemannSurfaces_Forster_1981/Book.html)<br>[Verso](https://optpku.github.io/ReasBook/sites/riemannsurfaces_forster_1981/pages/) |
| **[Computational Methods for Inverse Problems](ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/)**<br><sub>Curtis R. Vogel (2002)</sub> | Not assigned to an active release branch | Yifan Bai, Wanli Ma, Zichen Wang | Source only (excluded from the current release profile) |

## Papers

Titles open their catalog pages; version links open the Lean source directly.

| Formalization | Source | Contributors | Resources |
| --- | :---: | --- | --- |
| **[A Fixed-Penalty Linearized Augmented Lagrangian Method with Classical Multiplier Updates](ReasBook/Papers/TR_LALM_theory/)**<br><sub>Benqi Liu, Kangkang Deng, Zichen Wang, and Zaiwen Wen</sub> | [`v4.32.2`](https://github.com/optpku/ReasBook/tree/v4.32.2/ReasBook/Papers/TR_LALM_theory/) | Zichen Wang, Zaiwen Wen | [Docs](https://optpku.github.io/ReasBook/docs/ReasBook/Papers/TR_LALM_theory/Paper.html)<br>[Verso](https://optpku.github.io/ReasBook/sites/tr_lalm_theory/pages/)<br>[Theorem map](https://optpku.github.io/ReasBook/theorem-maps/papers/tr_lalm_theory/) |
| **[Smooth Minimization of Non-Smooth Functions](ReasBook/Papers/SmoothMinimization_Nesterov_2004/)**<br><sub>Yurii Nesterov (2004)</sub> | [`v4.26.0`](https://github.com/optpku/ReasBook/tree/v4.26.0/ReasBook/Papers/SmoothMinimization_Nesterov_2004/)<br>[`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Papers/SmoothMinimization_Nesterov_2004/) | Wanli Ma, Zichen Wang, Zaiwen Wen | [Docs](https://optpku.github.io/ReasBook/docs/ReasBook/Papers/SmoothMinimization_Nesterov_2004/Paper.html)<br>[Verso](https://optpku.github.io/ReasBook/sites/smoothminimization_nesterov_2004/pages/) |
| **[On Some Local Rings](ReasBook/Papers/OnSomeLocalRings_Maassaran_2025/)**<br><sub>Mohamad Maassarani (2025)</sub> | [`v4.26.0`](https://github.com/optpku/ReasBook/tree/v4.26.0/ReasBook/Papers/OnSomeLocalRings_Maassaran_2025/)<br>[`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Papers/OnSomeLocalRings_Maassaran_2025/) | Liang Xiao, Haochen Ju, Zichen Wang, Zaiwen Wen | [Docs](https://optpku.github.io/ReasBook/docs/ReasBook/Papers/OnSomeLocalRings_Maassaran_2025/Paper.html)<br>[Verso](https://optpku.github.io/ReasBook/sites/onsomelocalrings_maassaran_2025/pages/) |

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md).

- Book and paper code lives on the registered version branch matching its Lean/mathlib toolchain; only registered stable `vX.Y.Z` versions are accepted.
- **Book and paper code is not merged to `main`.** `main` remains the cross-version catalog, while its link folders point to the corresponding version branches.
- PR base, PR title version, `ReasBook/lean-toolchain`, and book metadata
  (when applicable) must all match.

## Build

Full multi-version Lean and documentation builds run on SiFlow and write only
to the external cache. The following local commands are intended for focused
development and preview, not for producing the public release:

```bash
./scripts/build/all.sh                 # cache, core, and optional docs
BUILD_DOCS=0 ./scripts/build/all.sh    # fast core-only build
./scripts/build/site.sh                # full pipeline plus Verso site
./scripts/preview/serve.py 18000       # http://127.0.0.1:18000/ReasBook/
```

The deployment helpers require Python 3.11 or newer. If `python3` points to an
older system interpreter, run `./sdk/deploy/bin/reasbook-deploy ci verify-python`
first and use the reported `REASBOOK_PYTHON_BIN` for local commands.

### One-command selected-book deployment

From the workspace root, use the deployment command for a reproducible local
build of one or two projects:

```bash
./sdk/deploy/bin/reasbook-deploy \
  --book IntroductiontoRealAnalysisVolumeI_JiriLebl_2025 \
  --book Analysis2_Tao_2022 \
  --no-build \
  --serve
```

The command selects the matching stable version branch, creates a detached
sparse worktree under
`/volume/math/users/zcwang/ReasBook_Reviewer/cache/reasbook/sources/`, installs
the branch toolchain when needed, and stores all Lake/package/native artifacts
under `/volume/math/users/zcwang/ReasBook_Reviewer/cache/reasbook/lake/`. It
writes only lightweight review indexes to the sibling reviewer and records an
atomic manifest under
`/volume/math/users/zcwang/ReasBook_Reviewer/cache/reasbook/manifests/`.
Override this root explicitly with `REASBOOK_CACHE_ROOT` or `--cache-root` when
using a different volume.
`--no-build` is the recommended first run: it creates only lightweight
declaration indexes and does not require Lean caches. Remove it when a local
Lean build is wanted. Pass `--dry-run` to inspect the plan, `--build-docs` only
when documentation is needed, or `--serve` to start the Python 3.11+ reviewer
after the build. The Stacks entry is indexed by default but its large Lean
build is opt-in via `--build-stacks`.
When `--serve` is used, host and port defaults are read from the reviewer
`.env`; pass `--host`/`--port` to override them.

For a static Docker deployment, run
`./sdk/deploy/bin/reasbook-deploy docker`. It builds first, validates the
generated site, starts Compose with `--remove-orphans`, and polls the published
port before returning success. The site is served at
`http://127.0.0.1:3200/ReasBook/` by default. `--skip-build` reuses an existing
site, and `--port` changes the host port.

### Immutable static release

Resolve all active version branches and explicit canonical projects without
building:

```bash
./sdk/deploy/bin/reasbook-deploy release plan \
  --profile github-pages --new-release --fetch
```

The production release flow pins every input, runs project builds and branch
finalizers on SiFlow, and assembles one verified site locally. Packaging then
derives two artifacts from that build:

| Artifact | Contents | Deployment target |
| --- | --- | --- |
| `pages` | Catalog, canonical projects, reachable project-module API docs, Verso, theorem maps, and dependency stubs | Temporary GitHub Pages host |
| `full` | Every project version with the same bounded, link-closed project-module documentation | Project-owned static server |

`release-set.json` binds both archives and their site-tree digests to the same
immutable `ReleaseSpec`. GitHub Actions only downloads, verifies, and deploys
the small `pages` archive; it never builds Lean or documentation. See
[ADR-0001](docs/decisions/0001-static-release-pipeline.md) and
[ADR-0002](docs/decisions/0002-target-specific-release-artifacts.md).

For each configured entry root, API documentation follows imports only through
project-owned Lean modules, in batches of at most 128 modules. Mathlib, Lean,
and other external libraries are excluded; referenced external HTML pages
become explicit stubs so the static site remains link-closed. The immutable
`project-modules-v2` cache identity makes retries reuse an exact prior result.

The commands below assume that `RELEASE_ID` already has a completed aggregate
`site` stage in the release cache. The default cache is
`/volume/math/users/zcwang/ReasBook_Reviewer/cache/reasbook`; override it with
`REASBOOK_CACHE_ROOT` or `--cache-root`. Branch-level Lean caches alone are not
a packageable release—finish the aggregate stage first and confirm it with
`release status`.

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

The required validation step does not rebuild Lean or documentation. It checks
the bounded Pages archive, the complete full archive, and an atomic
self-hosted installation, including representative desktop and mobile browser
routes. Install the optional browser runtime as described in
[the deployment SDK guide](sdk/deploy/README.md) before using this publication
gate.

It requires an authenticated GitHub CLI. The `release deploy` command remains
available for a small local canary; it must not be used for the full public
multi-version build. Use `--no-publish` to stop after local packaging or
`--dry-run` to resolve the spec without creating release state. See
[`sdk/deploy/release/README.md`](sdk/deploy/src/reasbook_deploy_sdk/release/README.md).

#### Preview the exact release artifact

After packaging, the CLI verifies both the archive checksum and the site-tree
digest before serving. It does not rebuild anything:

```bash
export REASBOOK_CACHE_ROOT=/path/to/reasbook-cache
RELEASE_ID="${RELEASE_ID:?set RELEASE_ID to the generated release ID}"
./sdk/deploy/bin/reasbook-deploy release preview "$RELEASE_ID" \
  --artifact pages --host 127.0.0.1 --port 18000
```

Open `http://127.0.0.1:18000/ReasBook/`. This serves the verified packaged
Pages tree, not an intermediate branch build. Use `--artifact full` to inspect
the exact self-hosted candidate. Add `--host 0.0.0.0 --public-prefix
/path/to/proxy/18000` when accessing it through a workspace proxy.

#### GitHub Pages capacity and publication

The `pages` artifact fails during local packaging above 850 MB, 60,000 files,
or 950 MB compressed. The publish workflow repeats the extracted-size and
file-count checks from the archive listing before extraction. Hidden site
content such as `.nojekyll` and `.well-known/` is retained and included in the
verified tree digest. Exact `.git` and `.github` path segments are rejected
because the Pages upload action excludes them and would otherwise change the
tree after local verification. These margins keep the site below GitHub Pages'
1 GB and 10-minute deployment limits; compression alone does not make an
oversized site acceptable.

After the deployment workflow has reached the default branch, configure and
audit the repository boundary once:

```bash
./sdk/deploy/bin/reasbook-deploy release configure-pages \
  --profile github-pages --dry-run
./sdk/deploy/bin/reasbook-deploy release configure-pages \
  --profile github-pages
```

The command creates only missing workflow-based Pages settings, enables
repository immutable releases, and permits only the exact default branch to
use the `github-pages` environment. Its token therefore needs repository
Administration read permission for an audit and write permission to enable the
setting. It refuses to rewrite an existing custom domain or incompatible/extra
branch policy; such a policy must be reviewed and removed explicitly in GitHub
before rerunning.

```bash
./sdk/deploy/bin/reasbook-deploy release publish "$RELEASE_ID" \
  --target github-pages --wait
```

The command first consumes the successful, required-browser acceptance record
under `cache/reasbook/validation/<release-id>/latest.json`. Dry runs use the
same gate. It then uploads the Pages archive, manifest, checksum, and ReleaseSet
to an immutable GitHub Release, waits until GitHub reports the Release as
immutable, and only then dispatches the pinned publish-only workflow. The
workflow uses GitHub's Release and per-asset verification commands before
deploying the exact hidden-file-inclusive tree. Its verify job has only
read-level contents, Pages, and artifact-attestation permissions and installs
only the pinned PyYAML verifier dependency.

Neither the local upload nor the GitHub workflow runs Lean, Verso, doc-gen, or
theorem-graph work, and no Lean cache is transferred. Wall-clock time is
therefore governed mainly by the Pages archive size and uplink, the Actions
queue, one download/decompression/upload pass, and GitHub Pages deployment;
CPU use is limited to hashing, validation, and archive extraction. The
workflow's 30-minute verify and 10-minute deploy limits are failure ceilings,
not expected runtimes. The local Release upload has a separate two-hour timeout
so a valid archive near the 950 MB ceiling is not killed by the normal
five-minute GitHub API-command limit.

This is a one-command promotion only after packaging, required validation,
authentication, and the one-time `configure-pages` setup. It is deliberately
not a source-to-production one-click build: the full SiFlow build and aggregate
stage remain explicit and independently retryable.
For a new Release, it also requires a clean checkout whose `HEAD` exactly
matches both the GitHub default branch and the ReleaseSpec
`source.registry_commit`, so merge and pull the deployment changes before
running it. A dirty tooling revision remains valid for local canaries, but the
GitHub publisher accepts only the clean
`COMMIT+tooling-sha256:DIGEST` form. It creates the exact Git ref first, uses
the Releases REST API to create and publish the draft, and rechecks the fully
dereferenced tag before upload, publication, and dispatch. This avoids relying
on release flags absent from the repository's supported GitHub CLI 2.4. A
pre-existing or concurrently created tag is accepted only when it resolves to
the same commit. The workflow repeats the source-commit and clean-tooling
checks from the bundled ReleaseSpec and recomputes the artifact-policy digest
from the trusted profile in its checked-out default-branch revision.
Consequently, a release cannot be re-dispatched after that policy changes;
create and validate a new ReleaseSpec instead. Otherwise re-dispatching an
existing immutable tag does not depend on the caller's branch. See the official
[GitHub Pages limits](https://docs.github.com/en/pages/getting-started-with-github-pages/github-pages-limits)
and
[GitHub Release limits](https://docs.github.com/en/repositories/releasing-projects-on-github/about-releases).

#### Deploy the complete site on your own server

Configure the web server once with `/srv/reasbook/current/public` as its
document root; a ready Nginx example is
[`config/deploy/nginx-self-hosted.conf`](config/deploy/nginx-self-hosted.conf).
Then either deploy directly from the shared release cache:

```bash
./sdk/deploy/bin/reasbook-deploy release publish "$RELEASE_ID" \
  --target self-hosted --deploy-root /srv/reasbook \
  --health-url http://127.0.0.1/ReasBook/release-spec.json
```

or transfer the full archive and `release-set.json`. Before transfer, record
the archive's per-release SHA-256 on the trusted build host and deliver that
value to the operator through an independent authenticated channel (for
example a signed deployment record). Also record the artifact-policy digest
from the reviewed profile:

```bash
POLICY_SHA256="$(./sdk/deploy/bin/reasbook-deploy release \
  --repo-root . policy-digest --profile github-pages)"
CACHE_ROOT="${REASBOOK_CACHE_ROOT:-/volume/math/users/zcwang/ReasBook_Reviewer/cache/reasbook}"
FULL_BUNDLE="$CACHE_ROOT/releases/$RELEASE_ID/$RELEASE_ID.site.tar.zst"
FULL_SHA256="$(sha256sum "$FULL_BUNDLE" | awk '{print $1}')"
printf 'release=%s\nfull_sha256=%s\npolicy_sha256=%s\n' \
  "$RELEASE_ID" "$FULL_SHA256" "$POLICY_SHA256"
```

The destination needs no source checkout or release cache:

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

This transfers and installs the same `full` bundle produced beside the Pages
bundle. Once the web server and trust inputs are configured, the single
`release install` invocation verifies it and performs the atomic activation;
it does not rebuild the site.

Record both trust inputs on the trusted build/publish side; do not derive
`FULL_SHA256` from a `SHA256SUMS` file transferred with the archive. Such a
co-transferred checksum is useful for diagnostics only and cannot authenticate
the release. `POLICY_SHA256` verifies deployment policy, but it is normally
stable across releases and therefore does not authenticate release identity.
Installation binds the independently authenticated full-bundle checksum, site
digest, counts, ReleaseSpec, and artifact policy to `release-set.json` before it
creates the deployment root. It then writes a versioned directory, atomically
switches `current`, and restores the previous release if the health check
fails. Roll back without rebuilding:

```bash
./sdk/deploy/bin/reasbook-deploy release rollback \
  --target self-hosted --deploy-root /srv/reasbook --to "$RELEASE_ID" \
  --health-url http://127.0.0.1/ReasBook/release-spec.json
```

For a containerized server, make the initial install with
`--filesystem-health-only`, then start the dedicated production Compose project
without rebuilding the site:

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

The container mounts the stable deploy root, so later atomic `current` switches
take effect without restarting Nginx. This is separate from
`docker-compose.yml`, which remains the local generated-site preview.

### Implementation layout

Repository adapters are grouped by responsibility under `scripts/`; there are
no top-level script wrappers. Reusable Python, Lake, toolchain, external-cache,
retry, heartbeat, graph, and deployment behavior lives under `sdk/`. CI and
local automation call the SDK entrypoints directly.

Reusable build tools are maintained separately under `sdk/`: `build`, `verso`,
`theorem_graph`, and `comparator` each provide a typed API, CLI, tests, and
README. They all depend on the platform-neutral primitives in `sdk/common`;
`sdk/deploy` is the composition layer for multi-stage builds. See
[sdk/README.md](sdk/README.md) for the dependency graph and installation order,
and [scripts/README.md](scripts/README.md) for the repository adapter boundary.

## Sponsors

- Beijing International Center for Mathematical Research, Peking University
- Great Bay University
- Huawei
- iQuest Research
- Sino-Russian Mathematics Center
- National Natural Science Foundation of China

## Lean Projects

### Formalization Platform

- [ReasLab](https://reaslab.io)
  - An online Lean formalization platform for collaborative theorem development and verification.

### Formalization Projects

- [Optlib](https://github.com/optsuite/optlib)
  - A Lean4 library for mathematical optimization, covering convex analysis, optimality conditions, and algorithm convergence.
- [ReasBook](https://github.com/optsuite/ReasBook)
  - A Lean4 project for textbook and paper formalization, including both theorem proving and computational problems.

### Benchmark

- [AMBER](https://github.com/optsuite/AMBER)
  - A Lean4 benchmark for construction and verification in applied mathematics formalization, covering both theorem-proving and computational problems.
- [CAM-Bench](https://github.com/optpku/CAM-Bench)
  - A Lean4 benchmark for formal theorem proving in computational and applied mathematics.

### Autoformalization and Theorem Proving Systems

- [M2F](https://github.com/optsuite/M2F)
  - A toolkit for converting natural-language mathematical textbooks into formalization-ready Lean projects.
- [SITA](https://github.com/chenyili0818/SITA)
  - A structure-to-instance autoformalization framework for generating Lean definitions/theorems with verification feedback.
- [lean-tools-mcp](https://github.com/optsuite/lean-tools-mcp)
  - A Lean MCP server with higher parallel throughput and lower memory usage for heavy imports (especially Mathlib).

## Publications

### Mathematical Formalization

- Wanli Ma, Zichen Wang,  Zaiwen Wen, *A Unified Framework for Formalizing Matrix Decomposition Proofs*. [(Paper)](https://arxiv.org/abs/2607.05874)
- Chenyi Li, Ziyu Wang, Wanyi He, Yuxuan Wu, Shengyang Xu, Zaiwen Wen. *Formalization of Complexity Analysis of the First-order Optimization Algorithms*, Journal of Automated Reasoning. [(Paper)](https://arxiv.org/abs/2403.11437)
- Chenyi Li, Zichen Wang, Yifan Bai, Yunxi Duan, Yuqing Gao, Pengfei Hao, Zaiwen Wen. *Formalization of Algorithms for Optimization with Block Structures*, Science in China Series A: Mathematics. [(Paper)](http://arxiv.org/abs/2503.18806)
- Chenyi Li, Shengyang Xu, Chumin Sun, Li Zhou, Zaiwen Wen. *Formalization of Optimality Conditions for Smooth Constrained Optimization Problems*. [(Paper)](https://arxiv.org/abs/2503.18821)
- Chenyi Li, Zaiwen Wen. *An Introduction to Mathematics Formalization Based on Lean*. [(Paper)](http://faculty.bicmr.pku.edu.cn/~wenzw/paper/OptLean.pdf)

### Autoformalization and Automated Theorem Proving

- Wentao Long, Yunfei Zhang, Chenyi Li, Zaiwen Wen, *MECA: A Mechanism-Centered Agent for Constructing Well-Specified and Valuable Mathematical Conjectures*. [(Paper)](https://arxiv.org/abs/2607.27709)
- Chenyi Li, Yanchen Nie, Zhenyu Ming, Gong Zhang, Kun Yuan, Zaiwen Wen. *OptProver: Bridging Olympiad and Optimization through Continual Training in Formal Theorem Proving*, ICML 2026. [(Paper)](https://arxiv.org/abs/2604.23712)
- Zichen Wang, Wanli Ma, Zhenyu Ming, Gong Zhang, Kun Yuan, Zaiwen Wen. *M2F: Automated Formalization of Mathematical Literature at Scale*. [(Paper)](https://arxiv.org/abs/2602.17016)
- Ziyu Wang, Bowen Yang, Chenyi Li, Yuan Zhang, Shihao Zhou, Bin Dong, Zaiwen Wen. *Translating Informal Proofs into Formal Proofs Using a Chain of States*. [(Paper)](https://arxiv.org/abs/2512.10317)
- Chenyi Li, Wanli Ma, Zichen Wang, Zaiwen Wen. *SITA: A Framework for Structure-to-Instance Theorem Autoformalization*, AAAI 2026. [(Paper)](https://arxiv.org/abs/2511.10356)

### Theorem-Proof Checking

- Ziyu Wang, Qiming Dai, Yishan Wu, Zaiwen Wen. *FaithSieve: Fine-Grained Evaluation of Math Proofs with Faithful Formal Evidence*.
- Ziyu Wang, Qiming Dai, Chenyi Li, Zaiwen Wen, *Beyond Formal Correctness: Structure-Aware Evaluation of Informal–Formal Proof Correspondence*

### Premise Selection

- Zichen Wang, Anjie Dong, Zaiwen Wen. *Tree-Based Premise Selection for Lean4*, NeurIPS 2025. [(Paper)](https://neurips.cc/virtual/2025/loc/san-diego/poster/116011)
- Shu Miao, Zichen Wang, Anjie Dong, Yishan Wu, Weixi Zhang, Zaiwen Wen. *Directed Multi-Relational GCNs for Premise Selection*.

### Benchmark

- Bowen Yang, Yi Yuan, Chenyi Li, Ziyu Wang, Liangqi Li, Bo Zhang, Zhe Li, Zaiwen Wen. *Construction-Verification: A Benchmark for Formalizing Applied Mathematics in Lean 4*. [(Paper)](https://arxiv.org/abs/2602.01291)
- Wentao Long, Yunfei Zhang, Chenyi Li, Li Zhou, Chumin Sun, Zaiwen Wen. *CAM-Bench: A Benchmark for Computational and Applied Mathematics in Lean*. [(Paper)](https://arxiv.org/abs/2605.17255)

## Contributors

- Chenyi Li, School of Mathematical Sciences, Peking University, China (`lichenyi@stu.pku.edu.cn`)
- Wanli Ma, Beijing International Center for Mathematical Research, Peking University, China (`wlma@pku.edu.cn`)
- Zichen Wang, School of Mathematical Sciences, Peking University, China (`zichenwang25@stu.pku.edu.cn`)
- Ziyu Wang, School of Mathematical Sciences, Peking University, China (`wangziyu-edu@stu.pku.edu.cn`)
- Zaiwen Wen, Beijing International Center for Mathematical Research, Peking University, China (`wenzw@pku.edu.cn`)
- Yifan Bai, Anjie Dong, Yunxi Duan, Xinyi Guo, Pengfei Hao, Yuhao Jiang, Gongxun Li, Yantao Li, Wentao Long, Zebo Liu, Zhenxi Liu, Siyuan Ma, Guangxuan Pan, Siyuan Shao, Weiran Shi, Junren Si, Xuran Sun, Xuan Tang, Feiming Wang, Yijie Wang, Zhiyan Wang, Zixi Wang, Suwu Wu, Mingyue Xu, Lurong Yang, Yunfei Zhang, Jian Yu, Changyun Zou

## Citation

If you use ReasBook, please cite both the M2F paper and the repository:

M2F paper:

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

ReasBook software:

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

When referring to a particular formalization, also cite the original book or
paper and record the ReasBook project directory, version branch, and full commit
SHA. For example: `v4.30.0`, `ReasBook/Books/<project>/`, and the output of
`git rev-parse HEAD`. This repository also provides [`CITATION.cff`](CITATION.cff)
for citation tools and GitHub's citation interface.

## License

ReasBook uses the [Apache License 2.0](LICENSE), matching mathlib. Unless an
individual file carries a different notice, this license covers ReasBook
content on every official branch and in all copies and forks derived from this
repository. Fork-specific additions and third-party dependencies remain subject
to their respective license notices.
