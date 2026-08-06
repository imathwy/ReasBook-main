# ReasBook — Lean/mathlib v4.26.0

**Toolchain:** `leanprover/lean4:v4.26.0`
**Mathlib:** v4.26.0
**Status:** Active
**Last build:** pending

This branch aggregates books and papers that use exactly Lean/mathlib `v4.26.0`.
Dependency locks, shared declarations, and namespaces must stay compatible within the branch.

- Manifest: [`ReasBook/lake-manifest.json`](ReasBook/lake-manifest.json)
- Aggregate entry: [`ReasBook/ReasBook.lean`](ReasBook/ReasBook.lean)

## Books

| Book | Contributors | Documentation | Source | Verso |
| --- | --- | --- | --- | --- |
| Analysis II — Terence Tao (4th ed., 2022) | Chenyi Li, Min Cui, Qiming Dai, Shu Miao, Wanli Ma, Yi Yuan, Zichen Wang, Ziyu Wang | [doc](https://optpku.github.io/ReasBook/docs/Books/Analysis2_Tao_2022/Book.html) | [source](./ReasBook/Books/Analysis2_Tao_2022/) | [verso](https://optpku.github.io/ReasBook/books/analysis2_tao_2022/) |
| Convex Analysis — R. Tyrrell Rockafellar (1970) | Wanli Ma, Zichen Wang, et al. | [doc](https://optpku.github.io/ReasBook/docs/Books/ConvexAnalysis_Rockafellar_1970/Book.html) | [source](./ReasBook/Books/ConvexAnalysis_Rockafellar_1970/) | [verso](https://optpku.github.io/ReasBook/books/convexanalysis_rockafellar_1970/) |
| Integer Programming — Conforti, Cornuejols, Zambelli (2014) | Wanli Ma, Zichen Wang, et al. | [doc](https://optpku.github.io/ReasBook/docs/Books/IntegerProgramming_Conforti_2014/Book.html) | [source](./ReasBook/Books/IntegerProgramming_Conforti_2014/) | [verso](https://optpku.github.io/ReasBook/books/integerprogramming_conforti_2014/) |
| Introduction to Real Analysis, Volume I — Jiri Lebl (v6.2, 2025) | Zichen Wang | [doc](https://optpku.github.io/ReasBook/docs/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Book.html) | [source](./ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/) | [verso](https://optpku.github.io/ReasBook/books/introductiontorealanalysisvolumei_jirilebl_2025/) |

## Papers

| Paper | Contributors | Documentation | Source | Verso |
| --- | --- | --- | --- | --- |
| Smooth Minimization of Non-Smooth Functions — Yurii Nesterov (2004) | Wanli Ma, Zichen Wang | [doc](https://optpku.github.io/ReasBook/docs/Papers/SmoothMinimization_Nesterov_2004/Paper.html) | [source](./ReasBook/Papers/SmoothMinimization_Nesterov_2004/) | [verso](https://optpku.github.io/ReasBook/papers/smoothminimization_nesterov_2004/) |
| On Some Local Rings — Mohamad Maassarani (2025) | Liang Xiao, Haochen Ju, Zichen Wang | [doc](https://optpku.github.io/ReasBook/docs/Papers/OnSomeLocalRings_Maassaran_2025/Paper.html) | [source](./ReasBook/Papers/OnSomeLocalRings_Maassaran_2025/) | [verso](https://optpku.github.io/ReasBook/papers/onsomelocalrings_maassaran_2025/) |

## Build

```bash
cd ReasBook
lake update
lake build
```

Full Lean build and web build run on the self-hosted runner; locally, `./build.sh` / `./build-web.sh`
replicate the same phases (see `scripts/`).
