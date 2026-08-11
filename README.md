# ReasBook

**ReasBook** is a Lean 4 project for formalizing mathematics from textbooks and research papers.
The goal is to preserve the structure of original references while producing machine-checkable proofs.
We welcome contributions from researchers, students, and practitioners.

ReasBook is generated using the tool: [M2F](https://github.com/optsuite/M2F.git). 
- Try [Quokka (https://quokka.reaslab.io/)](https://quokka.reaslab.io/), our publicly available automated formalization system. Quokka can automatically transform long-form mathematical literature into compilable Lean 4 projects containing formally verified statements and proofs.

## Toolchain Branches

| Branch | Lean/mathlib | Status | Books/Papers | Last build |
| --- | --- | --- | ---: | --- |
| `v4.32.0` | `v4.32.0` | Empty | 0 / 0 | Passed |
| `v4.32.2` | `v4.32.2` | Active | 0 / 1 | Passed |
| `v4.30.0` | `v4.30.0` | Active | 8 / 2 | Passed |
| `v4.26.0` | `v4.26.0` | Active | 4 / 2 | Passed |

`main` is the cross-version catalog. The source code stays on the registered version branches; the lightweight link folders below make each entry discoverable from this branch.

Status: `Empty` (initialized, no source projects on that branch) · `Active` (accepting PRs) · `Frozen` (kept, no new books) · `Archived` (historical only).

## Main-branch Link Folders

Each directory in these indexes is a landing page for one book or paper. Open a directory and follow its prominent source link to the exact version branch and project folder.

- [Books](https://github.com/optpku/ReasBook/tree/main/ReasBook/Books/)
- [Papers](https://github.com/optpku/ReasBook/tree/main/ReasBook/Papers/)
- [Theorem dependency maps](https://optpku.github.io/ReasBook/theorem-maps/) (currently TR-LALM only)

## Books

| Book | Branch | Contributors | Documentation | Source | Verso |
| --- | --- | --- | --- | --- | --- |
| A Concise Course in Algebraic Topology — J. Peter May (1999) | `v4.30.0` | Zichen Wang, Zaiwen Wen | [doc](https://optpku.github.io/ReasBook/docs/ReasBook/AlgebraicTopology_May_1999/Book.html) | [source](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/AlgebraicTopology_May_1999/) | [verso](https://optpku.github.io/ReasBook/books/algebraictopology_may_1999/) |
| Analysis II — Terence Tao (4th ed., 2022) | `v4.26.0` / `v4.30.0` | Chenyi Li, Min Cui, Qiming Dai, Shu Miao, Wanli Ma, Yi Yuan, Zichen Wang, Ziyu Wang, Zaiwen Wen | [doc v4.26.0](https://optpku.github.io/ReasBook/docs/ReasBook/Books/Analysis2_Tao_2022/Book.html) / [doc v4.30.0](https://optpku.github.io/ReasBook/docs/ReasBook/Analysis2_Tao_2022/Book.html) | [v4.26.0](https://github.com/optpku/ReasBook/tree/v4.26.0/ReasBook/Books/Analysis2_Tao_2022/) / [v4.30.0](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/Analysis2_Tao_2022/) | [verso](https://optpku.github.io/ReasBook/books/analysis2_tao_2022/) |
| Combinatorial Group Theory — Magnus, Karrass, Solitar (2004) | `v4.30.0` | Zichen Wang, Zaiwen Wen | [doc](https://optpku.github.io/ReasBook/docs/ReasBook/CombinatorialGroupTheory_Magnus_2004/Book.html) | [source](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/CombinatorialGroupTheory_Magnus_2004/) | [verso](https://optpku.github.io/ReasBook/books/combinatorialgrouptheory_magnus_2004/) |
| Convex Analysis — R. Tyrrell Rockafellar (1970) | `v4.26.0` | Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, Zaiwen Wen | [doc](https://optpku.github.io/ReasBook/docs/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Book.html) | [source](https://github.com/optpku/ReasBook/tree/v4.26.0/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/) | [verso](https://optpku.github.io/ReasBook/books/convexanalysis_rockafellar_1970/) |
| Convex Analysis and Monotone Operator Theory in Hilbert Spaces — Bauschke, Combettes (2nd ed., 2017) | `v4.30.0` | Zichen Wang, Zaiwen Wen | [doc](https://optpku.github.io/ReasBook/docs/ReasBook/ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017/Book.html) | [source](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017/) | [verso](https://optpku.github.io/ReasBook/books/convexanalysismonotoneoperators_bauschkecombettes_2017/) |
| First-Order Methods in Optimization — Amir Beck (2017) | `v4.30.0` | Zichen Wang, Zaiwen Wen | [doc](https://optpku.github.io/ReasBook/docs/ReasBook/FirstOrderMethodsOptimization_Beck_2017/Book.html) | [source](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/) | [verso](https://optpku.github.io/ReasBook/books/firstordermethodsoptimization_beck_2017/) |
| Integer Programming — Conforti, Cornuejols, Zambelli (2014) | `v4.26.0` | Binghe Huang, Chenglin Li, Chenrui Yang, Chenxi Liu, Congyuan Lei, Dongye Song, Fuzhi Wang, Haodong Zhang, Jiangnan Song, Jinmin Song, Junze Qiao, Junzhe Lai, Kaiwen He, Liming Han, Lurong Yang, Meng Zhou, Pengqi Lei, Renran Luo, Siyan Chen, Wangqi Liu, Wenxin Zeng, Wanli Ma, Wenxuan Wu, Xinru Zhu, Xu Han, Xutianshi Tao, Yichao Guo, Youyou Qin, Yuhan Zhang, Yushen Guo, Yutong Zhang, Ze Zhai, Zheng Ma, Zhiyong Chen, Zichen Wang, Zichen Xu, Zihao Liu, Zaiwen Wen | [doc](https://optpku.github.io/ReasBook/docs/ReasBook/Books/IntegerProgramming_Conforti_2014/Book.html) | [source](https://github.com/optpku/ReasBook/tree/v4.26.0/ReasBook/Books/IntegerProgramming_Conforti_2014/) | [verso](https://optpku.github.io/ReasBook/books/integerprogramming_conforti_2014/) |
| Introduction to Real Analysis, Volume I — Jiri Lebl (v6.2, 2025) | `v4.26.0` / `v4.30.0` | Zichen Wang, Zaiwen Wen | [doc v4.26.0](https://optpku.github.io/ReasBook/docs/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Book.html) / [doc v4.30.0](https://optpku.github.io/ReasBook/docs/ReasBook/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Book.html) | [v4.26.0](https://github.com/optpku/ReasBook/tree/v4.26.0/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/) / [v4.30.0](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/) | [verso](https://optpku.github.io/ReasBook/books/introductiontorealanalysisvolumei_jirilebl_2025/) |
| Probability Theory: A Comprehensive Course — Achim Klenke (3rd ed., 2020) | `v4.30.0` | Zichen Wang, Zaiwen Wen | [doc](https://optpku.github.io/ReasBook/docs/ReasBook/ProbabilityTheory_Klenke_2020/Book.html) | [source](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/ProbabilityTheory_Klenke_2020/) | [verso](https://optpku.github.io/ReasBook/books/probabilitytheory_klenke_2020/) |
| Lectures on Riemann Surfaces — Otto Forster (1981) | `v4.30.0` | Zichen Wang, Zaiwen Wen | [doc](https://optpku.github.io/ReasBook/docs/ReasBook/RiemannSurfaces_Forster_1981/Book.html) | [source](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/RiemannSurfaces_Forster_1981/) | [verso](https://optpku.github.io/ReasBook/books/riemannsurfaces_forster_1981/) |

## Papers

| Paper | Branch | Contributors | Documentation | Source | Verso |
| --- | --- | --- | --- | --- | --- |
| A Fixed-Penalty Linearized Augmented Lagrangian Method with Classical Multiplier Updates — Benqi Liu, Kangkang Deng, Zichen Wang, Zaiwen Wen | `v4.32.2` | Zichen Wang, Zaiwen Wen | [doc](https://optpku.github.io/ReasBook/docs/ReasBook/TR_LALM_theory/Paper.html) | [v4.32.2](https://github.com/optpku/ReasBook/tree/v4.32.2/ReasBook/Papers/TR_LALM_theory/) | [verso](https://optpku.github.io/ReasBook/papers/tr_lalm_theory/) |
| Smooth Minimization of Non-Smooth Functions — Yurii Nesterov (2004) | `v4.26.0` / `v4.30.0` | Wanli Ma, Zichen Wang, Zaiwen Wen | [doc v4.26.0](https://optpku.github.io/ReasBook/docs/ReasBook/Papers/SmoothMinimization_Nesterov_2004/Paper.html) / [doc v4.30.0](https://optpku.github.io/ReasBook/docs/ReasBook/SmoothMinimization_Nesterov_2004/Paper.html) | [v4.26.0](https://github.com/optpku/ReasBook/tree/v4.26.0/ReasBook/Papers/SmoothMinimization_Nesterov_2004/) / [v4.30.0](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Papers/SmoothMinimization_Nesterov_2004/) | [verso](https://optpku.github.io/ReasBook/papers/smoothminimization_nesterov_2004/) |
| On Some Local Rings — Mohamad Maassarani (2025) | `v4.26.0` / `v4.30.0` | Liang Xiao, Haochen Ju, Zichen Wang, Zaiwen Wen | [doc v4.26.0](https://optpku.github.io/ReasBook/docs/ReasBook/Papers/OnSomeLocalRings_Maassaran_2025/Paper.html) / [doc v4.30.0](https://optpku.github.io/ReasBook/docs/ReasBook/OnSomeLocalRings_Maassaran_2025/Paper.html) | [v4.26.0](https://github.com/optpku/ReasBook/tree/v4.26.0/ReasBook/Papers/OnSomeLocalRings_Maassaran_2025/) / [v4.30.0](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Papers/OnSomeLocalRings_Maassaran_2025/) | [verso](https://optpku.github.io/ReasBook/papers/onsomelocalrings_maassaran_2025/) |

The TR-LALM entry formalizes the fixed-penalty linearized augmented
Lagrangian analysis for nonlinear equality-constrained nonconvex optimization,
including deterministic and stochastic complexity, stopping/restart semantics,
finite-length KL convergence, and the optional minimum-norm correction. Its Lean
source has 2,853 declarations across 141 implementation files, with no `sorry`
or `admit` placeholders.

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md).

- Book and paper code lives on the registered version branch matching its Lean/mathlib toolchain; only registered stable `vX.Y.Z` versions are accepted.
- **Book and paper code is not merged to `main`.** `main` remains the cross-version catalog, while its link folders point to the corresponding version branches.
- PR base, PR title version, `ReasBook/lean-toolchain`, and `book.yml` must all match.

## Build

Full Lean build and web build run on a self-hosted runner. Locally:

```bash
./build.sh                 # full build (cache get → shared docs → project docs → core)
BUILD_DOCS=0 ./build.sh    # fast preview: core only
./build-web.sh             # full pipeline + Verso site
python3 serve.py 18000     # serve at http://127.0.0.1:18000/ReasBook/
```

## Sponsors

- Beijing International Center for Mathematical Research, Peking University
- Great Bay University
- Huawei
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

- Chenyi Li, Yanchen Nie, Zhenyu Ming, Gong Zhang, Kun Yuan, Zaiwen Wen. *OptProver: Bridging Olympiad and Optimization through Continual Training in Formal Theorem Proving*, ICML 2026. [(Paper)](https://arxiv.org/abs/2604.23712)
- Zichen Wang, Wanli Ma, Zhenyu Ming, Gong Zhang, Kun Yuan, Zaiwen Wen. *M2F: Automated Formalization of Mathematical Literature at Scale*. [(Paper)](https://arxiv.org/abs/2602.17016)
- Ziyu Wang, Bowen Yang, Chenyi Li, Yuan Zhang, Shihao Zhou, Bin Dong, Zaiwen Wen. *Translating Informal Proofs into Formal Proofs Using a Chain of States*. [(Paper)](https://arxiv.org/abs/2512.10317)
- Chenyi Li, Wanli Ma, Zichen Wang, Zaiwen Wen. *SITA: A Framework for Structure-to-Instance Theorem Autoformalization*, AAAI 2026. [(Paper)](https://arxiv.org/abs/2511.10356)

### Theorem-Proof Checking

- Ziyu Wang, Qiming Dai, Yishan Wu, Zaiwen Wen. *FaithSieve: Fine-Grained Evaluation of Math Proofs with Faithful Formal Evidence*.

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

## License

Released under the Apache 2.0 license. See `LICENSE` for details.
