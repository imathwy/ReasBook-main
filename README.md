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

## Download and Use One Project

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
| **[A Concise Course in Algebraic Topology](ReasBook/Books/AlgebraicTopology_May_1999/)**<br><sub>J. Peter May (1999)</sub> | [`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/AlgebraicTopology_May_1999/) | Ze Yuan, Zichen Wang, Zaiwen Wen | [Docs](https://optpku.github.io/ReasBook/docs/ReasBook/AlgebraicTopology_May_1999/Book.html)<br>[Verso](https://optpku.github.io/ReasBook/books/algebraictopology_may_1999/) |
| **[Analysis II](ReasBook/Books/Analysis2_Tao_2022/)**<br><sub>Terence Tao (4th ed., 2022)</sub> | [`v4.26.0`](https://github.com/optpku/ReasBook/tree/v4.26.0/ReasBook/Books/Analysis2_Tao_2022/)<br>[`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/Analysis2_Tao_2022/) | <details><summary>9 contributors</summary><sub>Chenyi Li, Min Cui, Qiming Dai, Shu Miao, Wanli Ma, Yi Yuan, Zichen Wang, Ziyu Wang, Zaiwen Wen</sub></details> | [Docs v4.26.0](https://optpku.github.io/ReasBook/docs/ReasBook/Books/Analysis2_Tao_2022/Book.html)<br>[Docs v4.30.0](https://optpku.github.io/ReasBook/docs/ReasBook/Analysis2_Tao_2022/Book.html)<br>[Verso](https://optpku.github.io/ReasBook/books/analysis2_tao_2022/) |
| **[Combinatorial Group Theory](ReasBook/Books/CombinatorialGroupTheory_Magnus_2004/)**<br><sub>Magnus, Karrass, and Solitar (2004)</sub> | [`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/CombinatorialGroupTheory_Magnus_2004/) | Zichen Wang, Zaiwen Wen | [Docs](https://optpku.github.io/ReasBook/docs/ReasBook/CombinatorialGroupTheory_Magnus_2004/Book.html)<br>[Verso](https://optpku.github.io/ReasBook/books/combinatorialgrouptheory_magnus_2004/) |
| **[Convex Analysis](ReasBook/Books/ConvexAnalysis_Rockafellar_1970/)**<br><sub>R. Tyrrell Rockafellar (1970)</sub> | [`v4.26.0`](https://github.com/optpku/ReasBook/tree/v4.26.0/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/) | <details><summary>21 contributors</summary><sub>Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, Zaiwen Wen</sub></details> | [Docs](https://optpku.github.io/ReasBook/docs/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Book.html)<br>[Verso](https://optpku.github.io/ReasBook/books/convexanalysis_rockafellar_1970/) |
| **[Convex Analysis and Monotone Operator Theory in Hilbert Spaces](ReasBook/Books/ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017/)**<br><sub>Bauschke and Combettes (2nd ed., 2017)</sub> | [`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017/) | Zichen Wang, Zaiwen Wen | [Docs](https://optpku.github.io/ReasBook/docs/ReasBook/ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017/Book.html)<br>[Verso](https://optpku.github.io/ReasBook/books/convexanalysismonotoneoperators_bauschkecombettes_2017/) |
| **[First-Order Methods in Optimization](ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/)**<br><sub>Amir Beck (2017)</sub> | [`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/) | Shu Miao, Zichen Wang, Zaiwen Wen | [Docs](https://optpku.github.io/ReasBook/docs/ReasBook/FirstOrderMethodsOptimization_Beck_2017/Book.html)<br>[Verso](https://optpku.github.io/ReasBook/books/firstordermethodsoptimization_beck_2017/) |
| **[Integer Programming](ReasBook/Books/IntegerProgramming_Conforti_2014/)**<br><sub>Conforti, Cornuejols, and Zambelli (2014)</sub> | [`v4.26.0`](https://github.com/optpku/ReasBook/tree/v4.26.0/ReasBook/Books/IntegerProgramming_Conforti_2014/) | <details><summary>38 contributors</summary><sub>Binghe Huang, Chenglin Li, Chenrui Yang, Chenxi Liu, Congyuan Lei, Dongye Song, Fuzhi Wang, Haodong Zhang, Jiangnan Song, Jinmin Song, Junze Qiao, Junzhe Lai, Kaiwen He, Liming Han, Lurong Yang, Meng Zhou, Pengqi Lei, Renran Luo, Siyan Chen, Wangqi Liu, Wenxin Zeng, Wanli Ma, Wenxuan Wu, Xinru Zhu, Xu Han, Xutianshi Tao, Yichao Guo, Youyou Qin, Yuhan Zhang, Yushen Guo, Yutong Zhang, Ze Zhai, Zheng Ma, Zhiyong Chen, Zichen Wang, Zichen Xu, Zihao Liu, Zaiwen Wen</sub></details> | [Docs](https://optpku.github.io/ReasBook/docs/ReasBook/Books/IntegerProgramming_Conforti_2014/Book.html)<br>[Verso](https://optpku.github.io/ReasBook/books/integerprogramming_conforti_2014/) |
| **[Introduction to Real Analysis, Volume I](ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/)**<br><sub>Jiri Lebl (v6.2, 2025)</sub> | [`v4.26.0`](https://github.com/optpku/ReasBook/tree/v4.26.0/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/)<br>[`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/) | Zichen Wang, Zaiwen Wen | [Docs v4.26.0](https://optpku.github.io/ReasBook/docs/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Book.html)<br>[Docs v4.30.0](https://optpku.github.io/ReasBook/docs/ReasBook/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Book.html)<br>[Verso](https://optpku.github.io/ReasBook/books/introductiontorealanalysisvolumei_jirilebl_2025/) |
| **[Probability Theory: A Comprehensive Course](ReasBook/Books/ProbabilityTheory_Klenke_2020/)**<br><sub>Achim Klenke (3rd ed., 2020)</sub> | [`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/ProbabilityTheory_Klenke_2020/) | Xuanzhi Ren, Zichen Wang, Zaiwen Wen | [Docs](https://optpku.github.io/ReasBook/docs/ReasBook/ProbabilityTheory_Klenke_2020/Book.html)<br>[Verso](https://optpku.github.io/ReasBook/books/probabilitytheory_klenke_2020/) |
| **[Lectures on Riemann Surfaces](ReasBook/Books/RiemannSurfaces_Forster_1981/)**<br><sub>Otto Forster (1981)</sub> | [`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Books/RiemannSurfaces_Forster_1981/) | Zichen Wang, Zaiwen Wen | [Docs](https://optpku.github.io/ReasBook/docs/ReasBook/RiemannSurfaces_Forster_1981/Book.html)<br>[Verso](https://optpku.github.io/ReasBook/books/riemannsurfaces_forster_1981/) |

## Papers

Titles open their catalog pages; version links open the Lean source directly.

| Formalization | Source | Contributors | Resources |
| --- | :---: | --- | --- |
| **[A Fixed-Penalty Linearized Augmented Lagrangian Method with Classical Multiplier Updates](ReasBook/Papers/TR_LALM_theory/)**<br><sub>Benqi Liu, Kangkang Deng, Zichen Wang, and Zaiwen Wen</sub> | [`v4.32.2`](https://github.com/optpku/ReasBook/tree/v4.32.2/ReasBook/Papers/TR_LALM_theory/) | Zichen Wang, Zaiwen Wen | [Docs](https://optpku.github.io/ReasBook/docs/ReasBook/TR_LALM_theory/Paper.html)<br>[Theorem map](https://optpku.github.io/ReasBook/theorem-maps/papers/tr_lalm_theory/)<br>[Verso](https://optpku.github.io/ReasBook/papers/tr_lalm_theory/) |
| **[Smooth Minimization of Non-Smooth Functions](ReasBook/Papers/SmoothMinimization_Nesterov_2004/)**<br><sub>Yurii Nesterov (2004)</sub> | [`v4.26.0`](https://github.com/optpku/ReasBook/tree/v4.26.0/ReasBook/Papers/SmoothMinimization_Nesterov_2004/)<br>[`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Papers/SmoothMinimization_Nesterov_2004/) | Wanli Ma, Zichen Wang, Zaiwen Wen | [Docs v4.26.0](https://optpku.github.io/ReasBook/docs/ReasBook/Papers/SmoothMinimization_Nesterov_2004/Paper.html)<br>[Docs v4.30.0](https://optpku.github.io/ReasBook/docs/ReasBook/SmoothMinimization_Nesterov_2004/Paper.html)<br>[Verso](https://optpku.github.io/ReasBook/papers/smoothminimization_nesterov_2004/) |
| **[On Some Local Rings](ReasBook/Papers/OnSomeLocalRings_Maassaran_2025/)**<br><sub>Mohamad Maassarani (2025)</sub> | [`v4.26.0`](https://github.com/optpku/ReasBook/tree/v4.26.0/ReasBook/Papers/OnSomeLocalRings_Maassaran_2025/)<br>[`v4.30.0`](https://github.com/optpku/ReasBook/tree/v4.30.0/ReasBook/Papers/OnSomeLocalRings_Maassaran_2025/) | Liang Xiao, Haochen Ju, Zichen Wang, Zaiwen Wen | [Docs v4.26.0](https://optpku.github.io/ReasBook/docs/ReasBook/Papers/OnSomeLocalRings_Maassaran_2025/Paper.html)<br>[Docs v4.30.0](https://optpku.github.io/ReasBook/docs/ReasBook/OnSomeLocalRings_Maassaran_2025/Paper.html)<br>[Verso](https://optpku.github.io/ReasBook/papers/onsomelocalrings_maassaran_2025/) |

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
