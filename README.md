# ReasBook

**ReasBook** is a Lean 4 project for formalizing mathematics from textbooks and
research papers while preserving the structure of the original references.
The formalizations are generated and maintained with
[M2F](https://github.com/optsuite/M2F).

This submission branch contains the Lean formalization of J. Peter May's
*A Concise Course in Algebraic Topology* (University of Chicago Press, 1999).

## Current Book

- [J. Peter May, *A Concise Course in Algebraic Topology* (1999)](./ReasBook/Books/AConciseCourseInAlgebraicTopology_May_1999/)
  - Contributor: Ze Yuan
  - Lean: 4.29.1
  - Mathlib: `5e932f97dd25535344f80f9dd8da3aab83df0fe6`
  - Coverage: 25 chapters, 159 numbered sections, and 1116 migrated source modules
  - Items: 985 total; 732 (74.3%) have no `sorry` in their main labeled statements
  - Remaining main-statement proof debt: 253 items, comprising 364 labeled declarations

The migration preserves the source proof bodies. Imports were rewritten only to
use the ReasBook module prefix. The 1180 existing `sorry` occurrences come from
the source project; no proofs were replaced with new `sorry` declarations.

## Source Layout

```text
ReasBook/
├── Books/
│   └── AConciseCourseInAlgebraicTopology_May_1999/
│       ├── Book.lean
│       ├── Chapters/
│       │   ├── Chap01.lean
│       │   ├── Chap01/
│       │   └── ...
│       └── README.md
├── ReasBook.lean
├── lakefile.lean
├── lake-manifest.json
└── lean-toolchain
```

Top-level book directories follow `<Title>_<AuthorLastName>_<Year>`. Lean
modules in this branch use the prefix
`Books.AConciseCourseInAlgebraicTopology_May_1999`.

The theorem files remain independent compilation units because combining all of
them into one Lean environment would introduce duplicate declarations. The
chapter and section modules therefore serve as source indexes. The `Books`
library is a default target and includes all of its submodules, so the ordinary
build still checks every migrated source file.

## Build

From the repository root:

```bash
cd ReasBook
lake build
```

To check one source file directly:

```bash
cd ReasBook
lake env lean Books/AConciseCourseInAlgebraicTopology_May_1999/Chapters/Chap25/Theorem_25_5_2.lean
```

Warnings about `sorry` and existing linter findings are expected. A successful
default build completes 5042 jobs and covers all JPMay source modules.

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
- Yifan Bai, Anjie Dong, Yunxi Duan, Xinyi Guo, Pengfei Hao, Yuhao Jiang, Gongxun Li, Yantao Li, Wentao Long, Zebo Liu, Zhenxi Liu, Siyuan Ma, Guangxuan Pan, Siyuan Shao, Weiran Shi, Junren Si, Xuran Sun, Xuan Tang, Feiming Wang, Yijie Wang, Zhiyan Wang, Zixi Wang, Suwan Wu, Mingyue Xu, Lurong Yang, Yunfei Zhang, Jian Yu, Changyun Zou

## License

Released under the Apache 2.0 license. See `LICENSE` for details.
