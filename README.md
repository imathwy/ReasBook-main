# ReasBook

**ReasBook** is a Lean 4 project for formalizing mathematics from textbooks and research papers.
The goal is to preserve the structure of original references while producing machine-checkable proofs.
We welcome collaboration from researchers, students, and practitioners.

This branch contains the M2F-generated formalization of Amir Beck's
*First-Order Methods in Optimization*.

## Current Coverage

### Books
- [Amir Beck, *First-Order Methods in Optimization*, MOS-SIAM Series on Optimization 25, SIAM, 2017, ISBN 978-1-61197-498-0.](./ReasBook/Books/FirstOrderMethodsInOptimization_Beck_2017/)
  - Contributors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang.
  - Links: [Documentation](https://optpku.github.io/ReasBook/docs/Books/FirstOrderMethodsInOptimization_Beck_2017/Book.html) | [Lean source](./ReasBook/Books/FirstOrderMethodsInOptimization_Beck_2017/) | [Verso](https://optpku.github.io/ReasBook/books/firstordermethodsinoptimization_beck_2017/)

## Repository Layout

The repository keeps a shared Lean source tree (`ReasBook/`) and a single Verso website project (`ReasBookWeb/`):

```text
ReasBook/
├── ReasBook/                         # Main Lean project
│   ├── Books/
│   ├── ReasBook.lean
│   ├── LiterateExtract.lean
│   ├── lakefile.lean
│   ├── lake-manifest.json
│   └── lean-toolchain
├── ReasBookWeb/                      # Verso website project
│   ├── ReasBookSite/
│   ├── static_files/
│   ├── scripts/gen_sections.py
│   ├── ReasBookSite.lean
│   ├── lakefile.lean
│   ├── lake-manifest.json
│   └── lean-toolchain
├── .github/workflows/deploy_pages.yml
├── build.sh
├── build-web.sh
├── serve.py
└── scripts/cleanup-generated.sh
```

## Naming Convention

Top-level content directories use:

`<Title>_<AuthorLastName>_<Year>`

Example in this branch:

- `FirstOrderMethodsInOptimization_Beck_2017`

## Build

### Fast preview (Verso-only, recommended)

From the repository root:

```bash
BUILD_DOCS=0 ./build.sh
./scripts/build_reasbook_web.sh
python3 serve.py 18000
```

Open:

- `http://127.0.0.1:18000/ReasBook/`

### Full build (complete pipeline)

```bash
./build-web.sh
python3 serve.py 18000
```

This path is much slower than the fast preview mode.

If generated artifacts were previously committed, untrack them (without deleting local files):

```bash
./scripts/cleanup-generated.sh
```

## Sponsors

- Beijing International Center for Mathematical Research, Peking University
- Great Bay University
- Huawei
- Sino-Russian Mathematics Center
- National Natural Science Foundation of China

## Lean Projects

### Formalization Platform

- [ReasLab](https://prove.reaslab.io)
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

### Formalization of Optimization, Numerical Linear Algebra

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
