# ReasBook-private

**ReasBook-private** 是一个 Lean 4 私有工作区，整合了 [ReasBook](https://github.com/optpku/ReasBook) 中的教材形式化内容与来自 [ALLBOOKS](https://github.com/optpku/ALLBOOKS) 的多个数学子库，统一使用 Lean v4.30.0 工具链和 Mathlib v4.30.0。

---

## 当前覆盖范围

### 教材 (Books)

| 书目 | 子库名 |
|------|--------|
| Terence Tao, *Analysis II*, 4th ed., 2022 | `Analysis2_Tao_2022` |
| Rockafellar, *Convex Analysis*, 1970 | `ConvexAnalysis_Rockafellar_1970` |
| Jiri Lebl, *Introduction to Real Analysis, Volume I*, 2025 | `IntroductiontoRealAnalysisVolumeI_JiriLebl_2025` |
| Conforti et al., *Integer Programming*, 2014 | `IntegerProgramming_Conforti_2014` |
| Achim Klenke, *Probability Theory*, 3rd ed. | `AchimKlenkeLean` |
| Bauschke & Combettes, *Convex Analysis and Monotone Operator Theory* | `BauschkeLean` |
| Magnus, Karrass & Solitar, *Combinatorial Group Theory* | `CombinatorialGroupTheory` |
| Beck, *First-Order Methods in Optimization* | `FirstOrderMethodsinOptimization` |
| May, *A Concise Course in Algebraic Topology*, revised | `MayConciseRevised` |
| Nesterov, *Lectures on Convex Optimization* | `Nesterov` |
| Forster, *Lectures on Riemann Surfaces* | `RiemannSurfaces` |
| Serre, *Linear Representations of Finite Groups* | `Serre` |
| Lee, *Introduction to Smooth Manifolds*, 2nd ed. | `SmoothManifoldsLee` |
| Cartan, *Differential Forms* | `cartan` |
| Stacks Project | `stacks_project` |
| Reaslib (optimization library) | `Reaslib` |

### 论文 (Papers)

| 论文 | 子库名 |
|------|--------|
| Nesterov, "Smooth minimization of non-smooth functions," *Math. Programming*, 2005 | `SmoothMinimization_Nesterov_2004` |
| Maassarani, "On Some Local Rings," arXiv:2512.19197v1, 2025 | `OnSomeLocalRings_Maassaran_2025` |

---

## 仓库结构

```
ReasBook-private/
├── ReasBook/              # 主 Lean 项目（Books/ + Papers/ + 子库）
│   ├── Books/             # 教材形式化内容
│   ├── Papers/            # 论文形式化内容
│   ├── lakefile.lean
│   └── lake-manifest.json
├── ReasBookWeb/           # Verso 网站项目
│   ├── ReasBookSite/      # 自动生成的页面模块
│   └── scripts/
│       └── gen_sections.py
├── .github/
│   └── workflows/
│       └── deploy_preview.yml  # CI: 构建 Verso 站点并部署到 GitHub Pages
├── scripts/               # 构建辅助脚本
├── build.sh
├── build-web.sh
└── serve.py
```

---

## 构建方式

**本地预览（仅 Verso 站点）：**
```bash
cd ReasBookWeb
python3 scripts/gen_sections.py
lake exe reasbook-site
python3 ../serve.py 18000
```

**完整构建（含 doc-gen4 文档）：**
```bash
./build-web.sh
python3 serve.py 18000
```

---

## CI 部署

每次推送到 `main` 分支会自动触发 GitHub Actions，在 self-hosted runner 上：

1. `lake exe cache get` — 拉取 Mathlib 编译缓存
2. `lake build` — 构建 ReasBook 核心
3. `gen_sections.py` + `lake exe reasbook-site` — 生成并构建 Verso 网站
4. 部署到 GitHub Pages

---

## 相关项目

| 项目 | 描述 |
|------|------|
| [ReasBook](https://github.com/optpku/ReasBook) | 公开 mirror（CI 部署源） |
| [ReasLab](https://prove.reaslab.io) | 在线 Lean 形式化平台 |
| [Optlib](https://github.com/optsuite/optlib) | 数学优化 Lean 4 库 |
| [M2F](https://github.com/optsuite/M2F) | 数学文献自动形式化工具 |

---

## 许可证

基于 **Apache 2.0** 许可证发布。
