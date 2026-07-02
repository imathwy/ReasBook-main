# ReasBook-private 编译修复与文档/网站适配计划

---

## 一、背景

结构调整完成后，`ReasBook/` 现在是一个单一 Lake 项目，包含约 18 个子库（lean_lib）。需要：

1. 排查各子库中编译失败/报错的 Lean 代码，列出待修改清单
2. 让所有书籍/论文实现与原 ReasBook 相同的 doc-gen4 文档和 Verso 网站页面

---

## 二、ReasBook 的文档与网站实现原理（现状）

### doc-gen4 文档管道

```
lake build Books.Analysis2_Tao_2022.Book:docs
→ ReasBook/.lake/build/doc/**/*.html
→ assemble_site_docs.sh 复制到 ReasBookWeb/_site/docs/
```

`build_reasbook_project_docs.sh` 通过 glob `Books/*/Book.lean` 和 `Papers/*/Paper.lean` 自动发现各书/论文，为每个生成 `:docs`。**前提：每本书必须有 `Book.lean`，每篇论文必须有 `Paper.lean`。**

### Verso 网站管道

```
gen_sections.py  →  Sections.lean + RouteTable.lean + WorkPages/**/*.lean
lake exe reasbook-site  →  ReasBookWeb/_site/
```

`gen_sections.py` 扫描 `ReasBook/Books/**/*.lean` 和 `ReasBook/Papers/**/*.lean`，按命名约定提取各节：

| 命名约定 | 说明 |
|---|---|
| `Books/<Name>/Book.lean` | 书籍首页，stem=`book` |
| `Books/<Name>/Chapters/ChapNN.lean` | 章节聚合（可自动创建） |
| `Books/<Name>/Chapters/ChapNN/sectionMM.lean` | 每个 Verso 页面，stem 以 `section` 开头 |
| `sectionMM_partP.lean` | 节的分段文件 |
| `Papers/<Name>/Paper.lean` | 论文首页，stem=`paper` 或 `main` |
| `Papers/<Name>/Sections/sectionMM.lean` | 论文各节 |

`gen_sections.py` 还会自动 upsert `/-! ... -/` docstring 到 `Book.lean`、章节聚合文件和各节文件。

### literate-extract 与 Verso 的关系

```
lake build +<Module>:literate  →  .lake/build/literate/<path>.json
LiterateModule.lean 的 loadModuleContent  →  读取 JSON
lake exe reasbook-site  →  Verso HTML（含 hover 注解）
```

每个 Verso section 页面调用 `loadModuleContent` 触发 `:literate`，将高亮后的 Lean 代码嵌入网页。

---

## 三、编译修复：待排查清单

### 3.1 已知问题

**工具链升级（v4.26.0 → v4.30.0）可能引起的破坏：**
- `ReasBook/SiteSupport/LiterateModule.lean`、`LiterateExtract.lean` 使用 SubVerso API，需确认与新版 subverso（v4.30.0）兼容
- `ReasBookWeb/lakefile.lean` 中 `verso` 升级到 v4.30.0，API 可能有变化

**新增子库可能引起的问题：**

| 子库 | 潜在问题 |
|---|---|
| `Reaslib` | 原依赖 mathlib v4.24.0，升级到 v4.30.0 后 API 变化较大 |
| `stacks_project` | 两个项目合并，`Book.lean` 冲突——`stacks-proof` 和 `stacks-refine-stmt` 都有各自的 `Book.lean` |
| `stacks_proof` | 独立 lean_lib，根目录有 `stacks_proof.lean`，需确认 import 路径 |
| `MayConciseRevised` | 原依赖 mathlib，需确认升级兼容性 |
| `AchimKlenkeLean`、`BauschkeLean` | 同上 |

### 3.2 需要执行的检查步骤

```bash
# 1. 构建 .shared-lake（确保 mathlib v4.30.0 编译完成）
cd .shared-lake && lake build

# 2. 逐个子库检查编译
cd ReasBook
lake build AchimKlenkeLean 2>&1 | grep -E "error:|warning:" | head -20
lake build BauschkeLean     2>&1 | grep -E "error:|warning:" | head -20
lake build Reaslib          2>&1 | grep -E "error:|warning:" | head -20
# ... 以此类推

# 3. 检查 literate-extract 可执行文件
lake build literate-extract
```

### 3.3 已知需要修复的文件结构问题

| 问题 | 位置 | 修复方式 |
|---|---|---|
| `stacks_project/Book.lean` 冲突 | `ReasBook/Books/stacks_project/` | 保留一份，或分别命名为 `BookProof.lean`/`BookStmt.lean` |
| `OptimizationResearch` 被 .gitignore 排除 | `ReasBook/Books/OptimizationResearch/` | 待内容完善后重新纳入追踪 |
| 各子库缺少 `Book.lean` 入口 | 所有非 Books/Papers 命名空间的子库 | 见下节 |

---

## 四、Verso/doc-gen4 适配：各子库需要做的修改

### 4.1 当前 gen_sections.py 的扫描范围问题

`gen_sections.py` 只扫描 `ReasBook/Books/` 和 `ReasBook/Papers/` 两棵子树，并且要求内部文件遵循 `ChapNN/sectionMM.lean` 的命名约定。现有新增子库有两类情况：

**A 类——目录已在 `Books/` 下，命名约定兼容**（如 Analysis2_Tao_2022、ConvexAnalysis_Rockafellar_1970）：
- 这些书已有 `Book.lean` 和 `Chapters/ChapNN/sectionMM.lean` 结构，可直接被 gen_sections.py 识别

**B 类——目录在 `Books/` 下，但命名约定不兼容**（如 AchimKlenkeLean、MayConciseRevised、Serre、cartan 等）：
- 内部没有 `ChapNN/sectionMM.lean` 结构，gen_sections.py 不会将其内容纳入 Verso 页面
- 需要决策：① 重组目录结构以符合约定；② 扩展 gen_sections.py 支持更多命名模式；③ 仅做 doc-gen4，不做 Verso 页面

**C 类——作为独立 lean_lib 注册、不在 Books/Papers 命名空间下**（如 Reaslib、stacks_project、OptimizationResearch）：
- gen_sections.py 完全不扫描这些路径，这些库不会出现在 Verso 网站中

### 4.2 各子库适配方案

对于每个子库，需要完成以下工作才能出现在 doc-gen4 文档和 Verso 网站：

**doc-gen4（最低要求）：**
- 子库的根模块文件存在（如 `Books/AchimKlenkeLean.lean` 或 `AchimKlenkeLean.lean`）
- 在 `build_reasbook_project_docs.sh` 中手动添加该模块，或者为其创建符合 glob 规则的 `Book.lean` 入口

**Verso 页面（完整要求）：**
- 必须符合 `Books/<Name>/Chapters/ChapNN/sectionMM.lean` 命名约定
- 或扩展 gen_sections.py 以支持该子库的实际结构

### 4.3 分类处理建议

| 子库 | 现有结构 | doc-gen4 | Verso | 工作量 |
|---|---|---|---|---|
| `Analysis2_Tao_2022` | Books/ + ChapNN/sectionMM | ✓ 已兼容 | ✓ 已兼容 | 无 |
| `ConvexAnalysis_Rockafellar_1970` | Books/ + ChapNN/子目录 | ✓ 有 Book.lean | 需确认 section 命名 | 小 |
| `IntroductiontoRealAnalysisVolumeI_JiriLebl_2025` | Books/ + ChapNN/sectionMM | ✓ 已兼容 | ✓ 已兼容 | 无 |
| `OnSomeLocalRings_Maassaran_2025` | Papers/ + Sections/sectionMM | ✓ 已兼容 | ✓ 已兼容 | 无 |
| `SmoothMinimization_Nesterov_2004` | Papers/ + Sections/sectionMM | ✓ 已兼容 | ✓ 已兼容 | 无 |
| `IntegerProgramming_Conforti_2014` | Books/（stub） | ✓ stub | stub | 无（等内容） |
| `Reaslib` | Books/Reaslib/（非标准） | 需添加入口 | 重组为路线A结构 | 中 |
| `AchimKlenkeLean` | Books/AchimKlenkeLean/（非标准） | 需添加入口 | 重组为路线A结构 | 中 |
| `BauschkeLean` | 同上 | 同上 | 同上 | 中 |
| `CombinatorialGroupTheory` | 同上 | 同上 | 同上 | 中 |
| `FirstOrderMethodsinOptimization` | 同上 | 同上 | 同上 | 中 |
| `MayConciseRevised` | 同上 | 同上 | 同上 | 中 |
| `Nesterov` | 同上 | 同上 | 同上 | 中 |
| `RiemannSurfaces` | 同上 | 同上 | 同上 | 中 |
| `SmoothManifoldsLee` | 同上 | 同上 | 同上 | 中 |
| `cartan` | 同上 | 同上 | 同上 | 中 |
| `Serre` | 同上 | 同上 | 同上 | 中 |
| `stacks_project` | Books/（Book.lean 冲突） | 需解决冲突 | 重组为路线A结构 | 大 |
| `chapter1_reference_format` | 同上 | 需添加入口 | 重组为路线A结构 | 中 |
| `OptimizationResearch` | 被 .gitignore（内容不完整） | 待内容完善 | 待内容完善 | 暂缓 |

---

## 五、分步实施

### 第 1 步：编译检查（优先）

在开始任何 Verso 适配之前，先确认各子库能编译通过：

1. 构建 `.shared-lake`（下载 mathlib v4.30.0）
2. 逐个 `lake build <LibName>` 检查，记录所有 error
3. 优先修复 `Reaslib`（版本跨度最大）和 stacks 相关（结构冲突）
4. 修复 `LiterateExtract.lean` 和 `SiteSupport/LiterateModule.lean` 与新版 subverso 的兼容性

### 第 2 步：解决 stacks 冲突

`stacks-proof` 和 `stacks-refine-stmt` 合并到 `Books/stacks_project/` 后，`Book.lean` 有重叠内容。需要：
- 比较两个 `Book.lean` 内容，合并为一份
- 确认 `stacks_proof.lean`（现在在 `Books/stacks_proof.lean`）的 import 路径是否正确

### 第 3 步：为 B/C 类子库创建 Book.lean 入口

对每个非标准结构的子库，在其目录下创建 `Book.lean`，import 该库的顶层模块。这样 `build_reasbook_project_docs.sh` 就能自动发现并生成 doc-gen4。

示例（`Books/AchimKlenkeLean/Book.lean`）：
```lean
import AchimKlenkeLean
```

### 第 4 步：更新 build_reasbook_project_docs.sh

当前脚本只 glob `Books/*/Book.lean` 和 `Papers/*/Paper.lean`。对于以独立 lean_lib 注册（不在 Books/Papers 命名空间下）的子库，需要在脚本中手动补充，或统一改为扫描 `lakefile.lean` 中所有 `lean_lib` 声明。

### 第 5 步：Verso 适配（路线 A）

所有 B/C 类子库采用**路线 A**：将各子库内容重组为 `Chapters/ChapNN/sectionMM.lean` 命名约定，充分利用现有 gen_sections.py，获得完整的 Verso 网站页面和侧边栏导航。

**每个子库需要完成的操作：**

1. 在 `Books/<LibName>/` 下创建 `Book.lean`（书籍首页入口，gen_sections 会 upsert docstring）
2. 将原有内容文件按章节重组为 `Chapters/ChapNN/sectionMM.lean` 结构：
   - 每个逻辑章对应一个 `ChapNN/` 目录（`NN` 为零填充两位数字）
   - 每个逻辑节对应一个 `sectionMM.lean` 文件（`MM` 为零填充两位数字）
   - 若节内容较多可进一步拆分为 `sectionMM_partP.lean`
3. 在每个 `ChapNN.lean` 中 import 该章下所有 section 文件（gen_sections 也会自动创建缺失的章聚合文件）
4. `Book.lean` import 所有 `ChapNN.lean`

**对于 Reaslib**（现有结构：`Basic/`、`ConvexAnalysis/`、`NumericalAlgebra/`、`Optlib/`）：
- 将四个顶层目录映射为四章：`Chap01`（Basic）、`Chap02`（ConvexAnalysis）、`Chap03`（NumericalAlgebra）、`Chap04`（Optlib）
- 各目录下的 `.lean` 文件映射为对应章的 section 文件

**注意**：重组后原来以独立 lean_lib 注册的子库（如 `lean_lib AchimKlenkeLean`）可保留，但其源码路径从 `Books/AchimKlenkeLean/` 下的原始结构变为重组后的结构，`lakefile.lean` 中对应的 lean_lib 声明需更新 `srcDir` 或保持默认（源码在包根下的同名目录）。

### 第 6 步：运行 gen_sections.py 并验证网站

```bash
cd ReasBookWeb && python3 scripts/gen_sections.py
lake exe reasbook-site
# 检查 _site/ 输出
```

---

## 六、优先级排序

| 优先级 | 任务 |
|---|---|
| P0 | 编译检查：确认各子库能 `lake build` 通过 |
| P0 | 修复 stacks_project/Book.lean 冲突 |
| P1 | 修复 Reaslib 与 mathlib v4.30.0 的兼容性 |
| P1 | 确认 LiterateExtract/LiterateModule 与新 subverso 兼容 |
| P2 | 为 B/C 类子库创建 Book.lean 入口（doc-gen4） |
| P2 | 更新 build_reasbook_project_docs.sh |
| P3 | Verso 适配（路线A）：重组各 B/C 类子库为 Chapters/ChapNN/sectionMM 结构 |
| P4 | OptimizationResearch 内容完善后重新纳入 |
