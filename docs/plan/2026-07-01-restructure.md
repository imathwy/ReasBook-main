# ReasBook-private 结构调整计划

## 关于项目结构的判断：单一 Lake 项目 vs 多个独立项目

**结论：ReasBook 应保持单一 Lake 项目，所有书籍/论文作为其内部子目录，不拆分为独立项目。**

理由来自 ReasBookWeb 的构建管道：

1. **`reasbookRoot` 硬编码为单一路径**：`ReasBookWeb/lakefile.lean` 第 18 行 `def reasbookRoot := "../ReasBook"` 是一个固定值，`buildLiterateJsonBatch` 用它作为唯一的 `cwd`，发出单条 `lake build +Mod:literate ...` 命令。支持多个 content root 需要改写 lakefile 的核心逻辑。

2. **`gen_sections.py` 只爬一个 source root**：脚本第 1664 行 `source_root = repo_root / "ReasBook"` 硬编码，只扫描 `Books/` 和 `Papers/` 两棵子树，生成统一的 `Sections.lean`。

3. **literate JSON 路径耦合**：每本书的 per-module `.json` 文件输出到 `ReasBook/.lake/build/literate/<module>.json`，`genLib` 按此路径查找。多个独立项目各有自己的 `.lake/`，路径无法统一。

4. **模块图必须在同一 Lake workspace 内**：`ReasBookWeb` 的 `Book` lean_lib 在自己的 workspace 内通过 `require` 引用 `ReasBook`。多个独立 content 项目意味着需要多个 `require`，且 `buildLiterateJsonBatch` 的锁机制是单文件锁，均需改造。

换言之，把书籍拆分为独立 Lake 项目，需要在 lakefile、Python 脚本、JSON 路径解析四个层面全部做改造，收益有限而成本高。**单一 Lake 项目结构既符合现有管道，又能让所有书籍共享 mathlib 编译缓存，是正确选择。**

---

## 目标

仿照 [ReasBook](https://github.com/optpku/ReasBook) 的结构，将 ReasBook-private 重构为一个统一的 literate formalization 工作区。**最终根目录下只保留 `ReasBook/`（统一内容包）、`ReasBookWeb/`（网站）、`.shared-lake/`（缓存）和顶层构建脚本**，所有书籍/论文/教材子项目全部纳入 `ReasBook/Books/` 或 `ReasBook/Papers/` 下，作为同一 Lake 项目的 lean_lib 子目录。

---

## 现状分析

### 当前目录结构（根目录平铺）

```
ReasBook-private/
  .shared-lake/              mathlib v4.30.0 共享缓存
  ReasBook/                  ReasBook 内容包（Lean v4.26.0）
  ReasBookWeb/               Verso 网站生成器（Lean v4.26.0）
  scripts/                   构建脚本
  build.sh / build-web.sh / serve.py
  Reaslib/                   优化库教材（Lean v4.24.0-rc1）
  Analysis2_Tao_2022/        ┐
  ConvexAnalysis_Rockafellar_1970/   │
  IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/  │
  OnSomeLocalRings_Maassaran_2025/   │
  SmoothMinimization_Nesterov_2004/  ├─ ALLBOOKS 来源，Lean v4.30.0
  AchimKlenke_runner/        │
  Bauschke_runner/           │
  CombinatorialGroupTheory/  │
  FirstOrderMethodsinOptimization/   │
  JPMay/  Nesterov/  RiemannSurfaces/  SmoothManifoldsLee/  │
  cartan/  serre/  stacks-proof/  stacks-refine-stmt/  │
  OptimizationResearch/  chapter1_reference_format_20260519_statement/ ┘
```

### 问题

1. **重复**：ReasBook/Books/ 中已有三本书（Analysis2_Tao、ConvexAnalysis_Rockafellar、JiriLebl）和两篇论文的旧副本，而根目录的 ALLBOOKS 来源版本更新，应以 ALLBOOKS 版本为准。

2. **结构分散**：19 个独立 Lake 项目平铺在根目录，与目标的统一内容包结构不符。

3. **工具链不统一**：ReasBook 包（v4.26.0）与 ALLBOOKS 子项目（v4.30.0）、Reaslib（v4.24.0-rc1）版本各异，需在迁移前统一到 v4.30.0。

---

## 目标结构

```
ReasBook-private/
  .shared-lake/              mathlib v4.30.0 共享缓存（ReasBook 依赖指向此处）
  ReasBook/                  统一内容包（单一 Lake 项目，v4.30.0）
    lakefile.lean
    lean-toolchain
    ReasBook.lean            根模块（imports all active books/papers）
    Books/
      Analysis2_Tao_2022/
      ConvexAnalysis_Rockafellar_1970/
      IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/
      IntegerProgramming_Conforti_2014/    （stub，已存在）
      Reaslib/               优化理论教材
      AchimKlenkeLean/
      BauschkeLean/
      CombinatorialGroupTheory/
      FirstOrderMethodsinOptimization/
      MayConciseRevised/     （JPMay 内容，源目录名为 MayConciseRevised/）
      Nesterov/
      RiemannSurfaces/
      SmoothManifoldsLee/
      cartan/
      Serre/                 （serre 内容，源目录名为 Serre/）
      stacks_project/        （stacks-proof / stacks-refine-stmt 内容）
      OptimizationResearch/
      chapter1_reference_format/
    Papers/
      OnSomeLocalRings_Maassaran_2025/
      SmoothMinimization_Nesterov_2004/
    SiteSupport/             literate 渲染支持（不变）
    LiterateExtract.lean
  ReasBookWeb/               Verso 网站生成器（结构不变）
  scripts/                   构建脚本（结构不变）
  build.sh
  build-web.sh
  serve.py
```

根目录不再有任何独立的 Lake 子项目，`.shared-lake/` 保留作 mathlib 缓存。

---

## 迁移映射表

### Books/

| 根目录项目 | 源 Lean 目录 | 目标路径 | 备注 |
|---|---|---|---|
| `Analysis2_Tao_2022/` | `Books/Analysis2_Tao_2022/` | `ReasBook/Books/Analysis2_Tao_2022/` | 覆盖旧副本 |
| `ConvexAnalysis_Rockafellar_1970/` | `Books/ConvexAnalysis_Rockafellar_1970/` 或顶层 | `ReasBook/Books/ConvexAnalysis_Rockafellar_1970/` | 覆盖旧副本 |
| `IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/` | `Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/` | `ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/` | 覆盖旧副本 |
| `Reaslib/` | `Reaslib/Reaslib/` | `ReasBook/Books/Reaslib/` | 模块前缀不变 |
| `AchimKlenke_runner/` | `AchimKlenkeLean/` | `ReasBook/Books/AchimKlenkeLean/` | |
| `Bauschke_runner/` | `BauschkeLean/` | `ReasBook/Books/BauschkeLean/` | |
| `CombinatorialGroupTheory/` | `CombinatorialGroupTheory/` | `ReasBook/Books/CombinatorialGroupTheory/` | |
| `FirstOrderMethodsinOptimization/` | `FirstOrderMethodsinOptimization/` | `ReasBook/Books/FirstOrderMethodsinOptimization/` | |
| `JPMay/` | `MayConciseRevised/` | `ReasBook/Books/MayConciseRevised/` | 源目录名与项目目录名不同 |
| `Nesterov/` | `Nesterov/` | `ReasBook/Books/Nesterov/` | |
| `RiemannSurfaces/` | `RiemannSurfaces/` | `ReasBook/Books/RiemannSurfaces/` | |
| `SmoothManifoldsLee/` | `SmoothManifoldsLee/` | `ReasBook/Books/SmoothManifoldsLee/` | |
| `cartan/` | `cartan/` | `ReasBook/Books/cartan/` | |
| `serre/` | `Serre/` | `ReasBook/Books/Serre/` | 源目录名大写 |
| `stacks-proof/` + `stacks-refine-stmt/` | `stacks_project/` 等 | `ReasBook/Books/stacks_project/` | 两个项目合并，需核查冲突 |
| `OptimizationResearch/` | `OptimizationResearch/` | `ReasBook/Books/OptimizationResearch/` | |
| `chapter1_reference_format_20260519_statement/` | `chapter1_reference_format/` | `ReasBook/Books/chapter1_reference_format/` | 源目录名不含日期后缀 |

### Papers/

| 根目录项目 | 源 Lean 目录 | 目标路径 | 备注 |
|---|---|---|---|
| `OnSomeLocalRings_Maassaran_2025/` | `Papers/OnSomeLocalRings_Maassaran_2025/` | `ReasBook/Papers/OnSomeLocalRings_Maassaran_2025/` | 覆盖旧副本 |
| `SmoothMinimization_Nesterov_2004/` | `Papers/SmoothMinimization_Nesterov_2004/` | `ReasBook/Papers/SmoothMinimization_Nesterov_2004/` | 覆盖旧副本 |

---

## 分步实施

### 第 0 步：统一工具链到 v4.30.0

**前置条件**，其余步骤均依赖此步完成。

需要升级的文件：
- `ReasBook/lean-toolchain`：`leanprover/lean4:v4.26.0` → `leanprover/lean4:v4.30.0`
- `ReasBook/lakefile.lean`：mathlib 改为指向 `.shared-lake`（与 ALLBOOKS 项目一致），doc-gen4、subverso 升级到 v4.30.0 兼容版本
- `ReasBook/lake-manifest.json`：重新 `lake update` 生成
- `ReasBookWeb/lean-toolchain` 和 `ReasBookWeb/lakefile.lean`：verso、subverso 同步升级
- Reaslib 源码：需验证是否能在 v4.30.0 + mathlib v4.30.0 下编译（可能需要少量适配）

---

### 第 1 步：迁移内容源码

按迁移映射表，对每个项目将其 Lean 源目录复制到 `ReasBook/Books/` 或 `ReasBook/Papers/` 对应位置。

```bash
# 源目录在 Books/ 子目录下（覆盖旧副本）
cp -r Analysis2_Tao_2022/Books/Analysis2_Tao_2022/ ReasBook/Books/Analysis2_Tao_2022/

# 源目录名与项目目录名一致
cp -r AchimKlenke_runner/AchimKlenkeLean/ ReasBook/Books/AchimKlenkeLean/

# 源目录名与项目目录名不同
cp -r JPMay/MayConciseRevised/ ReasBook/Books/MayConciseRevised/
cp -r serre/Serre/ ReasBook/Books/Serre/

# Reaslib 教材
cp -r Reaslib/Reaslib/ ReasBook/Books/Reaslib/

# 论文
cp -r OnSomeLocalRings_Maassaran_2025/Papers/OnSomeLocalRings_Maassaran_2025/ \
      ReasBook/Papers/OnSomeLocalRings_Maassaran_2025/
```

**注意**：`stacks-proof` 和 `stacks-refine-stmt` 均使用 `srcDir := .`（Lean 源码在项目根目录），迁移前需单独核查文件列表，避免把 lakefile 等非源码文件一并复制。

---

### 第 2 步：更新 ReasBook/lakefile.lean

各 ALLBOOKS 项目原有模块前缀（`AchimKlenkeLean.*`、`MayConciseRevised.*` 等）与 `Books.*` 命名空间不同。推荐为每个新增子库添加独立的 `lean_lib` 声明，保留原有模块前缀，避免大规模改动源码：

```lean
lean_lib AchimKlenkeLean where
lean_lib BauschkeLean where
lean_lib MayConciseRevised where
lean_lib Reaslib where
-- ... 以此类推
```

同时将 `require mathlib` 改为指向 `.shared-lake`：

```lean
require mathlib from
  FilePath.mk ".." / ".shared-lake" / ".lake" / "packages" / "mathlib"
```

---

### 第 3 步：更新 ReasBook/ReasBook.lean

为新增书籍/论文添加 `import`（可逐步启用，不必一次全部激活）：

```lean
import Books.Analysis2_Tao_2022.Book
import AchimKlenkeLean.Book   -- 若存在统一入口
-- ...
import Papers.OnSomeLocalRings_Maassaran_2025.Paper
```

各项目是否有统一的 `Book.lean` / `Paper.lean` 入口文件需在迁移时逐个确认。

---

### 第 4 步：删除根目录下的独立 Lake 项目

迁移并验证编译通过后，从根目录删除全部独立项目：

```
Analysis2_Tao_2022/  ConvexAnalysis_Rockafellar_1970/
IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/
OnSomeLocalRings_Maassaran_2025/  SmoothMinimization_Nesterov_2004/
AchimKlenke_runner/  Bauschke_runner/  CombinatorialGroupTheory/
FirstOrderMethodsinOptimization/  JPMay/  Nesterov/
RiemannSurfaces/  SmoothManifoldsLee/  cartan/  serre/
stacks-proof/  stacks-refine-stmt/  OptimizationResearch/
chapter1_reference_format_20260519_statement/
Reaslib/
```

**建议**：迁移期间保持"新旧并存"，逐项迁移 + 编译验证，通过后再删除对应的根目录项目，降低风险。

---

### 第 5 步：更新构建管道和自动生成文件

| 文件 | 操作 |
|---|---|
| `ReasBook/lakefile.lean` | 添加新 lean_lib 声明（第 2 步） |
| `ReasBook/ReasBook.lean` | 添加 import（第 3 步） |
| `ReasBookWeb/ReasBookSite/Sections.lean` | 重新运行 `scripts/gen_sections.py` 生成 |
| `ReasBookWeb/ReasBookSite/RouteTable.lean` | 同上（自动生成） |
| `.shared-lake/lakefile.lean` | 已是 v4.30.0，不变 |

---

## 注意事项

- **迁移顺序**：必须先完成第 0 步（toolchain 统一），否则 v4.26.0 的 ReasBook 包无法编译 v4.30.0 的内容。
- **stacks 项目特殊性**：`stacks-proof` 和 `stacks-refine-stmt` 均使用 `srcDir := .`，且 `stacks-proof` 包含多个 lean_lib 目标，迁移时需单独处理。
- **`gen_sections.py` 扫描范围**：脚本目前只识别 `Books/` 和 `Papers/` 两棵子树。对于以独立 lean_lib 方式注册（如 `AchimKlenkeLean`）、未置于 `Books/` 子目录下的内容，需要确认脚本是否需要扩展扫描路径，或统一迁入 `Books/` 子目录以保持一致。
- **IntegerProgramming_Conforti_2014**：仅在 `ReasBook/Books/` 中存在（stub），保留原位，无需迁移。
