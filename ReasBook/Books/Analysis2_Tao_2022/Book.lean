
import Books.Analysis2_Tao_2022.Chapters.Chap01
import Books.Analysis2_Tao_2022.Chapters.Chap02
import Books.Analysis2_Tao_2022.Chapters.Chap03
import Books.Analysis2_Tao_2022.Chapters.Chap04
import Books.Analysis2_Tao_2022.Chapters.Chap05
import Books.Analysis2_Tao_2022.Chapters.Chap06
import Books.Analysis2_Tao_2022.Chapters.Chap07
import Books.Analysis2_Tao_2022.Chapters.Chap08

/-!
Overview page for Analysis II (Tao, 2022).

This aggregation module imports the currently formalized sections in this book.


Directory:

Chapter 01 -- Metric Spaces


Chapter 02 -- Continuous Functions on Metric Spaces


Chapter 03 -- Uniform Convergence


Chapter 04 -- Power Series


Chapter 05 -- Fourier Series


Chapter 06 -- Several Variable Differential Calculus


Chapter 07 -- Lebesgue Measure


Chapter 08 -- Lebesgue Integration


-/

/-
`Books.Analysis2_Tao_2022/` is a per-project workspace under the `M2F/` Lean workspace.

When you run pipelines with `--project Books.Analysis2_Tao_2022` (or `FORMAL_PROJECT=Books.Analysis2_Tao_2022`),
the orchestrator writes chapter section files under:

- `Books.Analysis2_Tao_2022/Chapters/ChapXX/sectionYY.lean`
- (bench is global) `Question_bench/...`

This file is an optional aggregation module for that workspace.

Tip: keep this file minimal; add imports only after the corresponding files exist.
-/

-- Example (uncomment when created):
-- import Books.Analysis2_Tao_2022.Chapters.Chap01.section01
