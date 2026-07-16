import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap09.Definition_9_7_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped FieldExtensionDegree

/- Example 9.7.2: the canonical `ℝ`-basis of `ℂ` is the ordered pair `(1, I)`, so `ℂ` is a
two-dimensional `ℝ`-vector space and hence a finite extension of `ℝ` of degree `2`. -/
recall Complex.coe_basisOneI

/- Example 9.7.2: in the chapter's degree notation, the complex numbers form a degree-`2`
extension of the real numbers. This is the source-facing natural-number view of the canonical
owner theorem `Complex.rank_real_complex`. -/
theorem complex_degree_eq_two : Cardinal.toNat [ℂ : ℝ] = 2 := by
  simp [Complex.rank_real_complex]
