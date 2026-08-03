import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import Integer.Chapters.Chap06.section_6_3_2.ch6_sec6_3_2_lemma_6_28

-- Declarations for this item will be appended below by the statement pipeline.

section Theorem630

-- This theorem reuses the chapter's canonical owner `is_maximal_lattice_free` from
-- Section 6.2 and the direct set-builder presentation of the translate `B - f`.

variable {q : ℕ}

local notation "Rq" => Fin q → ℝ

open scoped Pointwise

/-- The canonical pointwise set translation `(-f) +ᵥ B` is exactly the source-facing translate
`B - f = {r | f + r ∈ B}`. -/
theorem neg_vadd_set_eq_setOf_add_mem
    (f : Rq) (B : Set Rq) :
    (-f) +ᵥ B = {r : Rq | f + r ∈ B} := by
  ext r
  simp [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]

/-- Theorem 6.30. A function `ψ` is a minimal valid function for `R_f` if and only if there
exists a maximal `ℤ^q`-free convex set `B` such that `ψ` is the gauge of `B - f`. -/
theorem minimal_valid_function_iff_exists_maximal_integer_free_gauge
    (f : Rq) (ψ : Rq → ℝ) :
    IsMinimalValidFunctionForContinuousInfiniteRelaxation f ψ ↔
      ∃ B : Set Rq, is_maximal_lattice_free B ∧ ψ = gauge {r | f + r ∈ B} := sorry

namespace IsMinimalValidFunctionForContinuousInfiniteRelaxation

/-- A minimal valid function for `R_f` is the gauge of `B - f` for some maximal `ℤ^q`-free
convex set `B`. -/
theorem exists_maximal_integer_free_gauge
    {f : Rq} {ψ : Rq → ℝ}
    (hψ : IsMinimalValidFunctionForContinuousInfiniteRelaxation f ψ) :
    ∃ B : Set Rq, is_maximal_lattice_free B ∧ ψ = gauge {r | f + r ∈ B} :=
  (minimal_valid_function_iff_exists_maximal_integer_free_gauge f ψ).1 hψ

/-- A minimal valid function for `R_f` is the gauge of the canonical pointwise translate
`(-f) +ᵥ B` of some maximal `ℤ^q`-free convex set `B`. -/
theorem exists_maximal_integer_free_gauge_vadd
    {f : Rq} {ψ : Rq → ℝ}
    (hψ : IsMinimalValidFunctionForContinuousInfiniteRelaxation f ψ) :
    ∃ B : Set Rq, is_maximal_lattice_free B ∧ ψ = gauge ((-f) +ᵥ B) := by
  rcases hψ.exists_maximal_integer_free_gauge with ⟨B, hB, hψB⟩
  refine ⟨B, hB, ?_⟩
  rw [hψB, neg_vadd_set_eq_setOf_add_mem]

/-- If `ψ` is the gauge of `B - f` for some maximal `ℤ^q`-free convex set `B`, then `ψ` is a
minimal valid function for `R_f`. -/
theorem of_exists_maximal_integer_free_gauge
    {f : Rq} {ψ : Rq → ℝ}
    (hψ : ∃ B : Set Rq, is_maximal_lattice_free B ∧ ψ = gauge {r | f + r ∈ B}) :
    IsMinimalValidFunctionForContinuousInfiniteRelaxation f ψ :=
  (minimal_valid_function_iff_exists_maximal_integer_free_gauge f ψ).2 hψ

/-- If `ψ` is the gauge of the canonical pointwise translate `(-f) +ᵥ B` of some maximal
`ℤ^q`-free convex set `B`, then `ψ` is a minimal valid function for `R_f`. -/
theorem of_exists_maximal_integer_free_gauge_vadd
    {f : Rq} {ψ : Rq → ℝ}
    (hψ : ∃ B : Set Rq, is_maximal_lattice_free B ∧ ψ = gauge ((-f) +ᵥ B)) :
    IsMinimalValidFunctionForContinuousInfiniteRelaxation f ψ := by
  rcases hψ with ⟨B, hB, hψB⟩
  refine of_exists_maximal_integer_free_gauge ?_
  refine ⟨B, hB, ?_⟩
  rw [hψB, neg_vadd_set_eq_setOf_add_mem]

end IsMinimalValidFunctionForContinuousInfiniteRelaxation

end Theorem630
