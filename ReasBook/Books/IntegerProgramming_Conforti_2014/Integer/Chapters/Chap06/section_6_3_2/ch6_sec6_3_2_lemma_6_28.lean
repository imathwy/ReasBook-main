import Mathlib.Analysis.Convex.Gauge
import Integer.Chapters.Chap06.section_6_2_2.ch6_sec6_2_2_theorem_6_18
import Integer.Chapters.Chap06.section_6_3_2.ch6_sec6_3_2_definition_6_3_2_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

section Lemma628

-- This lemma reuses the chapter's canonical lattice-free owner `is_lattice_free` from
-- Section 6.2 and writes the translate `B - f` in the same set-builder form used elsewhere in
-- Chapter 6.

variable {q : ℕ}

local notation "Rq" => Fin q → ℝ

/-- Lemma 6.28. If `B` is a `ℤ^q`-free closed convex set and `f ∈ interior B`, then the gauge of
the translated set `B - f = {r | f + r ∈ B}` is a valid function for the continuous infinite
relaxation `R_f`. -/
theorem lemma_6_28_gauge_is_valid_function
    (B : Set Rq)
    (f : Rq)
    (hB_closed : IsClosed B)
    (hB_convex : Convex ℝ B)
    (hB_free : is_lattice_free B)
    (hf : f ∈ interior B) :
    IsValidFunctionForContinuousInfiniteRelaxation f (gauge {r | f + r ∈ B}) := sorry

namespace IsValidFunctionForContinuousInfiniteRelaxation

/-- If `ψ` is the gauge of the translated set `B - f = {r | f + r ∈ B}` for a closed convex
`ℤ^q`-free set `B` with `f ∈ interior B`, then `ψ` is valid for `R_f`. -/
theorem of_eq_gauge_translate
    {B : Set Rq}
    {f : Rq}
    {ψ : Rq → ℝ}
    (hψ : ψ = gauge {r | f + r ∈ B})
    (hB_closed : IsClosed B)
    (hB_convex : Convex ℝ B)
    (hB_free : is_lattice_free B)
    (hf : f ∈ interior B) :
    IsValidFunctionForContinuousInfiniteRelaxation f ψ := by
  simpa [hψ] using
    lemma_6_28_gauge_is_valid_function B f hB_closed hB_convex hB_free hf

end IsValidFunctionForContinuousInfiniteRelaxation

end Lemma628
