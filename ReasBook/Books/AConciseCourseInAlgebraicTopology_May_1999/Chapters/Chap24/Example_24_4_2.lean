import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Definition_24_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

universe v w

section

variable {X : Type} [TopologicalSpace X]
variable {n : ℕ} {E : X → Type v}
variable [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) E)]
variable [(x : X) → TopologicalSpace (E x)] [FiberBundle (Fin n → ℂ) E]
variable [(x : X) → AddCommGroup (E x)] [(x : X) → Module ℂ (E x)]
variable [VectorBundle ℂ (Fin n → ℂ) E]
variable {A : Type w} [CharacteristicClassTarget X A]

-- Semantic recall: `lean_leansearch` confirmed `PowerSeries.X` as mathlib's formal variable for
-- the series `f(t) = 1 + t`.

/-- Example 24.4.2. The total Chern class is the multiplicative characteristic class obtained
from Definition 24.4.1 by specializing the formal power series to `f(t) = 1 + t`, represented in
Lean by `1 + PowerSeries.X`. -/
abbrev totalChernClass (D : SplitBundleDatum A n E) : A :=
  multiplicativeCharacteristicClass (1 + PowerSeries.X) D

/-- Unfolding `totalChernClass` gives the product of the factors `1 + x_i` over the Chern roots
canonically determined by the split-bundle datum. -/
theorem totalChernClass_eq_prod_one_add_cRoot
    (D : SplitBundleDatum A n E) :
    totalChernClass D = ∏ i : Fin n, (1 + D.cRoot i) := by
  change multiplicativeCharacteristicClass (1 + PowerSeries.X) D = _
  rw [multiplicativeCharacteristicClass_eq_prod_aeval]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [show (1 + PowerSeries.X : PowerSeries A) =
      ((1 + Polynomial.X : Polynomial A) : PowerSeries A) by
      simp]
  simp only [PowerSeries.aeval_coe, Polynomial.aeval_add,
    Polynomial.aeval_one, Polynomial.aeval_X]

end
