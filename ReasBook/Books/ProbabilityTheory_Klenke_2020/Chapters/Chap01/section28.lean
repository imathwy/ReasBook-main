import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_1_28 (from Items/Chap01) -/
/-
Definition 1.28 (content): A content on a semiring of sets is the canonical mathlib bundled
object `AddContent ℝ≥0∞ A`, namely a set function on `A` with value `0` on `∅` that is finitely
additive on finite pairwise disjoint unions inside `A`.
-/
recall MeasureTheory.AddContent

open MeasureTheory

open scoped ENNReal

universe u

variable {Ω : Type u} {A : Set (Set Ω)}

namespace AddContent

/-
Definition 1.28 (premeasure): On a semiring of sets, a premeasure is the canonical mathlib
predicate `AddContent.IsSigmaSubadditive` on an additive content.
-/
recall MeasureTheory.AddContent.IsSigmaSubadditive

/-- Definition 1.28 (premeasure): On a semiring of sets, the textbook countable additivity clause
for pairwise disjoint unions is equivalent to mathlib's canonical predicate
`AddContent.IsSigmaSubadditive` on an additive content. -/
theorem isSigmaSubadditive_iff_forall_iUnion_eq_tsum (μ : AddContent ℝ≥0∞ A)
    (hA : IsSetSemiring A) :
    μ.IsSigmaSubadditive ↔
      ∀ ⦃s : ℕ → Set Ω⦄, (∀ n, s n ∈ A) →
        Pairwise (fun i j ↦ Disjoint (s i) (s j)) → (⋃ n, s n) ∈ A →
        μ (⋃ n, s n) = ∑' n, μ (s n) := sorry

end AddContent

/- Definition 1.28 (measure): Once the domain is a `σ`-algebra, the canonical bundled notion of
measure is `Measure Ω` on the corresponding measurable space. -/
recall MeasureTheory.Measure

/- Definition 1.28 (probability measure): A probability measure is the canonical mathlib predicate
`IsProbabilityMeasure μ` on a measure `μ`, i.e. a measure with total mass `1`. -/
recall MeasureTheory.IsProbabilityMeasure
