import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_20
import ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_26

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped Topology MeasureTheory

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

variable {μ ν : ProbabilityMeasure ℝ}

-- Proof sketch: apply the limit theorem for domains of attraction to any law `ν` whose affinely
-- normalized convolution powers converge weakly to the nontrivial limit law `μ`.
/-- Any nontrivial real probability law with a nonempty domain of attraction is broadly stable. -/
theorem isStableInBroadSense_of_mem_domainOfAttraction
    (hμ_nontrivial : ∀ x : ℝ, μ ≠ diracProba x) (hν : ν ∈ domainOfAttraction μ) :
    IsStableInBroadSense μ := sorry

-- Proof sketch: extract the scale-and-shift witnesses from `IsStableInBroadSense` and use the
-- inverse affine normalizations to make the normalized convolution powers of `μ` converge to `μ`
-- itself.
/-- A broadly stable real probability law belongs to its own domain of attraction. -/
theorem self_mem_domainOfAttraction_of_isStableInBroadSense
    (hμ : IsStableInBroadSense μ) :
    μ ∈ domainOfAttraction μ := sorry

-- Proof sketch: combine the membership-to-stability bridge with self-membership of a broadly
-- stable law.
/-- Theorem 16.27: for a nontrivial real probability law, the domain of attraction is nonempty if
and only if the law is stable in the broad sense. -/
theorem domainOfAttraction_nonempty_iff_isStableInBroadSense
    (hμ_nontrivial : ∀ x : ℝ, μ ≠ diracProba x) :
    Set.Nonempty (domainOfAttraction μ) ↔ IsStableInBroadSense μ := by
  constructor
  · rintro ⟨ν, hν⟩
    exact isStableInBroadSense_of_mem_domainOfAttraction hμ_nontrivial hν
  · intro hμ
    exact ⟨μ, self_mem_domainOfAttraction_of_isStableInBroadSense hμ⟩

end MeasureTheory.ProbabilityMeasure
