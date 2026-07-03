import AchimKlenkeLean.Items.Chap17.Definition_17_30
import AchimKlenkeLean.Items.Chap17.Definition_17_43
import AchimKlenkeLean.Items.Chap17.Theorem_17_47
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E] [DiscreteMeasurableSpace E]

/- Layering for Corollary 17.48:
- `expectedFirstReturnTime` and `returnCycleOccupationMeasure` are the primitive source-facing
  data from the preceding items.
- `positiveRecurrentInvariantDistribution` is the source-facing normalized excursion law `π_x`.
- The invariant-distribution conclusion itself should be stated through the owner predicate
  `Kernel.Invariant`. -/

section

variable {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}

-- Proof sketch: identify the total mass of `returnCycleOccupationMeasure P X x` with the expected
-- first return time `𝔼_x[τ_x^1]`; positive recurrence makes this mass finite, and scaling by its
-- inverse normalizes the total mass to `1`.
/-- The excursion occupation measure `μ_x` divided by `𝔼_x[τ_x^1]` is a probability measure for a
positive recurrent state `x`. -/
theorem isProbabilityMeasure_smul_returnCycleOccupationMeasure
    (x : E) (hx : IsPositiveRecurrentState P X x) :
    IsProbabilityMeasure
      ((expectedFirstReturnTime P X x)⁻¹ • (μ[P, X] x)) := sorry

/-- The distribution `π_x := μ_x / 𝔼_x[τ_x^1]` obtained by normalizing the return-cycle
occupation measure of the state `x`. -/
def positiveRecurrentInvariantDistribution
    (x : E) (hx : IsPositiveRecurrentState P X x) : ProbabilityMeasure E :=
  ⟨(expectedFirstReturnTime P X x)⁻¹ • (μ[P, X] x),
    isProbabilityMeasure_smul_returnCycleOccupationMeasure x hx⟩

end

section

variable {κ : ℕ → Kernel E E}
variable {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
variable [IsMarkovProcessRealization κ P X]

-- Proof sketch: positive recurrence of the state `x` implies recurrence, so Theorem 17.47 gives
-- the owner-level invariance statement for `(μ[P, X] x)`. Linearity of measure-kernel composition
-- preserves invariance after scaling by
-- `(𝔼_x[τ_x^1])⁻¹`, and the helper theorem above upgrades the scaled measure to the probability
-- measure `π_x`.
/-- Corollary 17.48: for a positive recurrent state `x`, the normalized excursion law
`π_x := μ_x / 𝔼_x[τ_x^1]` is an invariant distribution for the one-step kernel `κ 1`. -/
theorem positiveRecurrentInvariantDistribution_isInvariantDistribution
    (x : E) (hx : IsPositiveRecurrentState P X x) :
    Kernel.Invariant (κ 1) (positiveRecurrentInvariantDistribution x hx) := sorry

end

end ProbabilityTheory
