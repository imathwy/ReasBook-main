import Mathlib
import ProbabilityTheory_Klenke_2020.Chap12.Definition_12_25
import ProbabilityTheory_Klenke_2020.Chap12.Theorem_12_26

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction Topology

universe u v

section

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
variable {E : Type v} [TopologicalSpace E] [MeasurableSpace E] [StandardBorelSpace E]
  [OpensMeasurableSpace E] [Nonempty E]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : ℕ → Ω → E} {xiInf : Ω → ProbabilityMeasure E}

local notation "Ξₙ" => fun n ω ↦ empiricalDistribution (Nat.succPNat n) (fun i ↦ X i) ω

-- Proof sketch: assume `Ξ∞` is a directing random probability measure as in Theorem 12.26; then
-- for each bounded continuous `f`, the empirical averages of `f (X i)` satisfy the strong law
-- with almost-sure limit `∫ x, f x ∂Ξ∞`. Rewriting those averages as integrals against the
-- empirical distribution of the first `n + 1` coordinates gives the claimed convergence.
/-- Remark 12.27 (i): if `Ξ∞` is a directing random probability measure for `X` as in
Theorem 12.26, then the empirical distributions of the prefixes `X₀, ..., Xₙ` converge almost
surely against every bounded continuous test function to `Ξ∞`. The zero-based sequence
`n ↦ empiricalDistribution (Nat.succPNat n) (fun i ↦ X i)` is the Lean encoding of the textbook
empirical measures `Ξₙ`. This is the source-facing bounded-continuous test-function formulation. -/
theorem deFinetti_empiricalDistribution_testFunction_tendsto_ae
    (hxiInf : IsDirectingProbabilityMeasure xiInf X μ) :
    ∀ f : E →ᵇ ℝ,
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n ↦ ∫ x, f x ∂(Ξₙ n ω : Measure E))
          atTop
          (nhds (∫ x, f x ∂(xiInf ω : Measure E))) := by
  sorry

-- Proof sketch: combine `deFinetti_empiricalDistribution_testFunction_tendsto_ae` with the owner
-- characterization `ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`; this is the
-- canonical `ProbabilityMeasure E` formulation of the textbook's locally compact upgrade.
/-- If `Ξ∞` is a directing random probability measure for `X` as in Theorem 12.26, then in the
canonical owner topology on `ProbabilityMeasure E` the empirical distributions of the prefixes
`X₀, ..., Xₙ` converge almost surely to `Ξ∞`. This is the `ProbabilityMeasure` bridge/view
reformulation of the preceding source-facing test-function statement. -/
theorem deFinetti_empiricalDistribution_tendsto_ae
    (hxiInf : IsDirectingProbabilityMeasure xiInf X μ) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n ↦ Ξₙ n ω) atTop (nhds (xiInf ω)) := by
  sorry

/- The textbook's part (ii), concerning finite exchangeable families, is bibliographic prose
rather than a mathematical statement and is therefore not encoded as a Lean declaration here. -/

end
