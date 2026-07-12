import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_70

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory Topology

noncomputable section

universe u

namespace ProbabilityTheory

/- Exercise 21.10.3 is `source-facing` existential content.

Domain-style sampling for the owner abstraction:
* `IsContinuousLocalMartingale` from Definition 21.66 is the chapter owner for the process `M`.
* `continuousSquareVariationProcess` from Theorem 21.70 is the canonical bracket owner, so the
  bracket is derived data rather than an extra primitive field.
* `IsStoppingTime` and `stoppedValue` are the existing owner-level interfaces for the stopping-time
  part of the statement.

Primitive data versus derived API:
* primitive data: the filtered probability space, the process `M`, and the stopping time `τ`;
* derived data: the bracket process `⟨M⟩ = continuousSquareVariationProcess hM`.

Accordingly, the exercise is stated directly with the canonical bracket owner instead of a local
package carrying a separate square-variation witness. -/

-- Proof sketch: take a Brownian motion `B` and stop it at an almost surely finite stopping time
-- with infinite mean, such as a return time to `0`; then `⟨B⟩_τ = τ` has infinite expectation,
-- while `B_τ = 0` almost surely keeps the stopped second moment finite.
/-- Exercise 21.10.3: there exists a continuous local martingale `M` with `M_0 = 0` and an almost
surely finite stopping time `τ` such that the stopped square variation has infinite expectation,
but the stopped second moment `E[M_τ^2]` is not infinite. -/
theorem exists_infinite_bracket_expectation_without_infinite_stopped_square_expectation :
    ∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω'),
      letI := mΩ'
      ∃ (μ : Measure Ω') (_ : IsProbabilityMeasure μ) (ℱ : Filtration NNReal mΩ')
        (M : NNReal → Ω' → ℝ) (τ : Ω' → ENNReal)
        (hM : IsContinuousLocalMartingale ℱ μ M),
        (∀ ω : Ω', M 0 ω = 0) ∧
          IsStoppingTime ℱ τ ∧
          (∀ᵐ ω ∂μ, τ ω ≠ ∞) ∧
          (∫⁻ ω,
              ENNReal.ofReal
                (stoppedValue (continuousSquareVariationProcess hM) τ ω) ∂μ) = ∞ ∧
          (∫⁻ ω, ENNReal.ofReal ((stoppedValue M τ ω) ^ (2 : ℕ)) ∂μ) ≠ ∞ := sorry

end ProbabilityTheory
