import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap09.Definition_9_1
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap09.Example_9_8
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap14.Definition_14_46
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

namespace MeasureTheory.ProbabilityMeasure

/- Corollary 16.10 is `source-facing`: it still asserts existence of the semigroup and of a
process with the prescribed increment laws. The owner abstractions already present earlier in the
project are:
- `ProbabilityMeasure.IsInfinitelyDivisible` for the law-side hypothesis,
- `IsContinuousConvolutionSemigroup` for the semigroup of marginals,
- `HasStationaryIndependentIncrements` for the process-side increment structure on the canonical
  path-space coordinate process.

The explicit increment-law conclusion remains the source-facing bridge data, but the ambient
realization is refined to the canonical path-space coordinate process from Chapter 14 rather than
an arbitrary auxiliary probability space with a separate chosen process. -/

-- Proof sketch: use Corollaries 16.7 and 16.8 to build the continuous convolution semigroup
-- `ν`, with `ν 1 = μ`, from the convolution roots of the characteristic function of `μ`.
-- Then apply the Chapter 14 path-space realization theorem to obtain a probability measure on
-- `ℝ^[0,∞)` whose coordinate process has stationary independent increments and increment law
-- `ν (t - s)` over `[s, t]`.
/-- Corollary 16.10: every infinitely divisible probability measure on `ℝ` occurs as the time-one
marginal of a continuous convolution semigroup and as the increment law of a real-valued process
with independent increments; because the increment law depends only on `t - s`, the process has
stationary increments as well. -/
theorem exists_continuousConvolutionSemigroup_with_increment_process
    (μ : ProbabilityMeasure ℝ) (hμ : IsInfinitelyDivisible μ) :
    ∃ ν : NNReal → ProbabilityMeasure ℝ,
      IsContinuousConvolutionSemigroup ν ∧
        ν 1 = μ ∧
          ∃ P : ProbabilityMeasure (NNReal → ℝ),
            IsStochasticProcess (Function.eval : NNReal → (NNReal → ℝ) → ℝ) ∧
              HasStationaryIndependentIncrements
                  (Function.eval : NNReal → (NNReal → ℝ) → ℝ)
                  (P : Measure (NNReal → ℝ)) ∧
                ∀ ⦃s t : NNReal⦄, s ≤ t →
                  HasLaw (fun ω : NNReal → ℝ ↦ ω t - ω s) (ν (t - s) : Measure ℝ)
                    (P : Measure (NNReal → ℝ)) := sorry

end MeasureTheory.ProbabilityMeasure
