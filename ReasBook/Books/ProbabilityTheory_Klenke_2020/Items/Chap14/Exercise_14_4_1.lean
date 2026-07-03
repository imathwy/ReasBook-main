import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_46

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped MeasureTheory Topology

section

variable {d : ℕ}
variable {ν : NNReal → ProbabilityMeasure (Fin d → ℝ)} [IsContinuousConvolutionSemigroup ν]

namespace IsContinuousConvolutionSemigroup

-- Proof sketch: use the semigroup identity to rewrite nearby time marginals as convolutions with
-- increment laws tending to `δ₀`; for `s > t`, use `ν s = ν t ∗ ν (s - t)`, and for `s < t`, use
-- `ν t = ν s ∗ ν (t - s)`. The defining continuity at `0` then shows the increment laws converge
-- weakly to `δ₀`, and convolution with `δ₀` is the identity.
/-- Exercise 14.4.1: a continuous convolution semigroup on the chapter's `ℝ^d` model is
continuous at every positive time. -/
theorem continuousAt_of_pos {t : NNReal} (ht : 0 < t) :
    ContinuousAt ν t := by
  sorry

/-- Reformulation of Exercise 14.4.1 as the corresponding limit statement. -/
theorem tendsto_of_pos {t : NNReal} (ht : 0 < t) :
    Tendsto ν (𝓝 t) (𝓝 (ν t)) :=
  (continuousAt_of_pos ht).tendsto

end IsContinuousConvolutionSemigroup

end
