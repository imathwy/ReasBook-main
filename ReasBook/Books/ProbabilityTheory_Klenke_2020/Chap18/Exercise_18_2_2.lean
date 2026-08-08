import ProbabilityTheory_Klenke_2020.Chap18.Definition_18_5
import ProbabilityTheory_Klenke_2020.Chap18.Example_18_6
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable [DiscreteMeasurableSpace (E × E)]
variable {Ω : Type v} [MeasurableSpace Ω]

variable {p : E → E → ℝ≥0∞}
variable {P : E × E → ProbabilityMeasure Ω} {Z : ℕ → Ω → E × E}
variable [IsMarkovProcessRealization
  (fun n : ℕ ↦ discreteMatrixKernel (independentCoalescentMatrix p) ^ n) P Z]

-- Proof sketch: view `Z` as the Markov chain on `E × E` with transition matrix
-- `independentCoalescentMatrix p`. The formulas from Example 18.6 show that the first and second
-- coordinate marginals of one step are both given by `p`; iterating the Markov property for `Z`
-- therefore identifies the coordinate laws at time `n` with `(discreteMatrixKernel p ^ n) x` and
-- `(discreteMatrixKernel p ^ n) y`, while the coordinate processes inherit the natural Markov
-- property from the bivariate chain.
/-- Exercise 18.2.2: if `Z` is the bivariate process from Example 18.6 with transition matrix
`independentCoalescentMatrix p`, then its coordinate process is a Markov coupling for `p`. In
other words, writing `X n ω = (Z n ω).1` and `Y n ω = (Z n ω).2`, the process `(X, Y)` is a
coupling with transition matrix `\bar p`. -/
theorem independentCoalescentChain_isMarkovCoupling :
    IsMarkovCoupling p P Z := sorry

end ProbabilityTheory
