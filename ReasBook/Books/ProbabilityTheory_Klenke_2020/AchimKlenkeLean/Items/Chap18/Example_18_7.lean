import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap17.Theorem_17_39
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap18.Definition_18_5
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap18.Example_18_6
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

/- Layering for Example 18.7:
- source-facing: the lazy nearest-neighbor walk on `ℤ` and the coalescing independent-chain
  coupling built from it;
- core/canonical owner: `lazyNearestNeighborStepPMF : PMF ℤ`;
- bridge/view: `lazyNearestNeighborTransitionMatrix`, obtained from
  `dirac_convolution_kernel lazyNearestNeighborStepPMF.toMeasure`, and the coalescent transition
  matrix `independentCoalescentMatrix lazyNearestNeighborTransitionMatrix`. -/

/-- The one-step increment law of the lazy nearest-neighbor walk on `ℤ`: jump by `-1`, `0`, or
`1` with probability `1 / 3` each. -/
def lazyNearestNeighborStepPMF : PMF ℤ :=
  (PMF.uniformOfFintype (Fin 3)).map fun i ↦ ((i : ℕ) : ℤ) - 1

/-- The transition matrix of the lazy nearest-neighbor walk on `ℤ`, viewed as the singleton-mass
bridge of the translation kernel driven by `lazyNearestNeighborStepPMF`. -/
abbrev lazyNearestNeighborTransitionMatrix : ℤ → ℤ → ℝ≥0∞ :=
  fun x y ↦ dirac_convolution_kernel lazyNearestNeighborStepPMF.toMeasure x {y}

-- Proof sketch: expand `dirac_convolution_kernel`; translating the step law by `x` shifts the
-- three equiprobable increments `-1`, `0`, `1` to `x - 1`, `x`, and `x + 1`.
/-- Evaluating `lazyNearestNeighborTransitionMatrix` on a singleton target recovers the usual lazy
nearest-neighbor transition probabilities. -/
theorem lazyNearestNeighborTransitionMatrix_apply (x y : ℤ) :
    lazyNearestNeighborTransitionMatrix x y =
      if |x - y| ≤ 1 then
        1 / 3
      else
        0 := sorry

section

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: before the two coordinates meet, the chain evolves with transition matrix
-- `independentCoalescentMatrix lazyNearestNeighborTransitionMatrix`, so the difference process is
-- a centered one-dimensional lazy random walk. Theorem 17.39(4) gives recurrence, hence the
-- difference hits `0` almost surely from every initial displacement. Once `Z` reaches the
-- diagonal, Example 18.6 keeps it there forever, so the tail disagreement probability tends to
-- `0`; together with the coordinate-chain property from the coalescent transition matrix, this is
-- exactly `IsSuccessfulMarkovCoupling`.
/-- Example 18.7: every realization of the independent coalescent chain associated with the lazy
nearest-neighbor walk on `ℤ` is a successful Markov coupling for that walk. -/
theorem lazyNearestNeighborIndependentCoalescent_isSuccessfulMarkovCoupling
    (P : ℤ × ℤ → ProbabilityMeasure Ω) (Z : ℕ → Ω → ℤ × ℤ)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦
        discreteMatrixKernel
          (independentCoalescentMatrix lazyNearestNeighborTransitionMatrix) ^ n)
      P Z] :
    IsSuccessfulMarkovCoupling lazyNearestNeighborTransitionMatrix P Z := sorry

end

end ProbabilityTheory
