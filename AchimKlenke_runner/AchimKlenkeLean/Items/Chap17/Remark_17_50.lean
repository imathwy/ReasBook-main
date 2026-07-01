import AchimKlenkeLean.Items.Chap14.Lemma_14_27
import AchimKlenkeLean.Items.Chap17.Definition_17_30
import AchimKlenkeLean.Items.Chap17.Exercise_17_6_6
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory unitInterval
open unitInterval

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E]

section GeneralClaim

variable {Ω : Type v} [MeasurableSpace Ω]
variable [DiscreteMeasurableSpace E]

/- Remark 17.50 (1): the uniqueness-up-to-scale statement for nonzero invariant measures of an
irreducible recurrent discrete chain is already the owner theorem from Exercise 17.6.6. -/
recall invariantMeasures_unique_up_to_scale_of_irreducible_recurrent

end GeneralClaim

section BiasedWalk

/- Layering for Remark 17.50:
- source-facing primitive data: the biased step law on the increment space `ℤ`;
- core/canonical owner: `biasedSimpleRandomWalkStepPMF r : PMF ℤ`;
- bridge/view: the translation kernel
  `dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF r).toMeasure` and its singleton
  transition probabilities. -/

/-- The one-step increment law of the one-dimensional biased nearest-neighbor walk: jump to `1`
with probability `r` and to `-1` with probability `1 - r`. -/
def biasedSimpleRandomWalkStepPMF (r : I) : PMF ℤ :=
  (PMF.bernoulli (toNNReal r) (by simpa using r.2.2)).map fun b ↦ if b then (1 : ℤ) else -1

-- Proof sketch: expand `dirac_convolution_kernel`; translating the two-point increment measure by
-- `x` gives masses `r` and `1 - r` at `x + 1` and `x - 1`, and no mass elsewhere.
/-- Evaluating the owner kernel of the biased nearest-neighbor walk on a singleton target recovers
the usual nearest-neighbor matrix entry formula. -/
theorem biasedSimpleRandomWalkKernel_apply_singleton (r : I) (x y : ℤ) :
    dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF r).toMeasure x {y} =
      if y = x + 1 then ENNReal.ofReal (r : ℝ)
      else if y = x - 1 then ENNReal.ofReal (1 - (r : ℝ))
      else 0 :=
  sorry

/-- The geometric weighted counting measure on `ℤ` with singleton masses
`(r / (1 - r)) ^ x`, used as the second invariant measure in the asymmetric random-walk example.
-/
def biasedSimpleRandomWalkGeometricInvariantMeasure (r : I) : Measure ℤ :=
  Measure.count.withDensity
    (fun x : ℤ ↦ ENNReal.ofReal ((((r : ℝ) / (1 - (r : ℝ))) : ℝ) ^ x))

-- Proof sketch: unfold `biasedSimpleRandomWalkGeometricInvariantMeasure`; on a discrete state
-- space,
-- `Measure.count.withDensity` assigns to `{x}` exactly the density value at `x`.
/-- The second example invariant measure gives singleton mass `(r / (1 - r)) ^ x` at `{x}`. -/
theorem biasedSimpleRandomWalkGeometricInvariantMeasure_apply_singleton (r : I) (x : ℤ) :
    biasedSimpleRandomWalkGeometricInvariantMeasure r {x} =
      ENNReal.ofReal ((((r : ℝ) / (1 - (r : ℝ))) : ℝ) ^ x) := sorry

-- Proof sketch: solve the discrete stationarity equation
-- `μ = dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF r).toMeasure ∘ₘ μ`; the
-- recurrence relation on singleton masses has solution space spanned by the constant and
-- geometric weights.
/-- Remark 17.50 (2): for the nearest-neighbor random walk on `ℤ` that jumps right with
probability `r` and left with probability `1 - r`, the invariant measures are exactly the
nonnegative linear combinations of the counting measure and the geometric weighted counting measure
from the remark. -/
theorem biasedSimpleRandomWalk_invariantMeasure_iff
    (r : I) (hr0 : 0 < (r : ℝ)) (hr1 : (r : ℝ) < 1) (μ : Measure ℤ) :
    Kernel.Invariant (dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF r).toMeasure) μ ↔
      ∃ a b : ℝ≥0∞,
        μ = a • (Measure.count : Measure ℤ) +
          b • biasedSimpleRandomWalkGeometricInvariantMeasure r :=
  sorry

variable {Ω : Type v} [MeasurableSpace Ω]

-- Proof sketch: combine the recurrence criterion for the biased nearest-neighbor walk on `ℤ`
-- with irreducibility of the walk for `0 < r < 1`; outside the symmetric case `r = 1 / 2`, all
-- states are transient.
/-- Remark 17.50 (3): the asymmetric nearest-neighbor random walk on `ℤ` is transient exactly
when `r ≠ 1 / 2`. Here transience is expressed by saying that every state is transient. -/
theorem biasedSimpleRandomWalk_allStatesTransient_iff_ne_half
    (r : I) (hr0 : 0 < (r : ℝ)) (hr1 : (r : ℝ) < 1)
    (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ)
    [IsMarkovProcessRealization
      (fun n ↦ dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF r).toMeasure ^ n) P X] :
    (∀ x : ℤ, IsTransientState P X x) ↔ (r : ℝ) ≠ 1 / 2 := sorry

-- Proof sketch: evaluate both measures on singleton sets; when `r ≠ 1 / 2`, the geometric ratio
-- `r / (1 - r)` is not `1`, so the singleton masses cannot agree for all `x`.
/-- Remark 17.50 (4): in the transient regime `r ≠ 1 / 2`, the two explicit invariant measures of
the asymmetric random walk are distinct. -/
theorem biasedSimpleRandomWalkGeometricInvariantMeasure_ne_count
    (r : I) (hr0 : 0 < (r : ℝ)) (hr1 : (r : ℝ) < 1) (hrne : (r : ℝ) ≠ 1 / 2) :
    biasedSimpleRandomWalkGeometricInvariantMeasure r ≠ (Measure.count : Measure ℤ) := sorry

end BiasedWalk

end ProbabilityTheory
