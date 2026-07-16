import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap17.Definition_17_30
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap17.Remark_17_50
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap19.Example_19_10
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap19.Theorem_19_25
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory unitInterval

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/- `source-facing`: Example 19.27 fixes the asymmetric nearest-neighbor conductance network on
`ℤ` coming from the biased walk parameter `p`.
`core/canonical`: the Chapter 19 owner `effectiveResistanceToInfinity` for conductance networks.
`bridge/view`: `conductanceTransitionMatrix` identifies the resulting conductance walk with the
canonical biased nearest-neighbor kernel from Chapter 17. -/

/-- The conductance family on `ℤ` from Example 19.27: the edge `{x, x + 1}` carries weight
`(p / (1 - p)) ^ x`, and all non-nearest-neighbor pairs have conductance `0`. The parameter
`p : I` is the canonical biased-walk probability from Chapter 17. -/
def asymmetricNearestNeighborWalkConductance (p : I) : ℤ → ℤ → ℝ≥0∞ :=
  fun x y ↦
    if y = x + 1 then
      ENNReal.ofReal (((p : ℝ) / (1 - (p : ℝ))) ^ x)
    else if y = x - 1 then
      ENNReal.ofReal (((p : ℝ) / (1 - (p : ℝ))) ^ y)
    else
      0

-- Proof sketch: unfold `asymmetricNearestNeighborWalkConductance`; only the two nearest-neighbor
-- cases survive, with the right-edge weight indexed by the left endpoint.
/-- Evaluating the Example 19.27 conductance family gives the prescribed geometric nearest-neighbor
weights. -/
theorem asymmetricNearestNeighborWalkConductance_apply (p : I) (x y : ℤ) :
    asymmetricNearestNeighborWalkConductance p x y =
      if y = x + 1 then
        ENNReal.ofReal (((p : ℝ) / (1 - (p : ℝ))) ^ x)
      else if y = x - 1 then
        ENNReal.ofReal (((p : ℝ) / (1 - (p : ℝ))) ^ y)
      else
        0 := sorry

-- Proof sketch: compute the row sum of `asymmetricNearestNeighborWalkConductance p` at `x`,
-- namely `(p / (1 - p)) ^ x + (p / (1 - p)) ^ (x - 1)`, factor out the common geometric term, and
-- simplify the quotient defining `conductanceTransitionMatrix`; the resulting singleton masses are
-- exactly the canonical biased-walk kernel from Remark 17.50.
/-- The Example 19.27 conductances reproduce the canonical biased nearest-neighbor walk kernel on
`ℤ`. -/
theorem conductanceTransitionMatrix_asymmetricNearestNeighborWalkConductance
    (p : I) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    conductanceTransitionMatrix (asymmetricNearestNeighborWalkConductance p) =
      fun x y ↦
        dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure x {y} := sorry

-- Proof sketch: the ratio `q = (1 - p) / p` satisfies `|q| < 1` when `p > 1 / 2`, so the
-- resistance sum is a convergent geometric series.
/-- The resistance series attached to the Example 19.27 conductance model is summable when
`p > 1 / 2`. -/
theorem summable_asymmetricNearestNeighborWalk_resistanceSeries
    (p : I) (hp : 1 / 2 < (p : ℝ)) :
    Summable (fun n : ℕ ↦ ((1 - (p : ℝ)) / (p : ℝ)) ^ n) := sorry

-- Proof sketch: apply the geometric-series formula with ratio `((1 - p) / p)`, then rewrite
-- `1 / (1 - (1 - p) / p)` as `p / (2 * p - 1)`.
/-- The geometric resistance series in Example 19.27 sums to `p / (2p - 1)`. -/
theorem asymmetricNearestNeighborWalk_resistanceSeries_eq
    (p : I) (hp : 1 / 2 < (p : ℝ)) :
    ∑' n : ℕ, ((1 - (p : ℝ)) / (p : ℝ)) ^ n = (p : ℝ) / (2 * (p : ℝ) - 1) := sorry

-- Proof sketch: approximate infinity by the cofinite boundaries `{-N, ..., N}ᶜ`. The right-hand
-- branch from `0` to `N + 1` is a series network with edge resistances
-- `((1 - p) / p)^n`, while the left branch only lowers the effective resistance by placing an
-- additional parallel path in the finite network. Passing to the limit yields the claimed
-- Chapter 19 resistance bound.
/-- Example 19.27: if `p > 1 / 2`, then the effective resistance from `0` to `∞` in the
asymmetric nearest-neighbor conductance network is bounded by `p / (2p - 1)`. -/
theorem asymmetricNearestNeighborWalk_effectiveResistanceToInfinity_le
    (p : I) (hp : 1 / 2 < (p : ℝ))
    (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ n)
      P X] :
    effectiveResistanceToInfinity (asymmetricNearestNeighborWalkConductance p) P X 0 ≤
      ENNReal.ofReal ((p : ℝ) / (2 * (p : ℝ) - 1)) := sorry

-- Proof sketch: combine the owner-level bound above with the finiteness of `ENNReal.ofReal`.
/-- In particular, the effective resistance from `0` to `∞` in Example 19.27 is finite when
`p > 1 / 2`. -/
theorem asymmetricNearestNeighborWalk_effectiveResistanceToInfinity_lt_top
    (p : I) (hp : 1 / 2 < (p : ℝ))
    (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ n)
      P X] :
    effectiveResistanceToInfinity (asymmetricNearestNeighborWalkConductance p) P X 0 < ∞ := sorry

-- Proof sketch: the finite-resistance theorem above rules out recurrence at `0` via
-- `effectiveConductanceToInfinity_eq_zero_iff_effectiveResistanceToInfinity_eq_top`. Since the
-- biased nearest-neighbor walk is the canonical Chapter 17 walk with parameter `p > 1 / 2`, the
-- walk lies in the transient regime and hence every state is transient.
/-- Example 19.27: if `p > 1 / 2`, then every state of the asymmetric nearest-neighbor random walk
on `ℤ` with jump probabilities `p` to the right and `1 - p` to the left is transient. -/
theorem asymmetricNearestNeighborWalk_allStatesTransient_of_half_lt
    (p : I) (hp : 1 / 2 < (p : ℝ))
    (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel (biasedSimpleRandomWalkStepPMF p).toMeasure ^ n)
      P X] :
    ∀ x : ℤ, IsTransientState P X x := sorry

end ProbabilityTheory
