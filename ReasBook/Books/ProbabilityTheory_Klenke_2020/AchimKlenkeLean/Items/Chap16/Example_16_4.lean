import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap03.Exercise_3_1_1
import ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_3

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped ENNReal MeasureTheory

noncomputable section

/-- The logarithmic jump measure with masses `((1 - p)^(k + 1)) / (k + 1)` at the positive
integers `k + 1`, viewed as a measure on `ℝ`. -/
noncomputable def logarithmicJumpMeasure (p : ℝ) : Measure ℝ :=
  Measure.sum
    (fun k : ℕ ↦
      ENNReal.ofReal ((1 - p) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) •
        Measure.dirac (((k + 1 : ℕ) : ℝ)))

-- Proof sketch: in the defining weighted Dirac sum, only the atom at `k + 1` contributes to the
-- singleton `{k + 1}`.
/-- The logarithmic jump measure assigns mass `((1 - p)^(k + 1)) / (k + 1)` to the atom `k + 1`.
-/
theorem logarithmicJumpMeasure_apply_natSucc (p : ℝ) (k : ℕ) :
    logarithmicJumpMeasure p {(((k + 1 : ℕ) : ℝ))} =
      ENNReal.ofReal ((1 - p) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) := sorry

-- Proof sketch: substitute `k = 0` into the defining formula and simplify the zeroth binomial
-- coefficient and the zeroth power in the canonical mass formula `negativeBinomialMass`.
/-- The atom at `0` in the canonical negative-binomial mass formula is `p^r`. -/
theorem negativeBinomialMass_zero (r p : ℝ) :
    negativeBinomialMass r p 0 = p ^ r := sorry

-- Proof sketch: unfold the pushforward of the canonical `ℕ`-valued negative-binomial measure,
-- then expand that measure by its singleton masses.
/-- The real-valued negative-binomial law is the weighted Dirac sum with coefficients
`negativeBinomialMass r p k` at the atoms `k ∈ ℕ ⊂ ℝ`. -/
theorem negativeBinomialMeasure_map_def (r p : ℝ) (hr : 0 < r) (hp : 0 < p)
    (hp_le_one : p ≤ 1) :
    (negativeBinomialMeasure r p hr hp hp_le_one).map (fun k : ℕ ↦ (k : ℝ)) =
      Measure.sum
        (fun k : ℕ ↦
          ENNReal.ofReal (negativeBinomialMass r p k) • Measure.dirac ((k : ℝ))) := sorry

-- Proof sketch: for `0 < p ≤ 1`, the logarithmic series
-- `∑_{k ≥ 0} (1 - p)^(k + 1) / (k + 1)` converges to `-log p`, so the total mass of
-- `logarithmicJumpMeasure p` is finite.
theorem logarithmicJumpMeasure_isFiniteMeasure (p : ℝ) (hp : 0 < p) (hp_le_one : p ≤ 1) :
    IsFiniteMeasure (logarithmicJumpMeasure p) := sorry

private theorem scaledLogarithmicJumpMeasure_isFiniteMeasure
    (r p : ℝ) (hp : 0 < p) (hp_le_one : p ≤ 1) :
    IsFiniteMeasure (Real.toNNReal r • logarithmicJumpMeasure p) := by
  letI := logarithmicJumpMeasure_isFiniteMeasure p hp hp_le_one
  infer_instance

-- Proof sketch: compute the singleton masses of the negative-binomial law, identify the candidate
-- jump measure from the `r ↓ 0` limit, evaluate the compound-Poisson characteristic function as
-- the logarithmic series from the example, and conclude by uniqueness of finite measures from
-- their characteristic functions. The source parameterization by rate `r` and jump measure is
-- realized through the canonical owner `compoundPoissonMeasure` applied to the finite intensity
-- measure `(Real.toNNReal r) • logarithmicJumpMeasure p`.
/-- Example 16.4: for `r > 0` and `p ∈ (0,1]`, the negative-binomial law equals the
canonical compound-Poisson law whose intensity measure is
`(Real.toNNReal r) • logarithmicJumpMeasure p`, where the jump measure has mass
`((1 - p)^k) / k` at each positive integer `k`. -/
theorem negativeBinomialMeasure_map_eq_compoundPoisson_logarithmicJump
    (r p : ℝ) (hr : 0 < r) (hp : 0 < p) (hp_le_one : p ≤ 1) :
    (negativeBinomialMeasure r p hr hp hp_le_one).map (fun k : ℕ ↦ (k : ℝ)) =
      letI : IsFiniteMeasure (Real.toNNReal r • logarithmicJumpMeasure p) :=
        scaledLogarithmicJumpMeasure_isFiniteMeasure r p hp hp_le_one
      (compoundPoissonMeasure ((Real.toNNReal r) • logarithmicJumpMeasure p) : Measure ℝ) := sorry
