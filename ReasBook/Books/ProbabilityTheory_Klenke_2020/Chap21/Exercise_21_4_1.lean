import Mathlib
import ProbabilityTheory_Klenke_2020.Chap21.Definition_21_21

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u}

/-- The running supremum `|X|*_T` of a real-valued continuous-time process on the interval
`[0, T]`, represented canonically as an `ℝ≥0∞`-valued interval supremum. -/
def continuousRunningAbsSup (X : NNReal → Ω → ℝ) (T : NNReal) : Ω → ℝ≥0∞ :=
  fun ω ↦ ⨆ t : Set.Icc (0 : NNReal) T, ENNReal.ofReal |X t ω|

syntax:max "|" term "|*_" term : term

macro_rules
  | `(|$X|*_$T) => `(continuousRunningAbsSup $X $T)

-- Proof sketch: unfold `|X|*_T`; the statement is exactly its defining equation.
/-- Unfolding formula for the running supremum `|X|*_T`. -/
theorem continuousRunningAbsSup_apply (X : NNReal → Ω → ℝ) (T : NNReal) (ω : Ω) :
    (|X|*_T) ω =
      ⨆ t : Set.Icc (0 : NNReal) T, ENNReal.ofReal |X t ω| :=
  rfl

section DoobLp

variable [mΩ : MeasurableSpace Ω]

variable {μ : Measure Ω} [IsFiniteMeasure μ]
variable {ℱ : Filtration NNReal mΩ}
variable {X : NNReal → Ω → ℝ}

-- Proof sketch: stop the process at the first time its absolute value reaches `threshold`, reduce
-- to bounded stopping times, and apply optional sampling to the nonnegative submartingale
-- `t ↦ |X t|^p`; right continuity identifies the stopped event with the hitting event of the
-- running supremum.
/-- Exercise 21.4.1 (1): on a finite measure space, for a martingale or nonnegative submartingale
with right-continuous paths, Doob's `L^p` tail estimate controls the event `{|X|*_T ≥ λ}` by the
terminal `p`-th moment. -/
theorem doobLp_tail_bound_rightContinuous
    (hX : Martingale X ℱ μ ∨ Submartingale X ℱ μ ∧ 0 ≤ X)
    (hX_rc : HasRightContinuousPaths X)
    {p threshold : ℝ} (hp : 1 ≤ p) (hthreshold : 0 < threshold) (T : NNReal) :
    ENNReal.ofReal (Real.rpow threshold p) *
        μ {ω | ENNReal.ofReal threshold ≤ (|X|*_T) ω} ≤
      ∫⁻ ω, ENNReal.ofReal (Real.rpow |X T ω| p) ∂μ := sorry

end DoobLp

section RunningSupMoment

variable [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω}

-- Proof sketch: for every sample point `ω`, the terminal value `|X T ω|` is one of the values
-- whose supremum defines `|X|*_T ω`, so monotonicity of `x ↦ x^p` on `ℝ≥0∞` for `p ≥ 0` gives
-- `|X T ω|^p ≤ (|X|*_T ω)^p`; integrate this pointwise inequality.
/-- Exercise 21.4.1 (2): for every nonnegative exponent `p`, the terminal `p`-th moment is bounded
by the `p`-th moment of `|X|*_T`. This is the left inequality in clause `(ii)`, stated with the
minimal exponent range used by its pointwise proof. -/
theorem terminalMoment_le_continuousRunningAbsSupMoment
    {p : ℝ} (hp : 0 ≤ p) (X : NNReal → Ω → ℝ) (T : NNReal) :
    ∫⁻ ω, ENNReal.ofReal (Real.rpow |X T ω| p) ∂μ ≤
      ∫⁻ ω, ((|X|*_T) ω) ^ p ∂μ := sorry

end RunningSupMoment

section DoobLp

variable [mΩ : MeasurableSpace Ω]

variable {μ : Measure Ω} [IsFiniteMeasure μ]
variable {ℱ : Filtration NNReal mΩ}
variable {X : NNReal → Ω → ℝ}

-- Proof sketch: integrate the tail estimate from clause `(1)` against `p λ^(p-1)`, use the layer-
-- cake representation of the `p`-th moment of `|X|*_T`, and optimize the resulting Hölder bound to
-- obtain the classical constant `(p / (p - 1))^p`.
/-- Exercise 21.4.1 (3): on a finite measure space, for `p > 1`, the `p`-th moment of `|X|*_T` is
bounded by the classical Doob constant `(p / (p - 1))^p` times the terminal `p`-th moment. This
is the right inequality in clause `(ii)`. -/
theorem continuousRunningAbsSupMoment_le_doobConstant_mul_terminalMoment
    (hX : Martingale X ℱ μ ∨ Submartingale X ℱ μ ∧ 0 ≤ X)
    (hX_rc : HasRightContinuousPaths X)
    {p : ℝ} (hp : 1 < p) (T : NNReal) :
    ∫⁻ ω, ((|X|*_T) ω) ^ p ∂μ ≤
      ENNReal.ofReal (Real.rpow (p / (p - 1)) p) *
        ∫⁻ ω, ENNReal.ofReal (Real.rpow |X T ω| p) ∂μ := sorry

end DoobLp

-- Proof sketch: choose a filtered probability space carrying a martingale or a nonnegative
-- submartingale with a jump visible only at a non-right-continuous exceptional time; the terminal
-- `p`-th moment stays too small compared with the probability of a large earlier excursion, so the
-- tail bound from clause `(1)` fails.
/-- Exercise 21.4.1 (4): right continuity is essential. There exists a martingale or a nonnegative
submartingale without right-continuous paths for which the tail estimate in clause `(i)` fails. -/
theorem exists_process_without_rightContinuous_paths_failing_doobLp_tail_bound :
    ∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω') (μ : Measure Ω') (ℱ : Filtration NNReal mΩ')
      (X : NNReal → Ω' → ℝ) (T : NNReal) (p threshold : ℝ),
      IsProbabilityMeasure μ ∧
        (Martingale X ℱ μ ∨ Submartingale X ℱ μ ∧ 0 ≤ X) ∧
        ¬ HasRightContinuousPaths X ∧
        1 ≤ p ∧
        0 < threshold ∧
        ∫⁻ ω, ENNReal.ofReal (Real.rpow |X T ω| p) ∂μ <
          ENNReal.ofReal (Real.rpow threshold p) *
            μ {ω | ENNReal.ofReal threshold ≤ (|X|*_T) ω} := sorry

end ProbabilityTheory
