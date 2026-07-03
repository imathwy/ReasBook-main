import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_19 (from Items/Chap15) -/
open MeasureTheory

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

-- Proof sketch: rewrite `charFun μ t - charFun μ s` as the integral of
-- `(Complex.exp (⟪x, t - s⟫ * Complex.I) - 1) * Complex.exp (⟪x, s⟫ * Complex.I)`, apply the
-- Cauchy--Schwarz inequality, use that the exponential factor has norm `1`, and identify the
-- remaining integral with `2 * (1 - Complex.re (charFun μ (t - s)))`.
/-- Lemma 15.19: For a probability measure on `ℝ^d`, the squared modulus of the increment of the
characteristic function is bounded by twice the real-part defect at the difference frequency. -/
theorem sq_norm_charFun_sub_le_two_mul_one_sub_re_charFun_sub
    (μ : Measure E) [IsProbabilityMeasure μ] (s t : E) :
    Complex.normSq (charFun μ t - charFun μ s) ≤
      2 * (1 - Complex.re (charFun μ (t - s))) := sorry
