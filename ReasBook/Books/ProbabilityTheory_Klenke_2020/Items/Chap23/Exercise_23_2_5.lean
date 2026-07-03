import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap23.Theorem_23_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

/-- At the origin, the chapter's extended logarithmic moment-generating function of a Cauchy law
equals `0`. -/
theorem cauchyMeasure_extendedLogMomentGeneratingFunction_zero
    (x₀ : ℝ) (γ : NNReal) :
    Λ(id; cauchyMeasure x₀ γ) 0 = 0 := sorry

-- Proof sketch: for every nonzero `t`, one of the tails of `exp (t x)` against a nondegenerate
-- Cauchy density is nonintegrable, so the chapter's extended logarithmic moment-generating
-- function takes the value `⊤`.
/-- Away from the origin, the chapter's extended logarithmic moment-generating function of a
nondegenerate Cauchy law equals `⊤`. -/
theorem cauchyMeasure_extendedLogMomentGeneratingFunction_eq_top
    (x₀ : ℝ) {γ : NNReal} (hγ : γ ≠ 0) {t : ℝ} (ht : t ≠ 0) :
    Λ(id; cauchyMeasure x₀ γ) t = ⊤ := sorry

-- Proof sketch: after substituting the explicit Cauchy formula for `Λ`, every term with `t ≠ 0`
-- becomes `-∞`, while the term `t = 0` contributes `0`; hence the supremum defining the
-- Legendre-Fenchel transform is `0` for every `x`.
/-- Exercise 23.2.5: for a nondegenerate Cauchy law, the chapter's extended logarithmic
moment-generating function is `Λ(0) = 0` and `Λ(t) = ⊤` for `t ≠ 0`, so its Legendre-Fenchel
transform is the trivial rate function `Λ*(x) = 0` for every `x`. This means that Theorem 23.11
yields only the degenerate large-deviation picture with zero exponential rate in the Cauchy
case. -/
theorem cauchyMeasure_legendreFenchelRateFunction_eq_zero
    (x₀ : ℝ) {γ : NNReal} (hγ : γ ≠ 0) (x : ℝ) :
    legendreFenchelRateFunction (Λ(id; cauchyMeasure x₀ γ)) x = 0 := sorry

end ProbabilityTheory
