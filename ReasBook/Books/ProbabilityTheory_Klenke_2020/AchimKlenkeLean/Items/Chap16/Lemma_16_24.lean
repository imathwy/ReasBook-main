import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap16.Definition_16_1
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap16.Definition_16_20
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap16.Theorem_16_17

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

-- Proof sketch: the log-characteristic function of the `n`-fold convolution power is `n` times
-- the original exponent, so the Gaussian coefficient, the drift coefficient, and the Lévy
-- measure all scale by `n`.
/-- Lemma 16.24 (1): if a probability law on `ℝ` has Lévy--Khinchin triple `(σ², b, ν)`, then the
law of the sum of `n` i.i.d. copies has Lévy--Khinchin triple `((n : ℝ) σ², (n : ℝ) b, n ν)`,
realized in Lean as the `n`th convolution power. -/
theorem pow_hasLevyKhinchinRepresentation
    (μ : ProbabilityMeasure ℝ) (τ : LevyKhinchinTriple) (n : ℕ+)
    (hτ : HasLevyKhinchinRepresentation μ τ) :
    HasLevyKhinchinRepresentation (μ ^ (n : ℕ))
      { sigma2 := (n : ℝ) * τ.sigma2
        b := (n : ℝ) * τ.b
        ν := (n : ℕ) • τ.ν } := sorry

-- Proof sketch: rewrite the log-characteristic function of the affine image law as `ψ (a t) + i d
-- t`, then change the truncation indicator from `1_{|x| < 1}` to `1_{|x| < 1 / a}`. This yields
-- the new Gaussian coefficient, the corrected drift term, and the pushed-forward Lévy measure.
/-- Lemma 16.24 (2): if a probability law on `ℝ` has Lévy--Khinchin triple `(σ², b, ν)`, then the
affine image law of `a X + d` for `a > 0` has Lévy--Khinchin triple
`(a² σ², a b + d + a ∫ ((1_{|x| < 1 / a} - 1_{|x| < 1}) x) dν, ν ∘ m_a⁻¹)`. -/
theorem map_affine_hasLevyKhinchinRepresentation
    (μ : ProbabilityMeasure ℝ) (τ : LevyKhinchinTriple)
    (hτ : HasLevyKhinchinRepresentation μ τ) {a d : ℝ} (ha : 0 < a) :
    HasLevyKhinchinRepresentation
      (μ.map (measurable_affineMap a d).aemeasurable)
      { sigma2 := a ^ (2 : ℕ) * τ.sigma2
        b := a * τ.b + d +
          a * ∫ x : ℝ, ((if |x| < 1 / a then x else 0) - (if |x| < 1 then x else 0)) ∂τ.ν
        ν := Measure.map (fun x : ℝ ↦ a * x) τ.ν } := sorry

end MeasureTheory.ProbabilityMeasure
