import Mathlib
import cartan.II.section05.«0001_Definition_II_1_extra_1»
import cartan.II.section05.«0033_Definition_II_1_extra_20»

open scoped ComplexConjugate

-- Declarations for this item will be appended below by the statement pipeline.

namespace Path

-- Proof sketch: compose `f` with complex conjugation on the source and target; continuity of
-- complex conjugation on `ℂ` and continuity of `f` along the image of `γ` imply continuity on the
-- reflected path image.
/-- Exercise 1 (1): if `f` is continuous on the image of a path `γ`, then
`z ↦ conj (f (conj z))` is continuous on the reflected path `γ.map Complex.continuous_conj`. -/
theorem continuousOn_conj_comp_conj_reflected
    {a b : ℂ} {γ : Path a b} {f : ℂ → ℂ} (hf : ContinuousOn f (Set.range γ)) :
    ContinuousOn (fun z ↦ conj (f (conj z)))
      (Set.range (γ.map Complex.continuous_conj)) := sorry

-- Proof sketch: parametrize the reflected path by `t ↦ conj (γ t)`, use the piecewise
-- differentiability of `γ` to justify taking derivatives on each smooth piece, and observe that
-- the reflected integrand is the complex conjugate of the original integrand.
/-- Exercise 1 (2): for a piecewise differentiable path `γ`, reflecting the path across the real
axis and replacing `f` by `z ↦ conj (f (conj z))` conjugates the complex path integral. -/
theorem conj_curveIntegral_eq_curveIntegral_reflected
    {a b : ℂ} {γ : Path a b} (hγ : γ.IsPiecewiseDifferentiable) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Set.range γ)) :
    conj (∫ᶜ z in γ, (1 : ℂ →L[ℂ] ℂ).smulRight (f z)) =
      ∫ᶜ z in γ.map Complex.continuous_conj,
        (1 : ℂ →L[ℂ] ℂ).smulRight (conj (f (conj z))) := sorry

end Path

-- Proof sketch: identify the reflected positively oriented unit circle with the negatively
-- oriented original circle, use `conj z = z⁻¹` on `|z| = 1`, and rewrite the reflected integrand
-- in terms of `dz / z^2`.
/-- Exercise 1 (3): on the positively oriented unit circle, conjugating the circle integral of `f`
produces the integral of `-conj (f z) / z^2`. -/
theorem conj_circleIntegral_unitCircle_eq_neg_circleIntegral_conj_div_zsq
    {f : ℂ → ℂ} (hf : ContinuousOn f (Metric.sphere (0 : ℂ) 1)) :
    conj (∮ z in C(0, 1), f z) =
      -(∮ z in C(0, 1), conj (f z) / z ^ (2 : ℕ)) := sorry
