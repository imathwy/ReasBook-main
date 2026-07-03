import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0009_Definition_II_1_extra_6»
import DifferentialForms_Cartan_1970.II.section05.«0017_Definition_II_1_extra_10»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped unitInterval

namespace Path

-- Proof sketch: apply Lemma II.1-extra-12 to the homotopy square `δ` supplied by the closed-path
-- homotopy, obtaining a primitive of `ω` along that square; comparing the primitive on the two
-- horizontal edges identifies the contour integrals along `γ₀` and `γ₁`.
/-- Theorem 2': if two piecewise differentiable closed paths in `D` are homotopic through closed
paths contained in `D`, then every closed complex differential form on `D` has the same contour
integral along both paths. -/
theorem curveIntegral_eq_of_homotopic_closed_paths_of_closed_form
    {D : Set ℂ} {z₀ z₁ : ℂ} {γ₀ : Path z₀ z₀} {γ₁ : Path z₁ z₁}
    (hγ : ClosedPathHomotopicIn D γ₀ γ₁)
    (hγ₀_piecewise : γ₀.IsPiecewiseDifferentiable)
    (hγ₁_piecewise : γ₁.IsPiecewiseDifferentiable)
    {ω : ℂ → ℂ →L[ℝ] ℂ}
    (hω : IsClosedOn ω D) :
    ∫ᶜ z in γ₀, ω z = ∫ᶜ z in γ₁, ω z := sorry

end Path
