import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0009_Definition_II_1_extra_6»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped unitInterval

namespace Path

-- Proof sketch: let `F : γ₀.Homotopy γ₁` be a homotopy whose image lies in `D`. Apply
-- `primitive_following_on_rectangle_exists_and_unique_up_to_constant` to the square map
-- `(s, t) ↦ F (t, s)` using the local primitives supplied by `hω`. The resulting primitive on the
-- square is constant on the vertical sides because the endpoints are fixed, so the endpoint
-- difference formula along the two horizontal sides gives equal integrals for `γ₀` and `γ₁`.
/-- Theorem 2: if two paths with the same endpoints are joined by a homotopy whose image stays in
`D`, then every closed form on `D` has the same integral along both piecewise differentiable
paths. -/
theorem curveIntegral_eq_of_homotopy_in_domain
    {D : Set ℂ} {ω : ℂ → ℂ →L[ℝ] ℂ}
    (hω : IsClosedOn ω D)
    {z₀ z₁ : ℂ} {γ₀ γ₁ : Path z₀ z₁}
    (hγ₀_piecewise : γ₀.IsPiecewiseDifferentiable)
    (hγ₁_piecewise : γ₁.IsPiecewiseDifferentiable)
    (F : γ₀.Homotopy γ₁) (hF : Set.range F ⊆ D) :
    ∫ᶜ z in γ₀, ω z = ∫ᶜ z in γ₁, ω z := sorry

end Path
