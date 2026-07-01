import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- Theorem 1: if `f` is holomorphic at every point of `D ⊆ ℂ`, then the differential form
`f(z) dz` is closed on `D`, i.e. `f` is conservative on `D` in the rectangle-integral sense. -/
-- Proof sketch: pointwise complex differentiability on `D` gives `DifferentiableOn ℂ f D`;
-- then apply the canonical owner theorem `DifferentiableOn.isConservativeOn`.
theorem holomorphic_isConservativeOn
    {D : Set ℂ} {f : ℂ → ℂ} (hf : ∀ z ∈ D, DifferentiableAt ℂ f z) :
    Complex.IsConservativeOn f D :=
  (show DifferentiableOn ℂ f D from fun z hz ↦ (hf z hz).differentiableWithinAt).isConservativeOn
