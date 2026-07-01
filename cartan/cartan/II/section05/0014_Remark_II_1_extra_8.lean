import Mathlib
import cartan.II.section05.«0001_Definition_II_1_extra_1»
import cartan.II.section05.«0012_Definition_II_1_extra_7»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped unitInterval

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {a b : E} {γ : Path a b} {ω : E → E →L[ℝ] F}
variable {D D₁ D₂ : Set E} {f g : C(I, F)}

-- Proof sketch: choose a subdivision witnessing piecewise differentiability of `γ`, apply the
-- one-variable fundamental theorem on each subinterval using the local primitive supplied by
-- `hf`, and sum the resulting endpoint differences to obtain a telescoping series.
/-- Remark II.1-extra-8: if `γ` is piecewise differentiable and `f` is a primitive of `ω` along
`γ`, then the curve integral of `ω` along `γ` is the endpoint difference `f 1 - f 0`. -/
theorem IsPrimitiveAlongPath.curveIntegral_eq_endpoint_sub
    [CompleteSpace F] (hf : IsPrimitiveAlongPath ω D γ f)
    (hγ_piecewise : γ.IsPiecewiseDifferentiable) :
    ∫ᶜ z in γ, ω z = f 1 - f 0 := sorry

-- Proof sketch: compare the endpoint differences attached to `f` and `g` on a common local cover
-- of `I`; on overlaps their difference is locally constant, hence constant on the connected unit
-- interval, so the endpoint jumps agree.
/-- The endpoint difference attached to a primitive along a continuous path is independent of the
chosen primitive. -/
theorem IsPrimitiveAlongPath.endpoint_sub_eq
    (hf : IsPrimitiveAlongPath ω D₁ γ f)
    (hg : IsPrimitiveAlongPath ω D₂ γ g) :
    f 1 - f 0 = g 1 - g 0 := sorry
