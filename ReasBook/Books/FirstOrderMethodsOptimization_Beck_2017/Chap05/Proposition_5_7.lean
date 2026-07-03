import FirstOrderMethodsOptimization_Beck_2017.Chap05.Theorem_5_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/-
Proposition 5.7 is `source-facing`: it records the textbook smoothness estimate for the radial
function `x ↦ √(1 + ‖x‖²)`. Domain sampling in the Chapter 5/10 neighborhood points to
`is_l_smooth_on` as the owner abstraction for the conclusion, while the ambient real
inner-product-space geometry in this project is organized around the canonical `[ProperSpace E]`
owner rather than an explicit finite-dimensionality hypothesis or a coordinate model of `ℝ^n`.
The only primitive local datum is the radial function itself; the smoothness statement is derived
API on that owner.
-/

-- Proof sketch: `φ` is `C²` because it is the square root of the everywhere-positive smooth
-- function `x ↦ 1 + ‖x‖²`. Apply the owner-level Hessian criterion from Theorem 5.12. The
-- remaining pointwise estimate is the explicit Hessian computation
-- `D²φ(x) = (1 + ‖x‖²)^(-1/2) I - (1 + ‖x‖²)^(-3/2) (x ⊗ x)`, whose operator norm is at most `1`.
/-- Proposition 5.7: on any proper real inner-product space, hence in particular on every
finite-dimensional Euclidean space `ℝ^n`, the function `x ↦ √(1 + ‖x‖²)` is globally `1`-smooth
with respect to the Euclidean norm. -/
theorem sqrt_one_add_sq_norm_is_l_smooth :
    is_l_smooth_on (fun x : E ↦ Real.sqrt (1 + ‖x‖ ^ (2 : ℕ))) Set.univ 1 := by
  sorry

end
