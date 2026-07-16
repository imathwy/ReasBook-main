import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Definition_2_9
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Definition_2_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix

section

variable {ι κ : Type*} [Fintype κ]

/-- The affine feasible set cut out by the linear equations `B x = b`, viewed as the fiber of the
matrix linear map over `b`. -/
def affine_linear_constraint_set (B : Matrix ι κ ℝ) (b : ι → ℝ) : Set (κ → ℝ) :=
  B.mulVecLin ⁻¹' {b}

/-- The homogeneous constraint set `ker B = {x | B x = 0}`, realized as the kernel of the matrix
linear map. -/
def homogeneous_linear_constraint_set (B : Matrix ι κ ℝ) : Set (κ → ℝ) :=
  LinearMap.ker B.mulVecLin

-- Proof sketch: every feasible point of `affine_linear_constraint_set B b` can be written as
-- `z + x₀` with `z ∈ homogeneous_linear_constraint_set B`, and conversely every such translate is
-- feasible because `x₀ ∈ affine_linear_constraint_set B b`. Rewriting the supremum in the
-- definition of `support_function`
-- along this translation gives the stated affine shift formula.
/-- Translating the homogeneous solution set by a particular solution `x₀` adds the evaluation
`y ↦ y x₀` to the support function. -/
theorem support_function_affine_linear_constraint_set_eq_eval_add_support_function_homogeneous
    (B : Matrix ι κ ℝ) (b : ι → ℝ) (x₀ : κ → ℝ)
    (hx₀ : x₀ ∈ affine_linear_constraint_set B b) :
    support_function (affine_linear_constraint_set B b) =
      fun y ↦ (y x₀ : EReal) + support_function (homogeneous_linear_constraint_set B) y := sorry

end

section

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

local instance instDecidableEqκ : DecidableEq κ := Classical.decEq κ

/-- The dual-space realization of `Range(Bᵀ)` under the canonical dot-product equivalence
`ℝⁿ ≃ (ℝⁿ)*`, obtained from the range of the transpose matrix linear map. -/
def transpose_range_dual (B : Matrix ι κ ℝ) : Set (Module.Dual ℝ (κ → ℝ)) :=
  dotProductEquiv ℝ κ '' (LinearMap.range Bᵀ.mulVecLin : Set (κ → ℝ))

-- Proof sketch: identify a dual vector with its representing vector via
-- `dotProductEquiv ℝ κ`.
-- Then the textbook argument shows that a functional is nonpositive on every `x` with `B x = 0`
-- exactly when it is represented by some vector in `Range(Bᵀ)`.
/-- The polar cone of the homogeneous solution set `ker B` is the dual-space image of
`Range(Bᵀ)`. -/
theorem polar_cone_homogeneous_linear_constraint_set_eq_transpose_range_dual
    (B : Matrix ι κ ℝ) :
    polar_cone (homogeneous_linear_constraint_set B) = transpose_range_dual B := sorry

-- Proof sketch: translate the feasible set by a chosen solution `x₀ ∈ affine_linear_constraint_set
-- B b`, so every `x` with `B x = b` becomes `z + x₀` with `B z = 0`; this is the preceding
-- translation formula. Then identify
-- `σ_{ker B}` with the indicator of the polar cone of `ker B`, and rewrite that polar cone using
-- `polar_cone_homogeneous_linear_constraint_set_eq_transpose_range_dual`.
/-- Example 2.8: if `x₀` satisfies `B x₀ = b`, then the support function of
`C = {x | B x = b}` is the affine functional `y ↦ y x₀` plus the indicator of the dual-space
realization of `Range(Bᵀ)`. -/
theorem support_function_affine_linear_constraint_set_eq_eval_add_indicator_transpose_range_dual
    (B : Matrix ι κ ℝ) (b : ι → ℝ) (x₀ : κ → ℝ)
    (hx₀ : x₀ ∈ affine_linear_constraint_set B b) :
    support_function (affine_linear_constraint_set B b) =
      fun y ↦ (y x₀ : EReal) + extendedIndicator (transpose_range_dual B) y := sorry

end
