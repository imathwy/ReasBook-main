import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_4
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient

/- Remark 5.9 is `source-facing`: the textbook fixes the concrete quadratic
`x ↦ -(1 / 2) * ‖x‖²` on `ℝ^n`. Domain sampling points to the existing owners already used in this
chapter: Chapter 4's `quadratic_affine_function` for concrete quadratics on `Fin n → ℝ`, Chapter
5's `is_l_smooth_on` for global smoothness, mathlib's `ConcaveOn` for concavity, and the ambient
gradient `∇`. The primitive data is only the quadratic itself, so the file should reuse the
Chapter 4 quadratic owner rather than keep a parallel local quadratic API. The remaining
declarations are the source-facing derived views: gradient, least smoothness parameter, concavity,
tangent-plane inequality, and failure of `0`-smoothness. -/

section

variable (n : ℕ)

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "f" => fun x : E ↦ quadratic_affine_function (-1) 0 0 x

-- Proof sketch: differentiate `x ↦ ‖x‖²` using `hasStrictFDerivAt_norm_sq`, scale by `-(1 / 2)`,
-- and identify the resulting Fréchet derivative with the inner product against `-x`; the canonical
-- gradient is then obtained from `HasGradientAt.gradient`.
/-- The gradient of `x ↦ -(1 / 2) * ‖x‖²` is the linear vector field `x ↦ -x`. -/
theorem gradient_negative_half_squared_norm (x : E) :
    ∇ f x = -x := sorry

-- Proof sketch: compute `∇ f x = -x`, so the gradient difference is
-- `-(x - y)` and has norm `‖x - y‖`. This gives global `1`-smoothness. When `0 < n`, choose
-- distinct `x,y`; if `is_l_smooth_on f Set.univ L`, evaluating the gradient Lipschitz inequality
-- on those points gives `1 ≤ L`, so `1` is the least smoothness parameter.
/-- Remark 5.9 (1): on nontrivial Euclidean spaces `ℝ^n`, the quadratic
`x ↦ -(1 / 2) * ‖x‖²` has least global smoothness parameter `1`; equivalently, it is `1`-smooth
and it is not `L`-smooth for any `L < 1`. -/
theorem negative_half_squared_norm_isLeast_smoothness_parameter (hn : 0 < n) :
    IsLeast {L : NNReal | is_l_smooth_on f Set.univ L} 1 := sorry

-- Proof sketch: `x ↦ ‖x‖²` is convex on `Set.univ`, and multiplying by the nonpositive scalar
-- `-(1 / 2)` turns that convex quadratic into a concave function on the whole space.
/-- Remark 5.9 (2): the quadratic `x ↦ -(1 / 2) * ‖x‖²` is concave on `ℝ^n`. -/
theorem negative_half_squared_norm_concaveOn :
    ConcaveOn ℝ Set.univ f := sorry

-- Proof sketch: apply the first-order support inequality for concave differentiable functions to
-- `f`, using the concavity statement above and the gradient formula `∇ f x = -x`. This is exactly
-- Theorem 5.8(ii) specialized to `L = 0`.
/-- Remark 5.9 (3): for all `x, y ∈ ℝ^n`, the quadratic `x ↦ -(1 / 2) * ‖x‖²` satisfies the
first-order upper bound `f y ≤ f x + ⟪∇f(x), y - x⟫`, so the quadratic upper-model clause from
Theorem 5.8 holds with `L = 0`. -/
theorem negative_half_squared_norm_le_tangent_plane (x y : E) :
    f y ≤ f x + inner ℝ (∇ f x) (y - x) :=
    sorry

-- Proof sketch: if `f` were `0`-smooth, its gradient field would be `0`-Lipschitz and hence
-- constant on `Set.univ`. When `0 < n`, `gradient_negative_half_squared_norm` identifies the
-- gradient with `x ↦ -x`, whose values differ at distinct points.
/-- Remark 5.9 (4): on nontrivial Euclidean spaces `ℝ^n`, although the first-order upper-model
inequality holds with `L = 0`, the quadratic `x ↦ -(1 / 2) * ‖x‖²` is not globally `0`-smooth. -/
theorem negative_half_squared_norm_not_zero_smooth (hn : 0 < n) :
    ¬ is_l_smooth_on f Set.univ 0 := sorry

end
