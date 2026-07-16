import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Example_2_5
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open InnerProductSpace

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Proposition 4.5 is `source-facing`. Its owner abstractions already exist upstream:
`extendedIndicator` in Chapter 2, `conjugate_function` in Definition 4.1, and the distance-based
potential in Example 2.5 as `euclidean_distance_potential`. This file therefore keeps only the
Fenchel-conjugacy identity specialized to that canonical project data, viewing the real-valued
distance potential as `EReal`-valued for conjugacy. -/

-- Proof sketch: rewrite `euclidean_distance_potential C` as the supremum over `c ∈ C` of the
-- affine functions `x ↦ ⟪x, c⟫ - 1/2 ‖c‖²`, identify the Euclidean pairing with the dual pairing
-- through `toDualMap`, and then compute the conjugate by splitting into the cases `y ∈ C` and
-- `y ∉ C`.
/-- Proposition 4.5: for a nonempty closed convex set `C` in a Euclidean space, the conjugate of
`x ↦ 1/2 ‖x‖² - 1/2 d(x, C)²`, expressed through the Chapter 2 owner
`euclidean_distance_potential`, is `y ↦ 1/2 ‖y‖² + δ_C(y)`. -/
theorem conjugate_function_quadratic_distance_eq_half_squared_norm_add_extendedIndicator
    (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    (fun y ↦ conjugate_function (fun x ↦ (euclidean_distance_potential C x : EReal))
      ↑(toDualMap ℝ E y)) =
      fun y ↦ (((1 / 2 : ℝ) * ‖y‖ ^ 2 : ℝ) : EReal) + extendedIndicator C y := sorry

end
