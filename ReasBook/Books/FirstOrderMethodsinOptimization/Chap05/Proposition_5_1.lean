import FirstOrderMethodsinOptimization.Chap04.Definition_4_4
import FirstOrderMethodsinOptimization.Chap05.Definition_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open WithLp (ofLp)

noncomputable section

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "E" => ι → ℝ

/- Proposition 5.1 is `source-facing`: it studies the quadratic-affine function from
Chapter 4 under the Chapter 5 owner predicate `is_l_smooth_on`, after transporting a finite real
product `ι → ℝ`, and hence `ℝ^n` when `ι = Fin n`, to the canonical `WithLp p` model. Domain
sampling points to the owner abstractions `quadratic_affine_function`, `is_l_smooth_on`, and the
operator norm of `(A.toLpLin p q).toContinuousLinearMap`, which is the canonical Lean rendering of
the textbook induced `(p,q)` matrix norm. -/

/-- The quadratic-affine function `x ↦ (1 / 2) xᵀ A x + bᵀ x + c`, viewed on the canonical
`WithLp p` model of a finite real product, specializing to `ℝ^n` for `ι = Fin n`. -/
def quadratic_affine_function_on_lp (p : ENNReal) (A : Matrix ι ι ℝ) (b : E)
    (c : ℝ) : WithLp p E → ℝ :=
  quadratic_affine_function A b c ∘ ofLp

-- Proof sketch: `quadratic_affine_function_on_lp p A b c` is the Chapter 4 owner quadratic
-- precomposed with `WithLp.ofLp`, so evaluation at `x` unfolds directly to the coordinate formula
-- applied to `ofLp x`.
/-- Evaluating `quadratic_affine_function_on_lp p A b c` at `x` applies the Chapter 4
quadratic-affine function to the underlying coordinate vector `ofLp x`. -/
@[simp] theorem quadratic_affine_function_on_lp_apply (p : ENNReal)
    (A : Matrix ι ι ℝ) (b : E) (c : ℝ) (x : WithLp p E) :
    quadratic_affine_function_on_lp p A b c x = quadratic_affine_function A b c (ofLp x) := sorry

-- Proof sketch: differentiate `quadratic_affine_function_on_lp p A b c` on the `WithLp` model;
-- the symmetry hypothesis identifies the derivative difference with the operator `A.toLpLin p q`,
-- which yields `is_l_smooth_on` with parameter `‖(A.toLpLin p q).toContinuousLinearMap‖₊`.
-- For optimality, use the unit-ball maximizer for the induced operator norm to show that any
-- smoothness constant must dominate this operator norm.
/-- Proposition 5.1: for the quadratic function `x ↦ (1 / 2) xᵀ A x + bᵀ x + c` on `ℝ^n`,
viewed with the `ℓ_p` norm on a finite real product `ι → ℝ`, and hence on `ℝ^n` when
`ι = Fin n`, the smallest global smoothness parameter is the canonical operator norm of
`(A.toLpLin p q).toContinuousLinearMap`, i.e. the textbook induced matrix norm `‖A‖_{p,q}`, when
`q` is Hölder-conjugate to `p`. -/
theorem quadratic_affine_function_on_lp_opNorm_isLeast_smoothness_parameter
    (p q : ENNReal) [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hpq : ENNReal.HolderConjugate p q)
    (A : Matrix ι ι ℝ) (hA : A.IsSymm) (b : E) (c : ℝ) :
    IsLeast
      {L : NNReal | is_l_smooth_on (quadratic_affine_function_on_lp p A b c) Set.univ L}
      ‖(A.toLpLin p q).toContinuousLinearMap‖₊ := sorry

end
