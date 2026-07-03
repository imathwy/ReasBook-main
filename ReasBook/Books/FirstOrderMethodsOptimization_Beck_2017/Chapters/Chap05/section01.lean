import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_1 (from Chap05) -/
noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Definition 5.1 is `source-facing`: it introduces the chapter smoothness-on-a-set predicate.
Domain sampling shows that the `core/canonical` owners are mathlib's `DifferentiableAt`,
`LipschitzOnWith`, and `fderiv`. The gradient formulation is an inner-product `bridge/view`,
derived from this owner abstraction rather than stored as primitive data. -/

/-- Definition 5.1: a real-valued function is `L`-smooth on `D` when it is differentiable at every
point of `D` and its Fréchet derivative is `L`-Lipschitz on `D`. -/
def is_l_smooth_on (f : E → ℝ) (D : Set E) (L : NNReal) : Prop :=
  (∀ x ∈ D, DifferentiableAt ℝ f x) ∧ LipschitzOnWith L (fderiv ℝ f) D

-- Proof sketch: unfold `is_l_smooth_on`, then rewrite `LipschitzOnWith` using
-- `lipschitzOnWith_iff_norm_sub_le`; the metric on continuous linear maps is induced by the
-- operator norm, so the Lipschitz condition becomes the displayed derivative estimate.
/-- An `L`-smooth function on `D` is equivalently differentiable at every point of `D` and
satisfies the textbook estimate `‖f'(x) - f'(y)‖ ≤ L ‖x - y‖` for all `x, y ∈ D`. -/
theorem is_l_smooth_on_iff {f : E → ℝ} {D : Set E} {L : NNReal} :
    is_l_smooth_on f D L ↔
      (∀ x ∈ D, DifferentiableAt ℝ f x) ∧
        ∀ x ∈ D, ∀ y ∈ D, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ (L : ℝ) * ‖x - y‖ := by
  rw [is_l_smooth_on, lipschitzOnWith_iff_norm_sub_le]

end

section

open scoped Gradient

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Proof sketch: combine `is_l_smooth_on_iff` with `DifferentiableAt.hasGradientAt`, which
-- identifies `fderiv ℝ f x` with `toDual ℝ E (∇ f x)` at differentiability points. Since
-- `gradient f = (toDual ℝ E).symm ∘ fderiv ℝ f` and `toDual ℝ E` is a linear isometry
-- equivalence, Lipschitz control of `fderiv ℝ f` on `D` is equivalent to Lipschitz control of the
-- canonical gradient field on `D`.
/-- In a real Hilbert space, `is_l_smooth_on` is equivalently differentiability on `D` together
with `L`-Lipschitz control of the canonical gradient field on `D`. -/
theorem is_l_smooth_on_iff_lipschitzOnWith_gradient {f : E → ℝ} {D : Set E} {L : NNReal} :
    is_l_smooth_on f D L ↔
      (∀ x ∈ D, DifferentiableAt ℝ f x) ∧ LipschitzOnWith L (∇ f) D := by
  rw [is_l_smooth_on]
  constructor
  · rintro ⟨hdiff, hderiv⟩
    refine ⟨hdiff, ?_⟩
    rw [lipschitzOnWith_iff_norm_sub_le] at hderiv ⊢
    intro x hx y hy
    have hx' := hdiff x hx
    have hy' := hdiff y hy
    have hxy : ‖InnerProductSpace.toDual ℝ E (∇ f x - ∇ f y)‖ ≤ (L : ℝ) * ‖x - y‖ := by
      simpa [hx'.hasGradientAt.hasFDerivAt.fderiv, hy'.hasGradientAt.hasFDerivAt.fderiv, map_sub]
        using hderiv hx hy
    rwa [(InnerProductSpace.toDual ℝ E).norm_map] at hxy
  · rintro ⟨hdiff, hgrad⟩
    refine ⟨hdiff, ?_⟩
    rw [lipschitzOnWith_iff_norm_sub_le] at hgrad ⊢
    intro x hx y hy
    have hx' := hdiff x hx
    have hy' := hdiff y hy
    have hxy : ‖InnerProductSpace.toDual ℝ E (∇ f x - ∇ f y)‖ ≤ (L : ℝ) * ‖x - y‖ := by
      rw [(InnerProductSpace.toDual ℝ E).norm_map]
      exact hgrad hx hy
    simpa [hx'.hasGradientAt.hasFDerivAt.fderiv, hy'.hasGradientAt.hasFDerivAt.fderiv, map_sub]
      using hxy

-- Proof sketch: combine `is_l_smooth_on_iff_lipschitzOnWith_gradient` with
-- `lipschitzOnWith_iff_norm_sub_le` in the normed target space `E`.
/-- In a real Hilbert space, `is_l_smooth_on` is equivalently differentiability on `D` together
with the textbook Lipschitz estimate for the gradient field. -/
theorem is_l_smooth_on_iff_forall_norm_sub_le {f : E → ℝ} {D : Set E} {L : NNReal} :
    is_l_smooth_on f D L ↔
      (∀ x ∈ D, DifferentiableAt ℝ f x) ∧
        ∀ x ∈ D, ∀ y ∈ D,
          ‖∇ f x - ∇ f y‖ ≤ (L : ℝ) * ‖x - y‖ := by
  rw [is_l_smooth_on_iff_lipschitzOnWith_gradient, lipschitzOnWith_iff_norm_sub_le]

end

/-! ### Proposition_5_1 (from Chap05) -/
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
