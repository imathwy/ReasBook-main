import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_13_10 (from Chap13) -/
open Matrix

noncomputable section

section

variable {n l : ℕ}

local notation "E" => Fin n → ℝ

/- Definition 13.10 is `source-facing`: the item introduces a concrete quadratic program on
`ℝ^n` with feasible set the convex hull of finitely many points. The relevant `core/canonical`
owners already present in the project are:

- `quadratic_affine_function` from Definition 4.4 for the quadratic objective
  `x ↦ (1 / 2) xᵀ Q x + bᵀ x`;
- `constrained_problem_objective` from Definition 3.15 for the constrained optimization owner.

The primitive data for this owner are therefore only the matrix `Q`, the linear term `b`, and the
finite vertex family `a`. Positive-definiteness of `Q` is a later property used by downstream
algorithms and optimality statements, not part of the defining owner itself. The clean public API
is therefore a direct specialization of the constrained-problem owner, with separate source-facing
names for the feasible set `Ω`, the quadratic objective `f_q`, and the optimal value `f_opt`. The
only nontrivial bridge needed here is the canonical Chapter 9 lift `Function.toEReal`, which
replaces a raw lambda coercion in the constrained objective. -/

/- The objective and constrained-problem owners already exist upstream; Definition 13.10 only
specializes them to the finite-hull quadratic setting. -/
recall quadratic_affine_function
recall quadratic_affine_function_apply
recall constrained_problem_objective
recall constrained_problem_objective_of_mem
recall constrained_problem_objective_of_not_mem

/-- The feasible set `Ω = conv{a₁, …, a_l}` for the finite-hull quadratic problem. -/
def polytope_quadratic_feasible_set (a : Fin l → E) : Set E :=
  convexHull ℝ (Set.range a)

/-- The quadratic objective `f_q(x) = (1 / 2) xᵀ Q x + bᵀ x` attached to a matrix `Q` and linear
term `b`. -/
abbrev polytope_quadratic_objective
    (Q : Matrix (Fin n) (Fin n) ℝ) (b : E) : E → ℝ :=
  quadratic_affine_function Q b 0

-- Proof sketch: specialize `quadratic_affine_function_apply` at constant term `0`; the final
-- `+ 0` disappears by simplification.
/-- Evaluating `polytope_quadratic_objective Q b` at `x` gives the textbook formula
`(1 / 2) xᵀ Q x + bᵀ x`. -/
@[simp] theorem polytope_quadratic_objective_apply
    (Q : Matrix (Fin n) (Fin n) ℝ) (b x : E) :
    polytope_quadratic_objective Q b x =
      (1 / 2 : ℝ) * dotProduct x (Q *ᵥ x) + dotProduct b x := by
  simp [polytope_quadratic_objective]

/-- Definition 13.10: the quadratic program (13.32) on `ℝ^n`, with matrix `Q`, linear term `b`,
and feasible set `Ω = conv{a₁, a₂, …, a_l}`, is the constrained objective obtained by restricting
`x ↦ (1 / 2) xᵀ Q x + bᵀ x` to `Ω`. In the textbook setting, later results further assume
`Q ∈ 𝕊_{++}^n`. -/
abbrev polytope_quadratic_problem
    (Q : Matrix (Fin n) (Fin n) ℝ) (b : E) (a : Fin l → E) : E → EReal :=
  constrained_problem_objective
    (polytope_quadratic_objective Q b).toEReal
    (polytope_quadratic_feasible_set a)

-- Proof sketch: rewrite `polytope_quadratic_problem` as `constrained_problem_objective` on the
-- feasible set `polytope_quadratic_feasible_set a`, then apply
-- `constrained_problem_objective_of_mem`.
/-- On the feasible set `Ω`, the quadratic problem agrees with the quadratic objective `f_q`. -/
@[simp] theorem polytope_quadratic_problem_of_mem
    (Q : Matrix (Fin n) (Fin n) ℝ) (b : E) (a : Fin l → E) {x : E}
    (hx : x ∈ polytope_quadratic_feasible_set a) :
    polytope_quadratic_problem Q b a x = polytope_quadratic_objective Q b x := by
  simpa [polytope_quadratic_problem] using
    constrained_problem_objective_of_mem (polytope_quadratic_objective Q b).toEReal hx

-- Proof sketch: rewrite `polytope_quadratic_problem` as `constrained_problem_objective` on the
-- feasible set `polytope_quadratic_feasible_set a`, then apply
-- `constrained_problem_objective_of_not_mem`.
/-- Outside the feasible set `Ω`, the quadratic problem takes the infeasible value `⊤`. -/
@[simp] theorem polytope_quadratic_problem_of_not_mem
    (Q : Matrix (Fin n) (Fin n) ℝ) (b : E) (a : Fin l → E) {x : E}
    (hx : x ∉ polytope_quadratic_feasible_set a) :
    polytope_quadratic_problem Q b a x = ⊤ := by
  simpa [polytope_quadratic_problem] using
    constrained_problem_objective_of_not_mem (polytope_quadratic_objective Q b).toEReal hx

/-- The optimal value `f_opt` of the finite-hull quadratic problem is the infimum of the attained
values of its constrained objective. -/
def polytope_quadratic_optimal_value
    (Q : Matrix (Fin n) (Fin n) ℝ) (b : E) (a : Fin l → E) : EReal :=
  sInf (Set.range (polytope_quadratic_problem Q b a))

-- Proof sketch: unfold `polytope_quadratic_optimal_value`; the result is exactly its defining
-- `sInf` expression over the constrained objective values.
/-- Expanding `polytope_quadratic_optimal_value Q b a` gives the `sInf` of the values of the
quadratic problem (13.32). -/
theorem polytope_quadratic_optimal_value_eq_sInf
    (Q : Matrix (Fin n) (Fin n) ℝ) (b : E) (a : Fin l → E) :
    polytope_quadratic_optimal_value Q b a =
      sInf (Set.range (polytope_quadratic_problem Q b a)) :=
  rfl

end

/-! ### Example_13_10 (from Chap13) -/
noncomputable section

universe u

open InnerProductSpace (toDualMap)
open Metric
open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "B" => closedBall (0 : E) 1

/- Example 13.10 lies in the Chapter 13 conditional-gradient / Chapter 10 unit-ball linear
optimization domain.

Domain sampling of the owner declarations shows:
- Chapter 10's `Λ[·]` is the source-facing owner for unit-ball linear minimization/maximization;
- `primalCounterparts_toDualMap_eq_singleton_normalized` is the Chapter 10 canonical singleton
  description of `Λ[toDualMap ℝ E a]` away from the zero case;
- `generalized_conditional_gradient_argmin` is the Chapter 13 owner for the linearized oracle;
- `S[·, ·](·)` is the canonical owner for the conditional-gradient gap value.

This file is therefore `bridge/view`: the only extra source-facing datum is the explicit oracle
point `-‖∇ f(x)‖⁻¹ ∇ f(x)`. The feasible set remains the canonical closed unit ball `B`, and the
example is organized by proving that this explicit point belongs to the existing Chapter 10 and
Chapter 13 owners rather than by introducing a parallel local direction definition. -/

-- Proof sketch: unfold `Λ[toDualMap ℝ E (-∇ f x)]`. The normalized negative gradient has norm `1`
-- when `∇ f x ≠ 0` and norm `0` when `∇ f x = 0`, so it is feasible for the unit ball. Its
-- pairing with `toDualMap ℝ E (-∇ f x)` is `‖∇ f x‖`, which is exactly the norm of that
-- functional because `toDualMap` is a linear isometry.
/-- The normalized negative gradient is a Chapter 10 primal counterpart of the functional
`toDualMap ℝ E (-∇ f(x))`, i.e. it is the canonical unit-ball linear-minimization point for the
negative gradient functional. -/
theorem neg_normalized_gradient_mem_primalCounterparts
    (f : E → ℝ) (x : E) :
    -((‖∇ f x‖)⁻¹ • ∇ f x) ∈ Λ[toDualMap ℝ E (-∇ f x)] := by
  by_cases hgrad : ∇ f x = 0
  · -- In the zero-gradient case, the Chapter 10 owner collapses to the unit ball itself.
    rw [primalCounterparts_eq_closedBall_of_eq_zero]
    · simp [hgrad]
    · simp [hgrad]
  · -- Away from `0`, the Chapter 10 singleton description identifies the explicit oracle point.
    have hneg_grad : -∇ f x ≠ 0 := by
      simpa using hgrad
    rw [primalCounterparts_toDualMap_eq_singleton_normalized hneg_grad]
    simp [Set.mem_singleton_iff, norm_neg]

-- Proof sketch: unfold both owners. For `g = extendedIndicator B`, the Chapter 13 argmin
-- condition is precisely minimization of `q ↦ ⟪q, ∇ f(x)⟫` over `B`; rewriting by negation turns
-- this into maximization of `q ↦ ⟪-∇ f(x), q⟫`, which is exactly the Chapter 10 owner
-- characterization `mem_Λ_iff` for `toDualMap ℝ E (-∇ f(x))`.
/-- For the unit-ball constrained problem, the Chapter 13 conditional-gradient oracle set is
exactly the Chapter 10 unit-ball primal-counterpart set for the negative gradient functional. -/
theorem mem_unit_ball_generalized_conditional_gradient_argmin_iff_mem_primalCounterparts
    {f : E → ℝ} {x p : E} :
    p ∈ generalized_conditional_gradient_argmin f (extendedIndicator B) x ↔
      p ∈ Λ[toDualMap ℝ E (-∇ f x)] := by
  have hargmin :
      p ∈ generalized_conditional_gradient_argmin f (extendedIndicator B) x ↔
        p ∈ B ∧ IsMinOn (fun q ↦ inner ℝ q (∇ f x)) B p := by
    -- Convert the Chapter 13 constrained argmin owner into feasibility plus linear minimization.
    have hB_nonempty : Set.Nonempty B := by
      refine ⟨0, ?_⟩
      simp
    have hbridge :=
      mem_generalized_conditional_gradient_argmin_extendedIndicator_iff
        (f := fun y ↦ ((f y : ℝ) : EReal)) (C := B) (xk := x) (p := p) hB_nonempty
    simpa using hbridge
  calc
    p ∈ generalized_conditional_gradient_argmin f (extendedIndicator B) x ↔
        p ∈ B ∧ IsMinOn (fun q ↦ inner ℝ q (∇ f x)) B p := hargmin
    _ ↔ p ∈ Λ[toDualMap ℝ E (-∇ f x)] := by
      rw [mem_Λ_iff]
      constructor
      · rintro ⟨hpB, hpmin⟩
        refine ⟨hpB, ?_⟩
        -- Minimizing `q ↦ ⟪q, ∇f(x)⟫` is equivalent to maximizing the negated functional.
        rw [isMinOn_iff] at hpmin
        rw [isMaxOn_iff]
        intro q hq
        have hq_le : inner ℝ p (∇ f x) ≤ inner ℝ q (∇ f x) :=
          hpmin q hq
        have hneg_le : -inner ℝ q (∇ f x) ≤ -inner ℝ p (∇ f x) :=
          neg_le_neg hq_le
        simpa [InnerProductSpace.toDualMap_apply_apply, real_inner_comm] using hneg_le
      · rintro ⟨hpB, hpmax⟩
        refine ⟨hpB, ?_⟩
        -- Conversely, maximizing the negated linear form is minimizing the original one.
        rw [isMaxOn_iff] at hpmax
        rw [isMinOn_iff]
        intro q hq
        have hq_le :
            (toDualMap ℝ E (-∇ f x)) q ≤ (toDualMap ℝ E (-∇ f x)) p :=
          hpmax q hq
        have hneg_le :
            -((toDualMap ℝ E (-∇ f x)) p) ≤ -((toDualMap ℝ E (-∇ f x)) q) :=
          neg_le_neg hq_le
        simpa [InnerProductSpace.toDualMap_apply_apply, real_inner_comm] using hneg_le

-- Proof sketch: combine the previous Chapter 10 membership theorem with the bridge theorem
-- identifying the Chapter 13 unit-ball argmin owner with `Λ[toDualMap ℝ E (-∇ f x)]`.
/-- The normalized negative gradient is a valid Chapter 13 conditional-gradient oracle choice for
the unit-ball constrained problem. -/
theorem neg_normalized_gradient_mem_unit_ball_generalized_conditional_gradient_argmin
    (f : E → ℝ) (x : E) :
    -((‖∇ f x‖)⁻¹ • ∇ f x) ∈ generalized_conditional_gradient_argmin
      f (extendedIndicator B) x := by
  rw [mem_unit_ball_generalized_conditional_gradient_argmin_iff_mem_primalCounterparts]
  exact neg_normalized_gradient_mem_primalCounterparts f x

/-- Helper for Example 13.10: pairing the gradient with its normalized direction yields its norm.
-/
lemma inner_gradient_normalized_eq_norm
    {f : E → ℝ} {x : E} :
    inner ℝ (∇ f x) ((‖∇ f x‖)⁻¹ • ∇ f x) = ‖∇ f x‖ := by
  -- Route correction: prove the norm term through the Chapter 10 owner equality, not by a fresh
  -- zero/nonzero split inside the main gap computation.
  have hp :
      -((‖∇ f x‖)⁻¹ • ∇ f x) ∈ Λ[toDualMap ℝ E (-∇ f x)] :=
    neg_normalized_gradient_mem_primalCounterparts f x
  calc
    inner ℝ (∇ f x) ((‖∇ f x‖)⁻¹ • ∇ f x) =
      (toDualMap ℝ E (-∇ f x)) (-((‖∇ f x‖)⁻¹ • ∇ f x)) := by
        simp [InnerProductSpace.toDualMap_apply_apply]
    _ = ‖toDualMap ℝ E (-∇ f x)‖ := by
        exact apply_eq_norm_of_mem_primalCounterparts hp
    _ = ‖∇ f x‖ := by
        simpa using (toDualMap ℝ E).norm_map (-∇ f x)

-- Proof sketch: the preceding argmin theorem lets us invoke
-- `generalized_conditional_gradient_norm_eq_of_mem_argmin`. Evaluating the gap objective at the
-- normalized negative gradient and simplifying the indicator terms with `hx` and the preceding
-- primal-counterpart membership theorem yields `⟪∇ f(x), x⟫ + ‖∇ f(x)‖`.
/-- Example 13.10 (1): for the unit-ball constrained problem, the canonical conditional-gradient
gap `S[f, δ_B](x)` is `⟪∇ f(x), x⟫ + ‖∇ f(x)‖`. Equivalently, the normalized negative gradient is
the corresponding oracle choice realizing this gap. -/
theorem unit_ball_generalized_conditional_gradient_norm_eq_inner_gradient_add_norm
    (f : E → ℝ) {x : E} (hx : x ∈ B) :
    S[f, extendedIndicator B](x) =
      ((inner ℝ (∇ f x) x + ‖∇ f x‖ : ℝ) : EReal) := by
  let p : E := -((‖∇ f x‖)⁻¹ • ∇ f x)
  have hp_argmin : p ∈ generalized_conditional_gradient_argmin f (extendedIndicator B) x := by
    simpa [p] using neg_normalized_gradient_mem_unit_ball_generalized_conditional_gradient_argmin f x
  have hp_primal : p ∈ Λ[toDualMap ℝ E (-∇ f x)] := by
    simpa [p] using neg_normalized_gradient_mem_primalCounterparts f x
  have hpB : p ∈ B :=
    (mem_Λ_iff.mp hp_primal).1
  have hgap :
      inner ℝ (∇ f x) (x - p) = inner ℝ (∇ f x) x + ‖∇ f x‖ := by
    -- Expand the oracle point and isolate the normalized-gradient pairing.
    calc
      inner ℝ (∇ f x) (x - p) =
          inner ℝ (∇ f x) (x + ((‖∇ f x‖)⁻¹ • ∇ f x)) := by
            simp [p, sub_eq_add_neg]
      _ = inner ℝ (∇ f x) x + inner ℝ (∇ f x) ((‖∇ f x‖)⁻¹ • ∇ f x) := by
            rw [inner_add_right]
      _ = inner ℝ (∇ f x) x + ‖∇ f x‖ := by
            rw [inner_gradient_normalized_eq_norm]
  -- Evaluate the Chapter 13 gap at the explicit oracle point and cancel the indicator terms.
  calc
    S[f, extendedIndicator B](x) =
        generalized_conditional_gradient_gap_objective f (extendedIndicator B) x p := by
          exact generalized_conditional_gradient_norm_eq_of_mem_argmin hp_argmin
    _ = ((inner ℝ (∇ f x) (x - p) : ℝ) : EReal) + extendedIndicator B x - extendedIndicator B p := by
          rw [generalized_conditional_gradient_gap_objective_apply]
    _ = ((inner ℝ (∇ f x) (x - p) : ℝ) : EReal) := by
          simp [extendedIndicator, hx, hpB]
    _ = ((inner ℝ (∇ f x) x + ‖∇ f x‖ : ℝ) : EReal) := by
          rw [hgap]

-- Proof sketch: substitute the explicit oracle point
-- `-((‖∇ f(xᵏ)‖)⁻¹ • ∇ f(xᵏ))` into the affine update `xᵏ + t (pᵏ - xᵏ)` and expand. The
-- resulting identity is purely algebraic, so it holds for every real `t`; the algorithmic
-- stepsize constraint `t ∈ [0,1]` is only a later specialization.
/-- Example 13.10 (2): the conditional-gradient update along the unit-ball oracle point
`-((‖∇ f(xᵏ)‖)⁻¹ • ∇ f(xᵏ))` rewrites for any real stepsize `t` as
`xᵏ + t • (pᵏ - xᵏ) = (1 - t) • xᵏ - t • ((‖∇ f(xᵏ)‖)⁻¹ • ∇ f(xᵏ))`. In particular, this applies
to the algorithmic case `t ∈ [0,1]`. -/
theorem unit_ball_generalized_conditional_gradient_update_eq
    (f : E → ℝ) (xk : E) (t : ℝ) :
    xk + t • (-((‖∇ f xk‖)⁻¹ • ∇ f xk) - xk) =
      (1 - t) • xk - t • ((‖∇ f xk‖)⁻¹ • ∇ f xk) := by
  let a : E := (‖∇ f xk‖)⁻¹ • ∇ f xk
  -- Expand the affine update and collect the `xk` terms into `(1 - t) • xk`.
  calc
    xk + t • (-((‖∇ f xk‖)⁻¹ • ∇ f xk) - xk) = xk + (-(t • a) - t • xk) := by
          simp [a, smul_sub]
    _ = (xk - t • xk) - t • a := by
          simp [sub_eq_add_neg, add_assoc, add_comm]
    _ = (1 - t) • xk - t • a := by
          rw [sub_smul, one_smul]
    _ = (1 - t) • xk - t • ((‖∇ f xk‖)⁻¹ • ∇ f xk) := by
          rfl

end
