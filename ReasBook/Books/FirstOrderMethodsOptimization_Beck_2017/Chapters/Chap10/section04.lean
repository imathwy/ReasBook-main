import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_4_1 (from Chap10) -/
universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (f : E → ℝ) (Lf : NNReal)

/- Definition 10.4.1 is a recall-only `source-facing` item in the smooth whole-space
minimization domain: it introduces no new owner abstraction beyond the Chapter 8 unconstrained
minimization owner and the Chapter 5 smoothness owner.

Domain sampling:
- `unconstrained_problem_solutions` is the source-facing owner for minimizing `f` on the ambient
  space `E`;
- `mem_unconstrained_problem_solutions_iff` is the companion characterization by `IsMinOn f
  Set.univ x`;
- `is_l_smooth_on` is the Chapter 5 owner for the `L_f`-smoothness clause;
- `is_l_smooth_on_iff` is the derivative-Lipschitz companion API for that smoothness owner.

The primitive data are only the objective `f : E → ℝ` and the smoothness parameter `L_f`. The
source-facing whole-space problem and smoothness clause are therefore the canonical specializations
`unconstrained_problem_solutions f` and `is_l_smooth_on f Set.univ Lf`, derived directly from the
existing owners rather than from a parallel local wrapper. -/

set_option linter.hashCommand false

/- Definition 10.4.1: the unconstrained minimization problem
`min {f(x) | x ∈ E}` is the Chapter 8 owner specialized to `f`. -/
#check unconstrained_problem_solutions f

/- Definition 10.4.1: the standing smoothness assumption is the Chapter 5 owner `is_l_smooth_on`,
specialized to the whole space `Set.univ`. -/
#check is_l_smooth_on f Set.univ Lf

end

/-! ### Definition_10_4_2 (from Chap10) -/
noncomputable section

universe u

section

variable {E : Type u}

/- Definition 10.4.2 is `source-facing`, but its owner abstractions already live upstream:

- `IsConstrainedConvexProblem` from Chapter 8 owns the constrained problem data
  `min {f x : x ∈ C}`;
- `is_l_smooth_on` from Chapter 5 owns the smoothness clause on `f.toReal`;
- `IsCompositeSmoothMinimizationProblem` from Definition 10.3 is the Chapter 10 canonical owner
  after specializing the nonsmooth term to `extendedIndicator C`.

The public surface here should therefore be a bridge between those owners, not a parallel wrapper
class. In this bridge layer the primitive data are only `f`, `C`, and the domain/nonemptiness
side conditions needed to compare the upstream solution-set owners; no normed-space structure is
mathematically active. Because `IsMinOn f C x` does not itself encode feasibility, the faithful
minimizer comparison is at the Chapter 8 solution-set level. -/

/-- If `C` contains a feasible point in the effective domain of `f`, then the ambient minimizers
of the constrained objective are exactly the constrained minimizers of `f` on `C`. -/
theorem unconstrained_problem_solutions_constrained_problem_objective_eq
    (f : E → EReal) (C : Set E) (hC_dom : (C ∩ effective_domain f).Nonempty) :
    unconstrained_problem_solutions (constrained_problem_objective f C) =
      constrained_problem_solutions f C := by
  rcases hC_dom with ⟨z, hzC, hz_dom⟩
  ext x
  rw [mem_unconstrained_problem_solutions_iff, mem_constrained_problem_solutions_iff]
  rw [isMinOn_univ_iff, isMinOn_iff]
  constructor
  · intro hx
    have hx_le_z : constrained_problem_objective f C x ≤ constrained_problem_objective f C z := hx z
    have hxC : x ∈ C := by
      by_contra hxC
      have hx_top : constrained_problem_objective f C x = ⊤ := by
        simp [constrained_problem_objective, hxC]
      have hz_lt_top : constrained_problem_objective f C z < ⊤ := by
        simpa [constrained_problem_objective, hzC] using hz_dom
      exact (not_le_of_gt hz_lt_top) (hx_top ▸ hx_le_z)
    refine ⟨hxC, ?_⟩
    intro y hyC
    simpa [constrained_problem_objective, hxC, hyC] using hx y
  · rintro ⟨hxC, hx⟩ y
    by_cases hyC : y ∈ C
    · simpa [constrained_problem_objective, hxC, hyC] using hx y hyC
    · simp [constrained_problem_objective, hxC, hyC]

/-- Under the standard side condition excluding the value `-∞` off the feasible set, the Chapter
10 composite model with `g = extendedIndicator C` has the same solution set as the constrained
problem `min {f x : x ∈ C}`. -/
theorem unconstrained_problem_solutions_composite_model_objective_extendedIndicator_eq
    (f : E → EReal) (C : Set E) (hC_dom : (C ∩ effective_domain f).Nonempty)
    (h_ne_bot : ∀ y ∉ C, f y ≠ ⊥) :
    unconstrained_problem_solutions (composite_model_objective f (extendedIndicator C)) =
      constrained_problem_solutions f C := by
  rw [composite_model_objective_eq_add]
  rw [← constrained_problem_objective_eq_add_extendedIndicator f C h_ne_bot]
  exact unconstrained_problem_solutions_constrained_problem_objective_eq f C hC_dom

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (f : E → EReal) (C XStar : Set E) (fOpt : ℝ) (Lf : NNReal)

/- Definition 10.4.2 itself is the Chapter 8 constrained convex owner together with the Chapter 5
smoothness clause on `f.toReal`; its Chapter 10 content is the canonical indicator specialization
to `IsCompositeSmoothMinimizationProblem`, not a second root owner. -/

/- Definition 10.4.2: the constrained problem itself is the Chapter 8 owner
`IsConstrainedConvexProblem f C XStar fOpt`. -/
#check IsConstrainedConvexProblem f C XStar fOpt

/- Definition 10.4.2: the smoothness clause is the Chapter 5 condition on `f.toReal` over
`interior (effective_domain f)`. -/
#check is_l_smooth_on (fun x ↦ (f x).toReal) (interior (effective_domain f)) Lf

/-- A Chapter 8 constrained convex problem together with the Chapter 5 smoothness clause on
`f.toReal` canonically induces the Chapter 10 composite smooth minimization owner with
`g = extendedIndicator C`. -/
theorem IsConstrainedConvexProblem.toIsCompositeSmoothMinimizationProblem
    {f : E → EReal} {C XStar : Set E} {fOpt : ℝ} {Lf : NNReal}
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    (h_smooth : is_l_smooth_on (fun x ↦ (f x).toReal) (interior (effective_domain f)) Lf) :
    IsCompositeSmoothMinimizationProblem f (extendedIndicator C) XStar fOpt Lf := by
  have h_ne_bot_off : ∀ y ∉ C, f y ≠ ⊥ := fun y _ ↦ h_problem.ne_bot y
  have hC_dom : (C ∩ effective_domain f).Nonempty := by
    rcases h_problem.feasible_nonempty with ⟨x, hxC⟩
    exact ⟨x, hxC, interior_subset (h_problem.feasible_subset_interior_effective_domain hxC)⟩
  have h_indicator_proper : IsProperExtendedRealFunction (extendedIndicator C) := by
    refine
      { ne_bot := ?_
        effective_domain_nonempty := ?_ }
    · intro x
      by_cases hx : x ∈ C <;> simp [extendedIndicator, hx]
    · rcases h_problem.feasible_nonempty with ⟨x, hxC⟩
      exact ⟨x, by simpa using hxC⟩
  have h_zero_convex : is_convex_function (0 : E → EReal) := by
    refine (is_convex_function_iff_convexOn_toReal ?_).2 ?_
    · intro x hx
      simp
    · simpa [effective_domain] using
        (convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (Set.univ : Set E)))
  have h_indicator_convex : is_convex_function (extendedIndicator C) := by
    have h_constrained_convex :
        is_convex_function (constrained_problem_objective (0 : E → EReal) C) :=
      is_convex_function_constrained_problem_objective h_zero_convex h_problem.feasible_convex
    rw [constrained_problem_objective_eq_add_extendedIndicator
      (0 : E → EReal) C (fun _ _ ↦ by simp)] at h_constrained_convex
    simpa [composite_model_objective] using h_constrained_convex
  refine
    { f_ne_bot := h_problem.ne_bot
      g_proper := h_indicator_proper
      f_closed := h_problem.closed
      g_closed :=
        (extendedIndicator_lowerSemicontinuous_iff_isClosed C).2 h_problem.feasible_closed
      g_convex := h_indicator_convex
      f_effective_domain_convex :=
        effective_domain_convex_of_is_convex_function h_problem.convex
      g_effective_domain_subset_interior_f_effective_domain := by
        simpa using h_problem.feasible_subset_interior_effective_domain
      f_toReal_smooth_on_interior_effective_domain := h_smooth
      optimal_set_eq := by
        calc
          XStar = constrained_problem_solutions f C := h_problem.optimal_set_eq
          _ = unconstrained_problem_solutions
              (composite_model_objective f (extendedIndicator C)) := by
            symm
            exact
              unconstrained_problem_solutions_composite_model_objective_extendedIndicator_eq
                f C hC_dom h_ne_bot_off
      optimal_set_nonempty := h_problem.optimal_set_nonempty
      optimal_value_isGLB := by
        refine ⟨?_, ?_⟩
        · rintro _ ⟨x, rfl⟩
          by_cases hxC : x ∈ C
          · simpa [composite_model_objective, extendedIndicator, hxC] using
              h_problem.optimal_value_isGLB.left ⟨x, hxC, rfl⟩
          · have hx_top :
                composite_model_objective f (extendedIndicator C) x = ⊤ := by
              simpa [composite_model_objective_apply, extendedIndicator, hxC] using
                EReal.add_top_of_ne_bot (h_ne_bot_off x hxC)
            simp [hx_top]
        · intro b hb
          exact h_problem.optimal_value_isGLB.right <| by
            rintro _ ⟨x, hxC, rfl⟩
            exact hb ⟨x, by simp [composite_model_objective, extendedIndicator, hxC]⟩ }

end

/-! ### Definition_10_4_3 (from Chap10) -/
universe u

section

variable {ι : Type u} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι

variable (f : E → ℝ) (lam : ℝ) (Lf : NNReal)

/- Definition 10.4.3 is `source-facing`: it considers the Euclidean `ℓ¹`-regularized composite
problem
`min_x {f x + λ ‖x‖₁}`
under the standing assumptions `0 < λ` and global `L_f`-smoothness of `f`.

Domain sampling:
- `EuclideanSpace.l1Norm` and the notation `‖x‖₁` from Chapter 6 are the project owner for the
  Euclidean `ℓ¹` norm on finite products;
- `unconstrained_problem_solutions` from Chapter 8 is the source-facing owner for whole-space
  minimization;
- `composite_model_objective` is the Chapter 10 owner for objectives of the form `f + g`;
- `is_l_smooth_on` is the Chapter 5 owner for the smoothness clause.

Primitive data here are therefore the whole-space minimization owner
`unconstrained_problem_solutions` applied to the Chapter 10 composite objective
`composite_model_objective f (fun x ↦ lam * ‖x‖₁)`, together with the explicit source
assumptions `0 < lam` and `is_l_smooth_on f Set.univ Lf`. There is no additional owner-level
wrapper to introduce. -/

set_option linter.hashCommand false

/- Definition 10.4.3: the Euclidean `ℓ¹`-regularized problem is the unconstrained minimization
problem for the Chapter 10 composite objective `x ↦ f x + λ ‖x‖₁`. -/
#check unconstrained_problem_solutions (composite_model_objective f (fun x ↦ lam * ‖x‖₁))

/- Definition 10.4.3: the regularization parameter satisfies the standing positivity condition
`0 < λ`. -/
#check 0 < lam

/- Definition 10.4.3: the smooth term `f` satisfies the whole-space `L_f`-smoothness condition. -/
#check is_l_smooth_on f Set.univ Lf

end

/-! ### Definition_10_4_4 (from Chap10) -/
noncomputable section

universe u

open InnerProductSpace (toDualMap)
open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 10.4.4 is a `bridge/view` specialization in the constrained first-order-method
domain. The recursive owner already exists upstream as Algorithm 8.3's
`projected_subgradient_method`, and the textbook projected-gradient iteration is exactly that owner
specialized to the selected direction `gₖ(x) = ∇ f(x)`. The positive stepsizes remain primitive
data through `PosReal`, while the constrained quadratic minimization clause is derived from Text
9.11's canonical indicator/quadratic projection bridge.

Domain sampling:
- `projected_subgradient_method` and `projected_subgradient_method_succ` from Algorithm 8.3;
- `PosReal` from Definition 6.7;
- `isMinOn_mirror_c_half_squared_norm_indicator_update_iff_eq_projection` from Text 9.11;
- `projectionPoint` from Proposition 3.12 for the ambient-space projection formula.

Accordingly, this file deletes the duplicate local owner and states Definition 10.4.4 directly as
the gradient specialization of the existing Chapter 8 owner. -/
recall projected_subgradient_method
recall projected_subgradient_method_succ
recall isMinOn_mirror_c_half_squared_norm_indicator_update_iff_eq_projection

section

variable (f : E → ℝ) (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
variable (hC_convex : Convex ℝ C) (t : ℕ → PosReal) (x0 : C)

local notation "xpg" =>
  projected_subgradient_method C hC_nonempty hC_closed hC_convex
    (fun _ x ↦ ∇ f (x : E)) (fun k ↦ (t k : ℝ)) x0

/- Definition 10.4.4: for a nonempty closed convex feasible set `C`, stepsizes `t_k`, and a
feasible initial point `x0`, the projected gradient method is exactly the Chapter 8 projected
subgradient sequence specialized to `gₖ(x) = ∇ f(x)`. -/
#check (projected_subgradient_method C hC_nonempty hC_closed hC_convex
  (fun _ x ↦ ∇ f (x : E)) (fun k ↦ (t k : ℝ)) x0 : ℕ → C)

/-- One projected-gradient step applies the canonical metric projection onto `C` to the current
iterate minus the current stepsize times the gradient at that iterate. -/
theorem projected_gradient_method_succ (k : ℕ) :
    xpg (k + 1) =
      metricProjection C hC_nonempty hC_closed.isComplete hC_convex
        ((xpg k : E) - (t k : ℝ) • ∇ f (xpg k : E)) := by
  simpa using
    projected_subgradient_method_succ C hC_nonempty hC_closed hC_convex
      (fun _ x ↦ ∇ f (x : E)) (fun j ↦ (t j : ℝ)) x0 k

/-- Coercing the recursive projected-gradient step to the ambient space gives the textbook
projection formula `x^(k+1) = P_C(x^k - t_k ∇ f(x^k))`. -/
theorem projected_gradient_method_succ_coe (k : ℕ) :
    (xpg (k + 1) : E) =
      Pp[C, hC_nonempty, hC_closed, hC_convex] ((xpg k : E) - (t k : ℝ) • ∇ f (xpg k : E)) := by
  simpa [projectionPoint] using
    congrArg (fun y : C ↦ (y : E)) (projected_gradient_method_succ f C hC_nonempty hC_closed
      hC_convex t x0 k)

-- Proof sketch: specialize Text 9.11's Euclidean indicator/projection bridge at the current
-- iterate `x^k`, the gradient `∇ f(x^k)`, and the positive stepsize `t_k`. Then rewrite the
-- chosen next iterate using `projected_gradient_method_succ_coe`.
/-- The next projected-gradient iterate minimizes the canonical Euclidean indicator/quadratic
Mirror-C update objective with current base point `x^k`, gradient `∇ f(x^k)`, and positive
stepsize `t_k`; by Text 9.11 this is exactly the textbook constrained quadratic argmin formula. -/
theorem projected_gradient_method_step_isMinOn (k : ℕ) :
    IsMinOn
      (mirror_c_update_objective (extendedIndicator C)
        (fun y : E ↦ ((((1 / 2 : ℝ) * ‖y‖ ^ (2 : ℕ) : ℝ) : EReal)))
        (xpg k : E) (toDualMap ℝ E (∇ f (xpg k : E))) (t k)
      )
      Set.univ
      (xpg (k + 1) : E) := by
  simpa using
    (isMinOn_mirror_c_half_squared_norm_indicator_update_iff_eq_projection
      C hC_nonempty hC_closed hC_convex (xpg k : E) (∇ f (xpg k : E))
      (xpg (k + 1) : E) (t k).2).2
      (projected_gradient_method_succ_coe f C hC_nonempty hC_closed hC_convex t x0 k)

end

end

/-! ### Lemma_10_4 (from Chap10) -/
noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
variable (f g : E → EReal) (Lf : NNReal)
variable [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
variable [Fact (is_convex_function g)] (hf_ne_bot : ∀ y, f y ≠ ⊥)
variable (hf_effective_domain_convex : Convex ℝ (effective_domain f))
variable (hg_effective_domain_subset_interior_f_effective_domain :
  effective_domain g ⊆ interior (effective_domain f))
variable (hf_toReal_smooth_on_interior_effective_domain :
  is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)

local notation "F" => composite_model_objective f g

/- Lemma 10.4 is `source-facing` in the Chapter 10 proximal-gradient API.

Domain sampling:
- `IsCompositeSmoothMinimizationProblem` from Definition 10.3 is the chapter owner separating
  primitive assumptions from derived facts for composite smooth minimization, with `f_ne_bot` as
  the primitive source-facing non-`⊥` assumption on the smooth term;
- `composite_model_objective` from Definition 10.2 is the chapter owner for the value `F = f + g`;
- `prox_grad_operator` from Definition 10.9 is the canonical prox-gradient update `T_L`;
- `gradient_mapping` from Definition 10.5 is the owner of the residual `G_L = L • (id - T_L)`.

This lemma stays `source-facing`, so it keeps only the primitive one-step descent hypotheses it
actually uses. In particular, the smooth term must still exclude the value `⊥`, but the
nonemptiness part of `IsProperExtendedRealFunction f` is derived data in Chapter 10 rather than
primitive source content, so the hypothesis is kept at the exact `f_ne_bot` level. The scaled
residual is likewise derived API and should be stated through `gradient_mapping` rather than as a
separate raw formula in the conclusion. -/

-- Proof sketch: let `x⁺ = T[L, f, g] x`. Apply the Chapter 5 descent lemma to
-- `(fun y ↦ (f y).toReal)` at `x` and `x⁺`, use the prox optimality inequality for the scaled
-- function `(1 / L) • g` to control the linear term by `g x - g x⁺ - L ‖x - x⁺‖²`, and then
-- rewrite the result in terms of `composite_model_objective` and the residual
-- `L • (x - x⁺) = G_L^{f,g}(x)`.
/-- Helper for Lemma 10.4: the prox-gradient update lies in the effective domain of `g`. -/
lemma prox_grad_operator_mem_effective_domain_g
    (L : PosReal)
    (x : interior (effective_domain f)) :
    T[L, f, g] x ∈ effective_domain g := by
  let hg_closed : LowerSemicontinuous g := Fact.out
  let hg_convex : is_convex_function g := Fact.out
  let hg_scaled :=
    scaled_function_proper_closed_convex_of_pos g inferInstance hg_closed hg_convex (1 / L)
  have hprox :
      prox[((((1 / L : PosReal) : EReal) • g))]
        ((x : E) - (1 / L : ℝ) • ∇ (fun y ↦ (f y).toReal) (x : E)) =
          {T[L, f, g] x} := by
    -- Expand the Chapter 10 prox-grad operator back to the singleton proximal step.
    simpa [proximal_gradient_step] using prox_grad_operator_eq_singleton f g L x
  rcases prox_singleton_implies_effective_domain_and_inner_support
      ((((1 / L : PosReal) : EReal) • g))
      hg_scaled.1
      hg_scaled.2.2
      ((x : E) - (1 / L : ℝ) • ∇ (fun y ↦ (f y).toReal) (x : E))
      (T[L, f, g] x)
      hprox with
    ⟨hxPlus_eff_scaled, _⟩
  -- Finiteness for the scaled penalty is equivalent to finiteness for `g` itself.
  exact
    (mem_effective_domain_scaled_function_iff g (1 / L) inferInstance (T[L, f, g] x)).mp
      hxPlus_eff_scaled

include hf_ne_bot hf_effective_domain_convex
  hg_effective_domain_subset_interior_f_effective_domain
  hf_toReal_smooth_on_interior_effective_domain

/-- Helper for Lemma 10.4: the prox-gradient update stays in the interior of `dom(f)`. -/
lemma prox_grad_operator_mem_interior_effective_domain_f
    (L : PosReal)
    (x : interior (effective_domain f)) :
    T[L, f, g] x ∈ interior (effective_domain f) := by
  -- The standing domain inclusion upgrades the previous `dom(g)` finiteness to `int(dom(f))`.
  exact
    hg_effective_domain_subset_interior_f_effective_domain
      (prox_grad_operator_mem_effective_domain_g
        (f := f)
        (g := g)
        L
        x)

/-- Helper for Lemma 10.4: the proximal support inequality controls the smooth linear term in
real-valued form. -/
lemma prox_grad_linear_term_le_toReal
    (L : PosReal)
    (x : interior (effective_domain f))
    (hxg : (x : E) ∈ effective_domain g) :
    inner ℝ (∇ (fun y ↦ (f y).toReal) (x : E)) (T[L, f, g] x - (x : E)) ≤
      -(L : ℝ) * ‖T[L, f, g] x - (x : E)‖ ^ (2 : ℕ) +
        (g (x : E)).toReal - (g (T[L, f, g] x)).toReal := by
  let xPlus : E := T[L, f, g] x
  let z : E := (x : E) - (1 / L : ℝ) • ∇ (fun y ↦ (f y).toReal) (x : E)
  let hg_convex : is_convex_function g := Fact.out
  let hg_proper : IsProperExtendedRealFunction g := inferInstance
  have hprox : prox[((((1 / L : PosReal) : EReal) • g))] z = {xPlus} := by
    -- The Chapter 10 prox-gradient step is exactly the singleton proximal point of `(1 / L) g`.
    simpa [xPlus, z, proximal_gradient_step] using prox_grad_operator_eq_singleton f g L x
  rcases scaled_prox_singleton_support_of_proper_convex
      (f := g) (μ := 1 / L) inferInstance hg_convex z xPlus hprox with
    ⟨hxPlus_eff, hsupport⟩
  have hx_val :
      g (x : E) = (((g (x : E)).toReal : ℝ) : EReal) := by
    exact (EReal.coe_toReal (mem_effective_domain.mp hxg).ne (hg_proper.ne_bot _)).symm
  have hxPlus_val :
      g xPlus = (((g xPlus).toReal : ℝ) : EReal) := by
    exact (EReal.coe_toReal (mem_effective_domain.mp hxPlus_eff).ne (hg_proper.ne_bot _)).symm
  have hsupport_real :
      inner ℝ ((1 / (1 / L : PosReal) : ℝ) • (z - xPlus)) ((x : E) - xPlus) ≤
        (g (x : E)).toReal - (g xPlus).toReal := by
    have hsupportE := hsupport (x : E) hxg
    rw [hx_val, hxPlus_val] at hsupportE
    have hsupportE' :
        (((inner ℝ ((1 / (1 / L : PosReal) : ℝ) • (z - xPlus)) ((x : E) - xPlus) : ℝ)) :
            EReal) ≤
          ((((g (x : E)).toReal - (g xPlus).toReal : ℝ)) : EReal) := by
      simpa [EReal.coe_sub] using hsupportE
    exact EReal.coe_le_coe_iff.mp hsupportE'
  have hLinv : (1 / (1 / L : PosReal) : ℝ) = (L : ℝ) := by
    simp [PosReal.coe_inv]
  have hleft :
      inner ℝ ((1 / (1 / L : PosReal) : ℝ) • (z - xPlus)) ((x : E) - xPlus) =
        (L : ℝ) * ‖(x : E) - xPlus‖ ^ (2 : ℕ) -
          inner ℝ (∇ (fun y ↦ (f y).toReal) (x : E)) ((x : E) - xPlus) := by
    -- Expanding the forward point `z` isolates the residual square and the linear gradient term.
    have hz_sub :
        z - xPlus = ((x : E) - xPlus) - (1 / L : ℝ) • ∇ (fun y ↦ (f y).toReal) (x : E) := by
      dsimp [z]
      abel
    rw [hLinv, hz_sub, smul_sub, inner_sub_left]
    have hnorm :
        inner ℝ ((L : ℝ) • ((x : E) - xPlus)) ((x : E) - xPlus) =
          (L : ℝ) * ‖(x : E) - xPlus‖ ^ (2 : ℕ) := by
      calc
        inner ℝ ((L : ℝ) • ((x : E) - xPlus)) ((x : E) - xPlus) =
            (starRingEnd ℝ) (L : ℝ) * inner ℝ ((x : E) - xPlus) ((x : E) - xPlus) := by
          rw [inner_smul_left]
        _ = (L : ℝ) * ‖(x : E) - xPlus‖ ^ (2 : ℕ) := by
          simp [real_inner_self_eq_norm_sq]
    have hgrad :
        inner ℝ ((L : ℝ) • ((1 / L : ℝ) • ∇ (fun y ↦ (f y).toReal) (x : E))) ((x : E) - xPlus) =
          inner ℝ (∇ (fun y ↦ (f y).toReal) (x : E)) ((x : E) - xPlus) := by
      rw [smul_smul]
      have hcancel : ((L : ℝ) * (1 / L : ℝ)) = 1 := by
        field_simp [show (L : ℝ) ≠ 0 by exact (PosReal.coe_pos L).ne']
      rw [hcancel, one_smul]
    rw [hnorm, hgrad]
  have haux :
      -inner ℝ (∇ (fun y ↦ (f y).toReal) (x : E)) ((x : E) - xPlus) ≤
        -(L : ℝ) * ‖(x : E) - xPlus‖ ^ (2 : ℕ) +
          (g (x : E)).toReal - (g xPlus).toReal := by
    rw [hleft] at hsupport_real
    linarith
  have hdir :
      inner ℝ (∇ (fun y ↦ (f y).toReal) (x : E)) (xPlus - (x : E)) =
        -inner ℝ (∇ (fun y ↦ (f y).toReal) (x : E)) ((x : E) - xPlus) := by
    have hsub : xPlus - (x : E) = -((x : E) - xPlus) := by
      abel
    rw [hsub, inner_neg_right]
  -- Replace `xPlus - x` by the negative residual and use symmetry of the norm.
  simpa [xPlus, hdir, norm_sub_rev] using haux

/-- Helper for Lemma 10.4: the squared norm of the gradient mapping is the squared residual norm
scaled by `L^2`. -/
lemma gradient_mapping_norm_sq_eq_residual_sq
    (L : PosReal)
    (x : interior (effective_domain f)) :
    ‖G[L, f, g] x‖ ^ (2 : ℕ) =
      (L : ℝ) ^ (2 : ℕ) * ‖((x : E) - T[L, f, g] x)‖ ^ (2 : ℕ) := by
  -- Expand `G_L(x) = L • (x - T_L(x))` and square the norm.
  rw [gradient_mapping_apply, norm_smul, Real.norm_eq_abs, abs_of_pos L.2, pow_two, pow_two]
  ring

/-- Lemma 10.4: if `g` is proper, closed, and convex; `effective_domain f` is convex;
`effective_domain g ⊆ interior (effective_domain f)`; and `(fun y ↦ (f y).toReal)` is
`L_f`-smooth on `interior (effective_domain f)`, then for every positive stepsize `L` the
composite objective `F = f + g` decreases along one prox-grad step by at least
`((L - L_f / 2) / L^2) ‖G_L^{f,g}(x)‖²`. -/
theorem prox_grad_sufficient_decrease
    (L : PosReal)
    (x : interior (effective_domain f)) :
    F (x : E) - F (T[L, f, g] x) ≥
      ((((L : ℝ) - (Lf : ℝ) / 2) / (L : ℝ) ^ (2 : ℕ) *
          ‖G[L, f, g] x‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  let xPlus : E := T[L, f, g] x
  let hg_proper : IsProperExtendedRealFunction g := inferInstance
  have hx_eff_f : (x : E) ∈ effective_domain f := interior_subset x.property
  have hxPlus_int_f :
      xPlus ∈ interior (effective_domain f) :=
    prox_grad_operator_mem_interior_effective_domain_f
      (f := f)
      (g := g)
      (hf_ne_bot := hf_ne_bot)
      (hf_effective_domain_convex := hf_effective_domain_convex)
      (hg_effective_domain_subset_interior_f_effective_domain :=
        hg_effective_domain_subset_interior_f_effective_domain)
      (hf_toReal_smooth_on_interior_effective_domain :=
        hf_toReal_smooth_on_interior_effective_domain)
      (L := L)
      (x := x)
  have hxPlus_eff_f : xPlus ∈ effective_domain f := interior_subset hxPlus_int_f
  have hxPlus_eff_g : xPlus ∈ effective_domain g :=
    prox_grad_operator_mem_effective_domain_g
      (f := f)
      (g := g)
      (L := L)
      (x := x)
  by_cases hxg : (x : E) ∈ effective_domain g
  · have hfx_val :
        f (x : E) = (((f (x : E)).toReal : ℝ) : EReal) := by
      exact (EReal.coe_toReal (mem_effective_domain.mp hx_eff_f).ne (hf_ne_bot _)).symm
    have hfxPlus_val :
        f xPlus = (((f xPlus).toReal : ℝ) : EReal) := by
      exact (EReal.coe_toReal (mem_effective_domain.mp hxPlus_eff_f).ne (hf_ne_bot _)).symm
    have hgx_val :
        g (x : E) = (((g (x : E)).toReal : ℝ) : EReal) := by
      exact (EReal.coe_toReal (mem_effective_domain.mp hxg).ne (hg_proper.ne_bot _)).symm
    have hgxPlus_val :
        g xPlus = (((g xPlus).toReal : ℝ) : EReal) := by
      exact (EReal.coe_toReal (mem_effective_domain.mp hxPlus_eff_g).ne (hg_proper.ne_bot _)).symm
    have hdescent :
        (f xPlus).toReal ≤
          (f (x : E)).toReal +
            inner ℝ (∇ (fun y ↦ (f y).toReal) (x : E)) (xPlus - (x : E)) +
            ((Lf : ℝ) / 2) * ‖xPlus - (x : E)‖ ^ (2 : ℕ) := by
      -- Apply the Chapter 5 descent lemma at `x` and the realized successor `xPlus`.
      simpa [xPlus, norm_sub_rev] using
        (is_l_smooth_on_descent_lemma
          (L := Lf)
          (D := interior (effective_domain f))
          (f := fun y ↦ (f y).toReal)
          hf_effective_domain_convex.interior
          hf_toReal_smooth_on_interior_effective_domain
          x.property
          hxPlus_int_f)
    have hlinear :
        inner ℝ (∇ (fun y ↦ (f y).toReal) (x : E)) (xPlus - (x : E)) ≤
          -(L : ℝ) * ‖xPlus - (x : E)‖ ^ (2 : ℕ) +
            (g (x : E)).toReal - (g xPlus).toReal := by
      -- The Chapter 6 singleton support inequality controls the linear model error.
      simpa [xPlus] using
        (prox_grad_linear_term_le_toReal
          (f := f)
          (g := g)
          (hf_ne_bot := hf_ne_bot)
          (hf_effective_domain_convex := hf_effective_domain_convex)
          (hg_effective_domain_subset_interior_f_effective_domain :=
            hg_effective_domain_subset_interior_f_effective_domain)
          (hf_toReal_smooth_on_interior_effective_domain :=
            hf_toReal_smooth_on_interior_effective_domain)
          (L := L)
          (x := x)
          (hxg := hxg))
    have hgap_real :
        ((L : ℝ) - (Lf : ℝ) / 2) * ‖xPlus - (x : E)‖ ^ (2 : ℕ) ≤
          (f (x : E)).toReal + (g (x : E)).toReal -
            ((f xPlus).toReal + (g xPlus).toReal) := by
      -- Adding the two real inequalities yields the exact one-step objective gap.
      linarith
    have hcoeff_real :
        (((L : ℝ) - (Lf : ℝ) / 2) / (L : ℝ) ^ (2 : ℕ) * ‖G[L, f, g] x‖ ^ (2 : ℕ)) =
          ((L : ℝ) - (Lf : ℝ) / 2) * ‖xPlus - (x : E)‖ ^ (2 : ℕ) := by
      rw [gradient_mapping_norm_sq_eq_residual_sq
        (f := f)
        (g := g)
        (hf_ne_bot := hf_ne_bot)
        (hf_effective_domain_convex := hf_effective_domain_convex)
        (hg_effective_domain_subset_interior_f_effective_domain :=
          hg_effective_domain_subset_interior_f_effective_domain)
        (hf_toReal_smooth_on_interior_effective_domain :=
          hf_toReal_smooth_on_interior_effective_domain)
        (L := L)
        (x := x)]
      have hL0 : (L : ℝ) ≠ 0 := (PosReal.coe_pos L).ne'
      rw [pow_two]
      have hnorm :
          ‖(x : E) - T[L, f, g] x‖ ^ (2 : ℕ) = ‖xPlus - (x : E)‖ ^ (2 : ℕ) := by
        simp [xPlus, norm_sub_rev]
      rw [hnorm]
      field_simp [hL0]
    have hFx :
        F (x : E) = ((((f (x : E)).toReal + (g (x : E)).toReal : ℝ)) : EReal) := by
      -- On the finite branch, the composite objective is the sum of two finite real values.
      rw [composite_model_objective_apply, hfx_val, hgx_val]
      exact (EReal.coe_add (f (x : E)).toReal (g (x : E)).toReal).symm
    have hFxPlus :
        F xPlus = ((((f xPlus).toReal + (g xPlus).toReal : ℝ)) : EReal) := by
      rw [composite_model_objective_apply, hfxPlus_val, hgxPlus_val]
      exact (EReal.coe_add (f xPlus).toReal (g xPlus).toReal).symm
    have hFgap :
        F (x : E) - F xPlus =
          ((((f (x : E)).toReal + (g (x : E)).toReal) -
              ((f xPlus).toReal + (g xPlus).toReal) : ℝ) : EReal) := by
      rw [hFx, hFxPlus, EReal.coe_sub]
    rw [hFgap, hcoeff_real]
    exact EReal.coe_le_coe_iff.mpr hgap_real
  · have hgx_top : g (x : E) = ⊤ := by
      rw [mem_effective_domain] at hxg
      exact le_antisymm le_top (not_lt.mp hxg)
    have hfxPlus_val :
        f xPlus = (((f xPlus).toReal : ℝ) : EReal) := by
      exact (EReal.coe_toReal (mem_effective_domain.mp hxPlus_eff_f).ne (hf_ne_bot _)).symm
    have hgxPlus_val :
        g xPlus = (((g xPlus).toReal : ℝ) : EReal) := by
      exact (EReal.coe_toReal (mem_effective_domain.mp hxPlus_eff_g).ne (hg_proper.ne_bot _)).symm
    have hFx_top : F (x : E) = ⊤ := by
      -- Outside `dom(g)`, the composite value is `⊤` because `f` never takes the value `⊥`.
      rw [composite_model_objective_apply, hgx_top]
      exact EReal.add_top_of_ne_bot (hf_ne_bot (x : E))
    have hFxPlus :
        F xPlus = ((((f xPlus).toReal + (g xPlus).toReal : ℝ)) : EReal) := by
      rw [composite_model_objective_apply, hfxPlus_val, hgxPlus_val]
      exact (EReal.coe_add (f xPlus).toReal (g xPlus).toReal).symm
    rw [hFx_top, hFxPlus, EReal.top_sub_coe]
    exact le_top

end
