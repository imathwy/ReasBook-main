import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Assumption_13_1 (from Chap13) -/
universe u

section

variable {E : Type u}

/-- The optimal value of the generalized conditional-gradient model is the infimum of the attained
composite objective values. -/
noncomputable def generalized_conditional_gradient_optimal_value (f g : E → EReal) : EReal :=
  sInf (Set.range (composite_model_objective f g))

-- Proof sketch: unfold `generalized_conditional_gradient_optimal_value`; the statement is the
-- defining `sInf` formula for the composite objective values.
/-- Expanding the generalized conditional-gradient optimal value gives the `sInf` of the range of
the composite objective. -/
theorem generalized_conditional_gradient_optimal_value_eq_sInf
    (f g : E → EReal) :
    generalized_conditional_gradient_optimal_value f g =
      sInf (Set.range (composite_model_objective f g)) := rfl

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Assumption 13.1 is `source-facing`: it fixes the standing hypotheses for the generalized
conditional-gradient model `min_x (f x + g x)`. Domain sampling identifies the relevant
`core/canonical` owners already present in the project:
- `composite_model_objective` and `unconstrained_problem_solutions` for the optimization object;
- `IsProperExtendedRealFunction`, `LowerSemicontinuous`, and `is_convex_function` for the
  extended-real regularity data;
- `effective_domain` and `is_l_smooth_on` for the domain-compatibility and smoothness clauses.

Primitive data are exactly the regularity and domain-compatibility clauses `(A)` and `(B)`.
Text 13.1 proves optimizer existence from those clauses, so optimal-set nonemptiness is derived
API and should not be stored as an extra primitive field in a second wrapper owner. -/

/-- Assumption 13.1: clauses `(A)` and `(B)` for the generalized conditional-gradient method mean
that `g : E → (-∞, ∞]` is proper, closed, and convex with compact effective domain, while
`f : E → (-∞, ∞]` never takes the value `-∞`, has open convex effective domain containing
`effective_domain g`, and `(fun x ↦ (f x).toReal)` is `L_f`-smooth on `effective_domain f` with
`L_f > 0`. Text 13.1 later derives the nonemptiness of the optimal set `X^*` from these
primitive assumptions. -/
class IsGeneralizedConditionalGradientProblem
    (f g : E → EReal) (Lf : NNReal) : Prop extends IsProperExtendedRealFunction g where
  g_closed : LowerSemicontinuous g
  g_convex : is_convex_function g
  g_effective_domain_compact : IsCompact (effective_domain g)
  f_ne_bot : ∀ x, f x ≠ ⊥
  f_effective_domain_open : IsOpen (effective_domain f)
  f_effective_domain_convex : Convex ℝ (effective_domain f)
  g_effective_domain_subset_f_effective_domain :
    effective_domain g ⊆ effective_domain f
  f_toReal_smooth_on_effective_domain :
    is_l_smooth_on (fun x ↦ (f x).toReal) (effective_domain f) Lf
  Lf_pos : 0 < (Lf : ℝ)

/-- The domain compatibility hypothesis and properness of `g` force `effective_domain f` to be
nonempty. -/
theorem IsGeneralizedConditionalGradientProblem.f_effective_domain_nonempty
    {f g : E → EReal} {Lf : NNReal}
    (h : IsGeneralizedConditionalGradientProblem f g Lf) :
    (effective_domain f).Nonempty := by
  rcases h.toIsProperExtendedRealFunction.effective_domain_nonempty with ⟨x, hx⟩
  exact ⟨x, h.g_effective_domain_subset_f_effective_domain hx⟩

/-- A generalized conditional-gradient problem canonically makes the smooth term `f` a proper
extended-real-valued function. -/
theorem IsGeneralizedConditionalGradientProblem.f_proper
    {f g : E → EReal} {Lf : NNReal}
    (h : IsGeneralizedConditionalGradientProblem f g Lf) :
    IsProperExtendedRealFunction f where
  ne_bot := h.f_ne_bot
  effective_domain_nonempty := h.f_effective_domain_nonempty

-- Proof sketch: `g` is proper, so some `x₀` lies in `effective_domain g`; the domain inclusion
-- puts `x₀` in `effective_domain f`, giving a nonempty effective domain for `f`. The no-`⊥`
-- field supplies the remaining properness clause.
/-- A generalized conditional-gradient problem canonically makes the smooth term `f` a proper
extended-real-valued function. -/
instance {f g : E → EReal} {Lf : NNReal}
    (h : IsGeneralizedConditionalGradientProblem f g Lf) :
    IsProperExtendedRealFunction f :=
  h.f_proper

-- Proof sketch: `effective_domain f` is open, so each `x ∈ effective_domain f` lies in its
-- interior; then apply the Chapter 10 interior-domain differentiability bridge to the smoothness
-- field of `h`.
/-- Under Assumption 13.1, every point of `effective_domain f` is a Chapter 3 differentiability
point of `f`. -/
theorem IsGeneralizedConditionalGradientProblem.is_differentiable_at
    {f g : E → EReal} {Lf : NNReal}
    (h : IsGeneralizedConditionalGradientProblem f g Lf) (x : effective_domain f) :
    is_differentiable_at f x := by
  apply is_differentiable_at_of_mem_interior_effective_domain h.f_ne_bot
  · simpa [h.f_effective_domain_open.interior_eq] using
      h.f_toReal_smooth_on_effective_domain
  · simp [h.f_effective_domain_open.interior_eq]

end

/-! ### Definition_13_1 (from Chap13) -/
universe u

section

variable {E : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Definition 13.1 is `source-facing`: it fixes the standing assumptions for the constrained
convex minimization problem used by the Frank-Wolfe / conditional-gradient method. The relevant
owner abstractions already present in the project are `IsProperExtendedRealFunction`,
`is_convex_function`, `effective_domain`, `IsCompact`, `Convex`, and `DifferentiableOn`, so the
clean public interface is a small `Prop`-valued class on the objective `f` and feasible set `C`
rather than a surrogate packaged optimization object. The primitive data are the no-`⊥` clause
for `f`, the feasible-set hypotheses on `C`, and the domain/differentiability clauses; properness
of `f` is derived from `constraint_nonempty` together with `C ⊆ effective_domain f`. -/

/-- Definition 13.1: the conditional-gradient problem `min {f x | x ∈ C}` has a nonempty convex
compact feasible set `C` in a normed real vector space `E`, an extended-real-valued convex objective
`f : E → (-∞, ∞]`, the feasibility condition `C ⊆ dom f`, an open effective domain `dom f`, and
differentiability of `f.toReal` on `dom f`. -/
class IsConditionalGradientProblem (f : E → EReal) (C : Set E) : Prop where
  f_ne_bot (x : E) : f x ≠ ⊥
  constraint_nonempty : C.Nonempty
  constraint_convex : Convex ℝ C
  constraint_compact : IsCompact C
  f_convex : is_convex_function f
  feasible_subset_effective_domain : C ⊆ effective_domain f
  f_effective_domain_open : IsOpen (effective_domain f)
  f_toReal_differentiableOn_effective_domain :
    DifferentiableOn ℝ (fun x ↦ (f x).toReal) (effective_domain f)

/-- A conditional-gradient problem canonically makes the objective `f` a proper
extended-real-valued function. -/
instance {f : E → EReal} {C : Set E} (h : IsConditionalGradientProblem f C) :
    IsProperExtendedRealFunction f where
  ne_bot := h.f_ne_bot
  effective_domain_nonempty := by
    rcases h.constraint_nonempty with ⟨x, hx⟩
    exact ⟨x, h.feasible_subset_effective_domain hx⟩

-- Proof sketch: an open set equals its interior, so `effective_domain f = interior
-- (effective_domain f)`. Combine this with the feasibility inclusion `C ⊆ effective_domain f`.
/-- A conditional-gradient problem places every feasible point in the interior of the effective
domain of the objective. -/
theorem IsConditionalGradientProblem.feasible_subset_interior_effective_domain
    {f : E → EReal} {C : Set E} (h : IsConditionalGradientProblem f C) :
    C ⊆ interior (effective_domain f) := by
  simpa [h.f_effective_domain_open.interior_eq] using h.feasible_subset_effective_domain

end

/-! ### Text_13_1 (from Chap13) -/
universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f g : E → EReal} {Lf : NNReal}

namespace IsGeneralizedConditionalGradientProblem

/-- Under Assumption 13.1, the composite objective `F(x) = f(x) + g(x)` is lower semicontinuous on
the compact feasible core `effective_domain g`. -/
theorem composite_model_objective_lowerSemicontinuousOn_effective_domain
    (h : IsGeneralizedConditionalGradientProblem f g Lf) :
    LowerSemicontinuousOn (composite_model_objective f g) (effective_domain g) := by
  have hf_cont : ContinuousOn (fun x ↦ ((f x).toReal : EReal)) (effective_domain g) := by
    refine
      (continuous_coe_real_ereal.continuousOn : ContinuousOn ((↑) : ℝ → EReal) Set.univ).comp
        ?_ ?_
    · intro x hx
      exact
        ((h.f_toReal_smooth_on_effective_domain.1 x
          (h.g_effective_domain_subset_f_effective_domain hx)).continuousAt).continuousWithinAt
    · intro x hx
      simp
  have hsum :
      LowerSemicontinuousOn (fun x ↦ ((f x).toReal : EReal) + g x) (effective_domain g) := by
    refine hf_cont.lowerSemicontinuousOn.add' (h.g_closed.lowerSemicontinuousOn _) ?_
    intro x hx
    exact EReal.continuousAt_add (.inl (EReal.coe_ne_top _)) (.inl (EReal.coe_ne_bot _))
  intro x hx
  refine (hsum x hx).congr_of_eventuallyEq hx ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp [EReal.coe_toReal
    (mem_effective_domain.mp (h.g_effective_domain_subset_f_effective_domain hy)).ne
    (h.f_ne_bot y)]

end IsGeneralizedConditionalGradientProblem

-- Proof sketch: use compactness and nonemptiness of `effective_domain g` from properness of `g`,
-- continuity of `f.toReal` on `effective_domain g` from the smoothness hypothesis and domain
-- inclusion, and lower semicontinuity of `g`; then `x ↦ f x + g x` is lower semicontinuous on the
-- nonempty compact set `effective_domain g`, so a generalized Weierstrass theorem yields a global
-- minimizer.
/-- Text 13.1: under Assumption 13.1 (A) and (B), the optimal set `X^*` of the composite
optimization problem `min_x {F(x) ≡ f(x) + g(x)}` is nonempty. -/
theorem generalized_conditional_gradient_optimal_set_nonempty
    (h : IsGeneralizedConditionalGradientProblem f g Lf) :
    (unconstrained_problem_solutions (composite_model_objective f g)).Nonempty := by
  obtain ⟨y, hy⟩ := h.toIsProperExtendedRealFunction.effective_domain_nonempty
  have hyF : y ∈ effective_domain (composite_model_objective f g) := by
    exact mem_effective_domain.mpr <|
      by
        simpa [composite_model_objective_apply] using
          (EReal.add_lt_top
            (mem_effective_domain.mp (h.g_effective_domain_subset_f_effective_domain hy)).ne
            (mem_effective_domain.mp hy).ne)
  obtain ⟨x, _, hxmin⟩ :=
    exists_isMinOn_on_compact
      (composite_model_objective f g)
      (effective_domain g)
      h.composite_model_objective_lowerSemicontinuousOn_effective_domain
      h.g_effective_domain_compact
      ⟨y, ⟨hy, hyF⟩⟩
  have hxmin_univ : IsMinOn (composite_model_objective f g) Set.univ x :=
    (isMinOn_composite_model_objective_univ_iff_isMinOn_effective_domain h.f_ne_bot).2 hxmin
  exact ⟨x, mem_unconstrained_problem_solutions_iff.mpr hxmin_univ⟩

end
