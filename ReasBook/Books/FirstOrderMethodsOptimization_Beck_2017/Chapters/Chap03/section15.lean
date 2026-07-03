

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_15 (from Chap03) -/
open Set

universe u

noncomputable section

/- Definition 3.15 is `source-facing`: it defines the constrained extended-real objective attached
to `f` and `C`. The owner abstractions in this domain are the chapter declarations
`extendedIndicator` for the set term, `realEpigraph` for the geometric owner view, and
`is_convex_function` for the convexity predicate. Primitive data are only the original objective
`f`, the feasible set `C`, and the source-facing rule "equal to `f` on `C`, equal to `⊤` off
`C`". The identification with the canonical owner expression `f + δ_C` is derived `bridge/view`
API only: it needs the extra hypothesis that `f` never takes the value `⊥` on `Cᶜ`, because
`x + ⊤ = ⊤` in `EReal` fails exactly at `x = ⊥`. -/
recall extendedIndicator
recall realEpigraph
recall is_convex_function

section

variable {E : Type u}

/-- Definition 3.15: the constrained problem `min {f x : x ∈ C}` is represented by the
extended-real objective that agrees with `f` on `C` and takes the value `⊤` outside `C`. -/
def constrained_problem_objective (f : E → EReal) (C : Set E) : E → EReal :=
  open scoped Classical in
  C.piecewise f fun _ ↦ (⊤ : EReal)

-- Bridge/view layer: when `f` never takes the value `⊥` outside `C`, the source-facing
-- constrained objective agrees with the canonical indicator expression `f + δ_C`.
/-- If `f` never takes the value `⊥` outside `C`, then the constrained objective is `f + δ_C`. -/
theorem constrained_problem_objective_eq_add_extendedIndicator
    (f : E → EReal) (C : Set E) (h_ne_bot : ∀ x ∉ C, f x ≠ ⊥) :
    constrained_problem_objective f C = f + extendedIndicator C := by
  ext x
  by_cases hx : x ∈ C
  · simp [constrained_problem_objective, extendedIndicator, hx]
  · simp [constrained_problem_objective, extendedIndicator, hx,
      EReal.add_top_of_ne_bot (h_ne_bot x hx)]

-- Proof sketch: unfold `constrained_problem_objective`; when `x ∈ C`, the `piecewise` definition
-- selects the branch `f x`.
/-- On the feasible set, the constrained problem objective agrees with the original objective. -/
@[simp] theorem constrained_problem_objective_of_mem
    (f : E → EReal) {C : Set E} {x : E} (hx : x ∈ C) :
    constrained_problem_objective f C x = f x := by
  simp [constrained_problem_objective, hx]

-- Proof sketch: unfold `constrained_problem_objective`; when `x ∉ C`, the `piecewise` definition
-- selects the infeasible-value branch `⊤`.
/-- Outside the feasible set, the constrained problem objective takes the value `⊤`. -/
@[simp] theorem constrained_problem_objective_of_not_mem
    (f : E → EReal) {C : Set E} {x : E} (hx : x ∉ C) :
    constrained_problem_objective f C x = ⊤ := by
  simp [constrained_problem_objective, hx]

/-- A point lies in the effective domain of the constrained objective exactly when it is feasible
and the original objective is finite there. -/
@[simp] theorem mem_effective_domain_constrained_problem_objective
    (f : E → EReal) (C : Set E) (x : E) :
    x ∈ effective_domain (constrained_problem_objective f C) ↔
      x ∈ C ∧ x ∈ effective_domain f := by
  by_cases hx : x ∈ C
  · simp [effective_domain, constrained_problem_objective, hx]
  · simp [effective_domain, constrained_problem_objective, hx]

/-- The effective domain of the constrained objective is the feasible set intersected with the
effective domain of the original objective. -/
theorem effective_domain_constrained_problem_objective
    (f : E → EReal) (C : Set E) :
    effective_domain (constrained_problem_objective f C) = C ∩ effective_domain f := by
  ext x
  simpa using mem_effective_domain_constrained_problem_objective f C x

-- Proof sketch: in the real epigraph, the branch `⊤` outside `C` contributes no points because
-- `⊤ ≤ r` is false for every real `r`. Thus the epigraph is exactly the intersection of the
-- epigraph of `f` with the cylinder `C ×ˢ univ`.
/-- The real epigraph of the constrained objective is the epigraph of `f` restricted to the
feasible set. -/
theorem realEpigraph_constrained_problem_objective
    (f : E → EReal) (C : Set E) :
    realEpigraph (constrained_problem_objective f C) =
      (C ×ˢ (Set.univ : Set ℝ)) ∩ realEpigraph f := by
  ext p
  by_cases hp : p.1 ∈ C <;> simp [realEpigraph, constrained_problem_objective, hp]

end

section

variable {E : Type u} [AddCommMonoid E] [Module ℝ E]

-- Proof sketch: use `realEpigraph_constrained_problem_objective` to rewrite the real epigraph as
-- `(C ×ˢ univ) ∩ realEpigraph f`. Convexity of `C` gives convexity of the cylinder `C ×ˢ univ`,
-- while `hf` is convexity of `realEpigraph f`; their intersection is therefore convex.
/-- If `f` is convex and `C` is convex, then the extended-real objective associated to the
constrained problem is convex. -/
theorem is_convex_function_constrained_problem_objective
    {f : E → EReal} {C : Set E} (hf : is_convex_function f) (hC : Convex ℝ C) :
    is_convex_function (constrained_problem_objective f C) := by
  have hf_epi : Convex ℝ (realEpigraph f) := by
    simpa [is_convex_function, realEpigraph] using hf
  have hconstrained_epi : Convex ℝ (realEpigraph (constrained_problem_objective f C)) := by
    simpa [realEpigraph_constrained_problem_objective] using
      (hC.prod convex_univ).inter hf_epi
  simpa [is_convex_function, realEpigraph] using hconstrained_epi

end

/-! ### Proposition_3_15 (from Chap03) -/
section

open Metric

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-
Proposition 3.15 is `source-facing`: the book states the Euclidean subdifferential as a subset of
`ℝ^n`, so the main declaration should use the chapter Euclidean bridge/view owner
`euclideanSubdifferentialAt`. The continuous-dual owner `subdifferentialAt` remains upstream in
Theorem 3.4 and should only appear through derived bridge lemmas, not as the main public surface
of this proposition.
-/

-- Proof sketch: for `x = 0`, this is Proposition 3.1 specialized to Euclidean space. For
-- `x ≠ 0`, the Euclidean norm is differentiable at `x`, so Theorem 3.13 identifies the owner
-- dual subdifferential with the Riesz functional of the normalized vector, and transporting back
-- along `toDualMap` gives the vector-side singleton `{(‖x‖⁻¹) • x}`.
/-- Proposition 3.15: for the Euclidean norm on `ℝ^n`, the Euclidean/vector-side
subdifferential is the singleton containing the normalized vector `(1 / ‖x‖) • x` away from the
origin, and it is the closed Euclidean unit ball at the origin. -/
theorem euclidean_subdifferentialAt_l2_norm_eq_piecewise (x : E) :
    euclideanSubdifferentialAt (fun y : E ↦ ‖y‖) x =
      if x = 0 then
        closedBall (0 : E) 1
      else
        {((‖x‖⁻¹ : ℝ) • x)} := sorry

end

/-! ### Theorem_3_15 (from Chap03) -/
open scoped Pointwise

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Theorem 3.15 is `source-facing` at the chapter owner
`subdifferential : Set (Module.Dual ℝ E)`. The continuous-dual object
`strongDualSubdifferential` from Theorem 3.1 is only a `bridge/view`, so the main declarations
here stay on the owner abstraction instead of restating the theorem after passing to `StrongDual`.
-/
recall subdifferential

-- Proof sketch: expand membership in the pointwise sum
-- `subdifferential f₁ x + subdifferential f₂ x`, choose `g₁ ∈ subdifferential f₁ x` and
-- `g₂ ∈ subdifferential f₂ x` with sum `g`,
-- and add the two defining subgradient inequalities to obtain the supporting inequality for
-- `f₁ + f₂` at `x`. Membership in the left-hand side already supplies the effective-domain
-- condition for both summands, so no extra hypotheses are primitive in this weak inclusion.
/-- Theorem 3.15 (1): any sum of a subgradient of `f₁` at `x` and a subgradient of `f₂` at `x`
is a subgradient of the pointwise sum `f₁ + f₂` at `x`. -/
theorem sum_subdifferential_subset_subdifferential_add
    (f₁ f₂ : E → EReal) (x : E) :
    subdifferential f₁ x + subdifferential f₂ x ⊆
      subdifferential (f₁ + f₂) x := sorry

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

recall finite_domain
recall is_convex_function

/- Part (2) stays on the same owner `subdifferential`; `finite_domain` is only the source-faithful
interior-point qualification and not a second public owner abstraction. -/

-- Proof sketch: the inclusion `⊇` is the weak sum rule from part (1). For the converse inclusion,
-- apply the max formula to the proper convex function `f₁ + f₂` at an interior point of its
-- finite domain, use additivity of directional derivatives together with the max formula for each
-- summand, and identify compact convex sets with equal support functions. Stating the qualification
-- on `finite_domain` matches the textbook `dom` directly, so no extra global no-`⊥` hypotheses are
-- primitive public data.
/-- Theorem 3.15 (2): if `x` lies in the interior of the finite domains of `f₁` and `f₂`, then
the subdifferential of the pointwise sum is exactly the pointwise sum of the two
subdifferentials. -/
theorem subdifferential_add_eq_sum_subdifferential_of_mem_interiors
    (f₁ f₂ : E → EReal) (x : E)
    (hconvex₁ : is_convex_function f₁)
    (hconvex₂ : is_convex_function f₂)
    (hx₁ : x ∈ interior (finite_domain f₁))
    (hx₂ : x ∈ interior (finite_domain f₂)) :
    subdifferential (f₁ + f₂) x =
      subdifferential f₁ x + subdifferential f₂ x := sorry

end
