import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_10_8 (from Chap10) -/
noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Corollary 10.8 is `source-facing`.

Domain sampling in the local Chapter 10 owner ecosystem:
- `IsCompositeSmoothMinimizationProblem` from Definition 10.3 separates the primitive smooth-term
  hypothesis `f_ne_bot : ∀ y, f y ≠ ⊥` from the derived properness of `f`;
- `effective_domain` and `finite_domain` from Chapters 2 and 3 are the canonical domain owners for
  extended-real functions;
- `is_differentiable_at` from Definition 3.10 is the Chapter 3 owner notion used by Theorem 10.7.

This file remains `source-facing`, so it should use only the primitive smooth-term data actually
needed here: `f` never takes the value `⊥`. The nonempty-domain part of properness is derived
elsewhere in Chapter 10 from properness of `g` and the domain-inclusion hypothesis, so keeping full
properness of `f` in these local statements would overstate the source mathematics. -/

-- Proof sketch: use `is_l_smooth_on_iff` on `interior (effective_domain f)` to obtain
-- differentiability of `fun y ↦ (f y).toReal` at `x`, and use the no-`⊥` hypothesis to rewrite
-- the Chapter 3 finite-domain interior condition as `x ∈ interior (effective_domain f)`.
/-- An extended-real-valued function that never takes the value `-∞` and is smooth on
`interior (effective_domain f)` is differentiable there in the Chapter 3 sense. -/
theorem is_differentiable_at_of_mem_interior_effective_domain
    {f : E → EReal} (hf_ne_bot : ∀ y, f y ≠ ⊥) {Lf : NNReal}
    (hf_smooth : is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)
    {x : E} (hx : x ∈ interior (effective_domain f)) :
    is_differentiable_at f x := by
  simpa [is_differentiable_at, finite_domain_eq_effective_domain hf_ne_bot] using
    ⟨hx, hf_smooth.1 x hx⟩

end

section

variable {E : Type u}
variable {f g : E → EReal}

local notation "F" => composite_model_objective f g

-- Proof sketch: the forward implication is restriction of a global minimizer. For the converse,
-- if `y ∉ effective_domain g`, then `g y = ⊤`, and the no-`⊥` hypothesis on `f` gives
-- `f y ≠ ⊥`, hence
-- `f y + g y = ⊤`; therefore points outside `effective_domain g` cannot improve the objective.
/-- If the smooth term never takes the value `-∞`, then minimizing `f + g` over all of `E` is
equivalent to minimizing it on `effective_domain g`, because the composite objective is `⊤`
outside `effective_domain g`. -/
theorem isMinOn_composite_model_objective_univ_iff_isMinOn_effective_domain
    (hf_ne_bot : ∀ y, f y ≠ ⊥) {xStar : E} :
    IsMinOn F Set.univ xStar ↔ IsMinOn F (effective_domain g) xStar := by
  rw [isMinOn_univ_iff, isMinOn_iff]
  constructor
  · intro hxMin y _
    exact hxMin y
  · intro hxMin y
    by_cases hy : y ∈ effective_domain g
    · exact hxMin y hy
    · have hgy_top : g y = ⊤ := by
        exact le_antisymm le_top (not_lt.mp (by simpa using hy))
      have hobjective_top : F y = ⊤ := by
        simp [hgy_top, hf_ne_bot y]
      rw [hobjective_top]
      exact le_top

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: send `xStar ∈ effective_domain g` into `interior (effective_domain f)` using the
-- domain-inclusion hypothesis, use smoothness plus the no-`⊥` hypothesis to obtain
-- `is_differentiable_at f xStar`, apply Theorem 10.7 to rewrite vanishing of the gradient
-- mapping as stationarity, then
-- apply Theorem 3.35 and the domain-restriction lemma above to identify stationarity with global
-- optimality of the composite objective.
/-- Corollary 10.8: if `g` is proper, closed, and convex, `effective_domain g ⊆ interior
(effective_domain f)`, `f` never takes the value `-∞`, `f` is `L_f`-smooth on
`interior (effective_domain f)`, and `f` is convex, then for `xStar ∈ effective_domain g`, the
gradient mapping vanishes at `xStar` if and only if `xStar` is a global minimizer of the
composite objective `F(x) = f(x) + g(x)`. -/
theorem gradient_mapping_eq_zero_iff_optimal_composite_model_objective
    (f g : E → EReal) (hf_ne_bot : ∀ y, f y ≠ ⊥)
    [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
    [Fact (is_convex_function g)] (Lf : NNReal)
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain g ⊆ interior (effective_domain f))
    (hf_toReal_smooth_on_interior_effective_domain :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)
    (hf_convex : is_convex_function f) (L : PosReal) {xStar : E}
    (hxStar : xStar ∈ effective_domain g) :
    G[L, f, g] ⟨xStar, hg_effective_domain_subset_interior_f_effective_domain hxStar⟩ = 0 ↔
      IsMinOn (composite_model_objective f g) Set.univ xStar := by
  let xStarInterior :=
    (⟨xStar, hg_effective_domain_subset_interior_f_effective_domain hxStar⟩ :
      interior (effective_domain f))
  have hdiff : is_differentiable_at f xStar :=
    is_differentiable_at_of_mem_interior_effective_domain
      hf_ne_bot
      hf_toReal_smooth_on_interior_effective_domain
      xStarInterior.property
  have hgradient :
      G[L, f, g] xStarInterior = 0 ↔ is_stationary_point f g xStar := by
    have hgradient' :
        G[L, f, g] xStarInterior = 0 ↔ is_stationary_point f g (xStarInterior : E) :=
      gradient_mapping_eq_zero_iff_is_stationary_point L xStarInterior hdiff
    simpa [xStarInterior] using hgradient'
  have hg_convex : is_convex_function g := ‹Fact (is_convex_function g)›.1
  have hoptimal :
      IsMinOn (composite_model_objective f g) (effective_domain g) xStar ↔
        is_stationary_point f g xStar := by
    simpa [isMinOn_composite_model_objective_iff] using
      (isMinOn_iff_is_stationary_point hg_convex hxStar hdiff hf_convex)
  calc
    G[L, f, g] ⟨xStar, hg_effective_domain_subset_interior_f_effective_domain hxStar⟩ = 0 ↔
        is_stationary_point f g xStar := by
          simpa [xStarInterior] using hgradient
    _ ↔ IsMinOn (composite_model_objective f g) (effective_domain g) xStar := hoptimal.symm
    _ ↔ IsMinOn (composite_model_objective f g) Set.univ xStar :=
      (isMinOn_composite_model_objective_univ_iff_isMinOn_effective_domain hf_ne_bot).symm

end

/-! ### Definition_10_8 (from Chap10) -/
noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 10.8 is `source-facing` in the Chapter 10 proximal-gradient API.

Domain sampling in the proximal-gradient domain identifies the relevant owners:
- `prox[...]` from Chapter 6 is the `core/canonical` owner for the set-valued proximal update in
  textbook stepsize language;
- `proximal_gradient_step` from Algorithm 10.1 is the canonical reciprocal-curvature bridge from
  the stepsize update to the chapter's curvature-parametrized prox-gradient owner;
- `mem_proximal_gradient_step_iff_isMinOn_curvature_model` from Algorithm 10.66 is the
  curvature-model argmin bridge for that one-step owner;
- `DifferentiableAt` is the canonical regularity owner ensuring that the displayed `∇ f(x^k)` is
  the actual textbook gradient at the iterate;
- `PosReal` is the canonical owner for positive stepsizes.

Primitive data:
- positive stepsizes `t_k`;
- actual differentiability of `f` at each iterate `x^k`;
- the direct stepsize proximal update
  `x^(k+1) ∈ prox[t_k g](x^k - t_k ∇ f(x^k))`.

Derived API:
- the reciprocal-curvature reformulation through `proximal_gradient_step` and
  `is_proximal_gradient_trajectory` is a `bridge/view`;
- the textbook argmin clause with quadratic coefficient `1 / (2 t_k)` is a further
  `bridge/view` consequence of Algorithm 10.66.

Accordingly, this file does not own a second local update-objective definition or a parallel
chosen-step wrapper. The source-facing owner is stated directly in textbook stepsize language on
the proximal map, while the reciprocal-curvature trajectory view is exposed separately as a bridge
to Algorithm 10.1. -/

/-- Definition 10.8: sequences of iterates `x` and positive stepsizes `t` follow the
proximal-gradient method for `f + g` when `f` is differentiable at every iterate `x^k` and the
iterates satisfy the textbook stepsize update
`x^(k+1) ∈ prox[t_k g](x^k - t_k ∇ f(x^k))`. -/
def is_proximal_gradient_trajectory_with_stepsizes
    (f : E → ℝ) (g : E → EReal) (x : ℕ → E) (t : ℕ → PosReal) : Prop :=
  ∀ k : ℕ,
    DifferentiableAt ℝ f (x k) ∧
      x (k + 1) ∈ prox[(((t k : ℝ) : EReal) • g)] (x k - (t k : ℝ) • ∇ f (x k))

/-- Rewriting the reciprocal-curvature one-step owner `proximal_gradient_step` at `L = t⁻¹`
recovers the textbook stepsize proximal update `prox[t g](x - t ∇ f(x))`. -/
theorem proximal_gradient_step_eq_stepsize_form
    (f : E → ℝ) (g : E → EReal) (xk : E) (t : PosReal) :
    proximal_gradient_step f.toEReal g xk t⁻¹ =
      prox[(((t : ℝ) : EReal) • g)] (xk - (t : ℝ) • ∇ f xk) := by
  rw [proximal_gradient_step]
  rw [show (((1 / t⁻¹ : PosReal) : EReal)) = (((t : ℝ) : EReal)) by
    simp [PosReal.coe_inv]]
  rw [show (1 / (t⁻¹ : PosReal) : ℝ) = (t : ℝ) by
    simp [PosReal.coe_inv]]
  rfl

/-- A Definition 10.8 trajectory satisfies, at each iteration `k`, the primitive textbook data:
`f` is differentiable at `x^k` and `x^(k+1)` belongs to the stepsize proximal update set. -/
theorem is_proximal_gradient_trajectory_with_stepsizes_step
    {f : E → ℝ} {g : E → EReal} {x : ℕ → E} {t : ℕ → PosReal}
    (h : is_proximal_gradient_trajectory_with_stepsizes f g x t) (k : ℕ) :
    DifferentiableAt ℝ f (x k) ∧
      x (k + 1) ∈ prox[(((t k : ℝ) : EReal) • g)] (x k - (t k : ℝ) • ∇ f (x k)) :=
  h k

/-- Along a Definition 10.8 stepsize trajectory, the smooth term `f` is differentiable at each
iterate `x^k`. -/
theorem is_proximal_gradient_trajectory_with_stepsizes_differentiableAt
    {f : E → ℝ} {g : E → EReal} {x : ℕ → E} {t : ℕ → PosReal}
    (h : is_proximal_gradient_trajectory_with_stepsizes f g x t) (k : ℕ) :
    DifferentiableAt ℝ f (x k) :=
  (is_proximal_gradient_trajectory_with_stepsizes_step h k).1

/-- Along a Definition 10.8 stepsize trajectory, the next iterate `x^(k+1)` belongs to the
textbook proximal update `prox[t_k g](x^k - t_k ∇ f(x^k))`. -/
theorem is_proximal_gradient_trajectory_with_stepsizes_mem_prox
    {f : E → ℝ} {g : E → EReal} {x : ℕ → E} {t : ℕ → PosReal}
    (h : is_proximal_gradient_trajectory_with_stepsizes f g x t) (k : ℕ) :
    x (k + 1) ∈ prox[(((t k : ℝ) : EReal) • g)] (x k - (t k : ℝ) • ∇ f (x k)) :=
  (is_proximal_gradient_trajectory_with_stepsizes_step h k).2

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Along a Definition 10.8 stepsize trajectory, the next iterate `x^(k+1)` belongs to the
canonical prox-gradient step with reciprocal curvature parameter `t_k⁻¹`. -/
theorem is_proximal_gradient_trajectory_with_stepsizes_mem_step
    {f : E → ℝ} {g : E → EReal} {x : ℕ → E} {t : ℕ → PosReal}
    (h : is_proximal_gradient_trajectory_with_stepsizes f g x t) (k : ℕ) :
    x (k + 1) ∈ proximal_gradient_step f.toEReal g (x k) (t k)⁻¹ :=
  by
    simpa [proximal_gradient_step_eq_stepsize_form] using
      is_proximal_gradient_trajectory_with_stepsizes_mem_prox h k

omit [CompleteSpace E] in
private theorem is_differentiable_at_toEReal_of_differentiableAt
    {f : E → ℝ} {x : E} (hdiff : DifferentiableAt ℝ f x) :
    is_differentiable_at f.toEReal x := by
  refine ⟨?_, ?_⟩
  · simp [finite_domain, effective_domain]
  · simpa using hdiff

private theorem reciprocal_stepsize_half_eq_inv_two_mul (t : PosReal) :
    (((t⁻¹ : PosReal) : ℝ) / 2) = 1 / (2 * (t : ℝ)) := by
  have ht : (t : ℝ) ≠ 0 := ne_of_gt t.2
  change (t : ℝ)⁻¹ / 2 = 1 / (2 * (t : ℝ))
  field_simp [ht]

/-- The source-facing Definition 10.8 owner canonically induces the reciprocal-curvature
Algorithm 10.1 trajectory for `f.toEReal` and parameters `L_k = t_k⁻¹`. This is the bridge/view
from textbook stepsize language to the chapter's curvature-language owner. -/
theorem is_proximal_gradient_trajectory_with_stepsizes.toCurvatureTrajectory
    {f : E → ℝ} {g : E → EReal} {x : ℕ → E} {t : ℕ → PosReal}
    (h : is_proximal_gradient_trajectory_with_stepsizes f g x t) :
    is_proximal_gradient_trajectory f.toEReal g x (fun k ↦ (t k)⁻¹) := by
  intro k
  refine ⟨?_, ?_⟩
  · have hx :
        x k ∈ interior (finite_domain f.toEReal) :=
      (is_differentiable_at_toEReal_of_differentiableAt
        (is_proximal_gradient_trajectory_with_stepsizes_differentiableAt h k)).1
    simp [effective_domain] at hx ⊢
  · simpa using is_proximal_gradient_trajectory_with_stepsizes_mem_step h k

-- Proof sketch: specialize Algorithm 10.66's curvature-parameter argmin bridge at `L = t⁻¹` and
-- rewrite `((t⁻¹ : ℝ) / 2) * ‖x - xk‖²` as `‖x - xk‖² / (2 t)`.
/-- For a positive stepsize `t`, the Chapter 10 prox-gradient step with reciprocal curvature `t⁻¹`
is equivalent to the textbook argmin clause
`xNext ∈ argmin_u [f(xk) + ⟪∇ f(xk), u - xk⟫ + g(u) + ‖u - xk‖² / (2 t)]`,
provided `f` is differentiable at `xk` so that the displayed `∇ f(xk)` is the genuine textbook
gradient. -/
theorem mem_proximal_gradient_step_iff_isMinOn_stepsize_model
    {f : E → ℝ} {g : E → EReal} {xk xNext : E} {t : PosReal}
    (hdiff : DifferentiableAt ℝ f xk) :
    xNext ∈ proximal_gradient_step f.toEReal g xk t⁻¹ ↔
      IsMinOn
        (fun u ↦
          ((((f xk : ℝ) : EReal) + ((inner ℝ (∇ f xk) (u - xk) : ℝ) : EReal)) + g u) +
            ((((1 / (2 * (t : ℝ)) : ℝ) * ‖u - xk‖ ^ (2 : ℕ)) : ℝ) : EReal))
        Set.univ xNext := by
  have hcurvature :
      xNext ∈ proximal_gradient_step f.toEReal g xk t⁻¹ ↔
        IsMinOn
          (fun u ↦
            ((((f xk : ℝ) : EReal) + ((inner ℝ (∇ f xk) (u - xk) : ℝ) : EReal)) + g u) +
              ((((((t⁻¹ : PosReal) : ℝ) / 2) * ‖u - xk‖ ^ (2 : ℕ)) : ℝ) : EReal))
          Set.univ xNext :=
    show xNext ∈ proximal_gradient_step f.toEReal g xk t⁻¹ ↔
        IsMinOn
          (fun u ↦
            ((((f xk : ℝ) : EReal) + ((inner ℝ (∇ f xk) (u - xk) : ℝ) : EReal)) + g u) +
              ((((((t⁻¹ : PosReal) : ℝ) / 2) * ‖u - xk‖ ^ (2 : ℕ)) : ℝ) : EReal))
          Set.univ xNext from
      mem_proximal_gradient_step_iff_isMinOn_curvature_model
        (is_differentiable_at_toEReal_of_differentiableAt hdiff)
  simpa [PosReal.coe_inv, reciprocal_stepsize_half_eq_inv_two_mul, Function.toEReal] using
    hcurvature

/-- Definition 10.8 in textbook form: at each iteration `k`, the next iterate `x^(k+1)` globally
minimizes the linearized quadratic model with stepsize `t_k`. The differentiability clause for the
current iterate `x^k` is available separately from
`is_proximal_gradient_trajectory_with_stepsizes_differentiableAt`. -/
theorem is_proximal_gradient_trajectory_with_stepsizes_isMinOn_step
    {f : E → ℝ} {g : E → EReal} {x : ℕ → E} {t : ℕ → PosReal}
    (h : is_proximal_gradient_trajectory_with_stepsizes f g x t) (k : ℕ) :
    IsMinOn
      (fun u ↦
        ((((f (x k) : ℝ) : EReal) + ((inner ℝ (∇ f (x k)) (u - x k) : ℝ) : EReal)) + g u) +
          ((((1 / (2 * (t k : ℝ)) : ℝ) * ‖u - x k‖ ^ (2 : ℕ)) : ℝ) : EReal))
      Set.univ
      (x (k + 1)) := by
  exact
    (mem_proximal_gradient_step_iff_isMinOn_stepsize_model
      (is_proximal_gradient_trajectory_with_stepsizes_differentiableAt h k)).1
      (is_proximal_gradient_trajectory_with_stepsizes_mem_step h k)

end
