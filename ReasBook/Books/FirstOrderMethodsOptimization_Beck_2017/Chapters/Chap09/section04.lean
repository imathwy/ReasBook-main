import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_9_4 (from Chap09) -/
universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Source-facing note: this item fixes the standing assumptions for the composite mirror-descent
problem `min_x (f x + g x)`. The canonical owners already present in the project are
`IsProperExtendedRealFunction`, `LowerSemicontinuous`, `is_convex_function`,
`SubgradientNormBoundOn`, mathlib's minimizer predicate `IsMinOn`, and `IsGLB`. The source item
includes both the optimizer/value data and the bounded-subgradient constant `L_f`, but later
Chapter 9 statements do not always use the bound. To avoid baking the `L_f` package into
unrelated theorem surfaces, the public API separates the core composite convex minimization owner
from the stronger source-facing mirror-descent problem owner. -/

/-- The core composite-convex minimization assumptions for `min_x (f x + g x)`: `f` and `g` are
proper, closed, and convex, `dom(g) ⊆ interior(dom(f))`, and `XStar = X^*` is the nonempty
optimal set with optimal value `FOpt = F_opt`. -/
class IsCompositeConvexMinimizationProblem
    (f g : E → EReal) (XStar : Set E) (FOpt : ℝ)
    : Prop extends IsProperExtendedRealFunction f where
  g_proper : IsProperExtendedRealFunction g
  f_closed : LowerSemicontinuous f
  f_convex : is_convex_function f
  g_closed : LowerSemicontinuous g
  g_convex : is_convex_function g
  g_effective_domain_subset_interior_f_effective_domain :
    effective_domain g ⊆ interior (effective_domain f)
  optimal_set_eq : XStar = {x | IsMinOn (fun y ↦ f y + g y) Set.univ x}
  optimal_set_nonempty : XStar.Nonempty
  optimal_value_isGLB : IsGLB (Set.range (fun x ↦ f x + g x)) (FOpt : EReal)

/-- Definition 9.4: clauses (A)-(D) for the composite mirror-descent problem
`min_x {F(x) = f(x) + g(x)}` mean the core composite-convex assumptions together with the
bounded-subgradient clause that every continuous-dual subgradient of `f` at every point of
`dom(g)` has norm at most `L_f > 0`. -/
class IsCompositeMirrorDescentProblem
    (f g : E → EReal) (XStar : Set E) (FOpt Lf : ℝ)
    : Prop extends IsCompositeConvexMinimizationProblem f g XStar FOpt where
  Lf_pos : 0 < Lf
  subgradient_norm_le {x : E} {s : StrongDual ℝ E}
      (hx : x ∈ effective_domain g) (hs : s ∈ strongDualSubdifferential f x) :
      ‖s‖ ≤ Lf

/-- A composite convex minimization problem packages both existence of minimizers and the
greatest-lower-bound characterization of the optimal value. -/
instance instFactCompositeOptimalSetNonemptyAndOptimalValueIsGLB
    {f g : E → EReal} {XStar : Set E} {FOpt : ℝ}
    [h : IsCompositeConvexMinimizationProblem f g XStar FOpt] :
    Fact (XStar.Nonempty ∧ IsGLB (Set.range (fun x ↦ f x + g x)) (FOpt : EReal)) where
  out := ⟨h.optimal_set_nonempty, h.optimal_value_isGLB⟩

/-- A composite mirror-descent problem canonically induces the Chapter 8 bounded-subgradient
owner on `effective_domain g`. -/
def IsCompositeMirrorDescentProblem.subgradientNormBoundOn
    {f g : E → EReal} {XStar : Set E} {FOpt Lf : ℝ}
    (h : IsCompositeMirrorDescentProblem f g XStar FOpt Lf) :
    SubgradientNormBoundOn f (effective_domain g) :=
  { L_f := Lf
    L_f_pos := h.Lf_pos
    norm_le := h.subgradient_norm_le }

/-- A composite mirror-descent problem canonically packages nonemptiness of the optimal set, the
greatest-lower-bound characterization of the optimal value, and positivity of `L_f`. -/
instance instFactCompositeOptimalSetNonemptyOptimalValueIsGLBAndLfPos
    {f g : E → EReal} {XStar : Set E} {FOpt Lf : ℝ}
    [h : IsCompositeMirrorDescentProblem f g XStar FOpt Lf] :
    Fact (XStar.Nonempty ∧ IsGLB (Set.range (fun x ↦ f x + g x)) (FOpt : EReal) ∧ 0 < Lf) where
  out := ⟨h.optimal_set_nonempty, h.optimal_value_isGLB, h.Lf_pos⟩

end

/-! ### Lemma_9_4 (from Chap09) -/
universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {C : Set E} {ω : E → EReal} {σ : ℝ}

/- Lemma 9.4 is `source-facing`: it records the lower quadratic bound, nonnegativity, and
definiteness properties of the Chapter 9 Bregman distance on `C × (C ∩ dom(∂ ω))`. Its owner
abstractions are already upstream: `B[ω]` / `bregmanDistance`, `IsBregmanPotentialOn`,
`subdifferential_domain`, and the strong-convexity support inequality behind clause (1). The
source item is therefore kept as three atomic Bregman lemmas rather than a new wrapper package. -/

-- Proof sketch: apply Theorem 5.24(ii) to the strongly convex real-valued restriction of
-- `ω + extendedIndicator C` given by `hω.strongConvexOn_add_indicator`. For `x ∈ C` and
-- `y ∈ C ∩ dom(∂ ω)`, the indicator terms vanish, `hy_subgrad` identifies the supporting
-- subgradient at `y` with the gradient of the finite-valued restriction of `ω`, and the resulting
-- quadratic lower-support inequality is exactly the displayed Bregman lower bound.
/-- Lemma 9.4 (1): if `ω` is a Bregman potential on `C`, then for every `x ∈ C` and every
`y ∈ C ∩ dom(∂ ω)`, the associated Bregman distance dominates the quadratic term
`(σ / 2) ‖x - y‖²`. -/
theorem bregmanDistance_lower_quadratic_bound
    (hω : IsBregmanPotentialOn ω C σ) (x y : E)
    (hx : x ∈ C) (hyC : y ∈ C) (hy_subgrad : y ∈ subdifferential_domain ω) :
    B[ω] x y ≥ (σ / 2) * ‖x - y‖ ^ (2 : ℕ) := sorry

-- Proof sketch: combine `bregmanDistance_lower_quadratic_bound` with `hω.sigma_pos`, which gives
-- `(σ / 2) * ‖x - y‖² ≥ 0`, and conclude that the Bregman distance is nonnegative.
/-- Lemma 9.4 (2): if `x ∈ C` and `y ∈ C ∩ dom(∂ ω)`, then the Bregman distance
`B_ω(x, y)` is nonnegative. -/
theorem bregmanDistance_nonneg_of_mem_subdifferential_domain
    (hω : IsBregmanPotentialOn ω C σ) (x y : E)
    (hx : x ∈ C) (hyC : y ∈ C) (hy_subgrad : y ∈ subdifferential_domain ω) :
    0 ≤ B[ω] x y := by
  have hnorm_sq_nonneg : 0 ≤ ‖x - y‖ ^ (2 : ℕ) := by
    positivity
  have hquad_nonneg : 0 ≤ (σ / 2) * ‖x - y‖ ^ (2 : ℕ) := by
    nlinarith [hω.sigma_pos, hnorm_sq_nonneg]
  exact hquad_nonneg.trans <| bregmanDistance_lower_quadratic_bound hω x y hx hyC hy_subgrad

-- Proof sketch: if `x = y`, then `bregmanDistance_eq_zero_of_eq` gives the reverse implication.
-- Conversely, `bregmanDistance_nonneg_of_mem_subdifferential_domain` and
-- `bregmanDistance_lower_quadratic_bound` force `‖x - y‖² = 0` when the Bregman distance
-- vanishes, hence `x = y`.
/-- Lemma 9.4 (3): for `x ∈ C` and `y ∈ C ∩ dom(∂ ω)`, the Bregman distance vanishes exactly on
the diagonal. -/
theorem bregmanDistance_eq_zero_iff_eq_of_mem_subdifferential_domain
    (hω : IsBregmanPotentialOn ω C σ) (x y : E)
    (hx : x ∈ C) (hyC : y ∈ C) (hy_subgrad : y ∈ subdifferential_domain ω) :
    B[ω] x y = 0 ↔ x = y := by
  constructor
  · intro hzero
    have hquad_le :
        (σ / 2) * ‖x - y‖ ^ (2 : ℕ) ≤ 0 := by
      rw [← hzero]
      exact bregmanDistance_lower_quadratic_bound hω x y hx hyC hy_subgrad
    have hnorm_sq_nonneg : 0 ≤ ‖x - y‖ ^ (2 : ℕ) := by
      positivity
    have hquad_nonneg : 0 ≤ (σ / 2) * ‖x - y‖ ^ (2 : ℕ) := by
      nlinarith [hω.sigma_pos, hnorm_sq_nonneg]
    have hquad_eq :
        (σ / 2) * ‖x - y‖ ^ (2 : ℕ) = 0 := by
      linarith
    have hsigma_half_pos : 0 < σ / 2 := by
      nlinarith [hω.sigma_pos]
    have hnorm_sq : ‖x - y‖ ^ (2 : ℕ) = 0 := by
      nlinarith
    have hnorm : ‖x - y‖ = 0 := by
      exact eq_zero_of_pow_eq_zero hnorm_sq
    exact sub_eq_zero.mp <| norm_eq_zero.mp hnorm
  · intro hxy
    exact bregmanDistance_eq_zero_of_eq ω hxy

end

/-! ### Text_9_4 (from Chap09) -/
noncomputable section

open InnerProductSpace (toDualMap)
open scoped Gradient

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ω : E → EReal} {C : Set E} {σ : ℝ} {xk xNext gradf : E} {t : ℝ}

/-
Text 9.4 is `source-facing` in the Chapter 9 mirror-descent API. Domain sampling in the relevant
convex-analysis layer points to these existing owners:
- Chapter 9's `IsBregmanPotentialOn ω C σ` for the primitive mirror-map data on `C`;
- Chapter 9's `bregmanDistance` / `B[ω]` for the step objective;
- Chapter 3's owner `subdifferential` / `subdifferential_domain` for the constrained optimality
  condition;
- Chapter 4's Fenchel owner `conjugate_function` together with the conjugate-side bridge used to
  pass from constrained subgradient membership to the gradient of the conjugate.

The right abstraction layer is therefore:
- `source-facing`: the mirror step over `C` and the textbook conclusion
  `x⁺ = ∇ ω̃∗(∇ω(xᵏ) - t g_f)`;
- `core/canonical`: the constrained potential `ω̃ = ω + extendedIndicator C`;
- `bridge/view`: the intermediate constrained-subgradient and conjugate-subdifferential
  formulations.

The primitive data are the Bregman-potential owner `hω : IsBregmanPotentialOn ω C σ` and the
current-point hypothesis `xk ∈ C ∩ dom(∂ ω)`. The constrained potential and conjugate-side
formulations are derived API from those owners; they should not replace the source-facing mirror
step as the main public statement. -/

-- Proof sketch: because `hω.subset_effective_domain` makes `ω` finite on `C`, the objective
-- `x ↦ ⟪t g_f, x⟫ + B[ω] x xk` on `C` agrees, up to an additive constant independent of `x`, with
-- the unconstrained extended-real objective
-- `x ↦ (ω + δ_C)(x) - ⟪∇ω(xk) - t g_f, x⟫`. Fermat's rule for that constrained potential therefore
-- gives the textbook optimality condition
-- `∇ω(xk) - t g_f ∈ ∂ (ω + δ_C) (x⁺)`, expressed on the chapter's continuous-dual bridge
-- `strongDualSubdifferential`.
/-- Text 9.4 bridge: if `ω` is a Bregman potential on `C` and `x^k ∈ C ∩ dom(∂ ω)`, then the
mirror-descent step
`x⁺ ∈ argmin_{x ∈ C} {⟪t g_f, x⟫ + B_ω(x, x^k)}`
is equivalent to the constrained subgradient condition
`∇ω(x^k) - t g_f ∈ ∂ (ω + δ_C)(x⁺)`. -/
lemma mirror_descent_step_isMinOn_iff_dual_mem_subdifferential_add_indicator
    (hω : IsBregmanPotentialOn ω C σ) (hxk : xk ∈ C ∩ subdifferential_domain ω) :
    IsMinOn (fun x ↦ inner ℝ (t • gradf) x + B[ω] x xk) C xNext ↔
      toDualMap ℝ E (∇ (fun y ↦ (ω y).toReal) xk - t • gradf) ∈
        strongDualSubdifferential (ω + extendedIndicator C) xNext :=
  sorry

-- Proof sketch: combine the constrained-subgradient bridge above with Fenchel conjugacy for
-- `ω̃ = ω + δ_C`. Strong convexity of the constrained potential makes `ω̃∗` differentiable at the
-- dual point, so the singleton subdifferential there is represented by the gradient of
-- `y ↦ ((ω̃∗) y).toReal`. Transporting back through the Riesz map identifies the primal vector
-- `x⁺` with that gradient.
/-- Text 9.4: letting `ω̃ = ω + δ_C`, if `ω` is a Bregman potential on `C` and
`x^k ∈ C ∩ dom(∂ ω)`, then the mirror-descent update step
`x⁺ ∈ argmin_{x ∈ C} {⟪t g_f, x⟫ + B_ω(x, x^k)}`
is equivalent to the source-facing conjugate formula
`x⁺ = ∇ ω̃∗(∇ω(x^k) - t g_f)`, expressed in Lean via the real-valued restriction of `ω̃∗`. -/
theorem mirror_descent_step_isMinOn_iff_eq_gradient_conjugate_add_indicator
    (hω : IsBregmanPotentialOn ω C σ) (hxk : xk ∈ C ∩ subdifferential_domain ω) :
    IsMinOn (fun x ↦ inner ℝ (t • gradf) x + B[ω] x xk) C xNext ↔
      xNext =
        ∇ (fun y ↦ ((((ω + extendedIndicator C)∗) y).toReal))
          (∇ (fun y ↦ (ω y).toReal) xk - t • gradf) :=
  sorry

end
