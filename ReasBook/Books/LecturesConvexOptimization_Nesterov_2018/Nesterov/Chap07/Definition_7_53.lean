import Mathlib
import Mathlib.Tactic.Recall
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap06.Definition_6_30

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Definition 7.53 lies in the chapter's barrier-smoothed support-function domain.

Mandatory domain-style sampling before refinement:
- `smoothedPrimalObjective` in `Chap06/Definition_6_30`, the chapter owner of regularized
  supremum constructions of the form `hatf x + sup_u (A x u - hatφ u - μ d₂ u)`;
- `smoothedPrimalObjectiveArgmax` and `mem_smoothedPrimalObjectiveArgmax_iff` in
  `Chap06/Definition_6_30`, the canonical argmax owner and its feasibility/maximality bridge;
- mathlib `IsMaxOn`, the primitive maximality predicate used by the owner bridge.

Best owner abstraction:
- source-facing: Definition 7.53's smooth support-function approximation `Uβ` together with its
  maximizer owner `Argmaxβ`, representing
  `U_β(s) = max_{u ∈ hatP} {⟨s, u - x₀⟩ - β (F(u) - F(x₀))}`;
- core/canonical: `smoothedPrimalObjective` and `smoothedPrimalObjectiveArgmax`, specialized to
  the identity dual map on `StrongDual ℝ E`, zero dual penalty, and prox term `F`;
- bridge/view: the expansion theorems below, which rewrite `Uβ` and `Argmaxβ` back to the
  textbook support-function formula and maximizer condition.

Primitive data:
- the feasible set `hatP`, barrier term `F`, base point `x₀`, smoothing parameter `β`, and the
  dual variable `s`.

Derived API:
- the value function owner `Uβ`, via the Chapter 6 owner `smoothedPrimalObjective`;
- the maximizer owner `Argmaxβ`, via `smoothedPrimalObjectiveArgmax`;
- the textbook support-function formula and feasible-maximizer characterization, via thin
  companion theorems.

The previous version introduced a second public owner
`SmoothSupportFunctionApproximationSetup` together with exact duplicate-wheel wrappers for the
maximand, value function, and argmax set. Those notions are already owned by
`smoothedPrimalObjective` and `smoothedPrimalObjectiveArgmax`. This file therefore refines
Definition 7.53 to a thin source-facing owner layer `Uβ` / `Argmaxβ` on top of the Chapter 6
owners, keeping only the textbook formula and argmax bridges as derived API.
-/

section

variable (hatP : Set E) (F : E → ℝ) (x0 : E) (β : {β : ℝ // 0 < β})
variable (s : StrongDual ℝ E) (u : E)

/- Definition 7.53's smoothed support-function approximation `Uβ` is the Chapter 6 regularized-max
owner specialized to the identity dual map, the feasible set `hatP`, zero dual penalty, prox term
`F`, and affine base term `s ↦ -s x₀ + β F(x₀)`. Its maximizer layer `Argmaxβ` is the
corresponding canonical argmax owner. -/
recall smoothedPrimalObjective
recall smoothedPrimalObjective_apply
recall smoothedPrimalObjectiveArgmax
recall mem_smoothedPrimalObjectiveArgmax_iff

/-- Definition 7.53: the positive barrier-smoothed support-function approximation `U_β`. -/
abbrev Uβ (hatP : Set E) (F : E → ℝ) (x0 : E) (β : {β : ℝ // 0 < β}) :
    StrongDual ℝ E → ℝ :=
  smoothedPrimalObjective
    (ContinuousLinearMap.id ℝ (StrongDual ℝ E))
    hatP
    (fun t : StrongDual ℝ E ↦ -t x0 + (β : ℝ) * F x0)
    0
    F
    (β : ℝ)

-- Proof sketch: unfold `Uβ`; the result is the defining Chapter 6 specialization of the whole
-- owner.
/-- Expanding `Uβ` recovers its Chapter 6 owner specialization. -/
@[simp] theorem Uβ_def
    (hatP : Set E) (F : E → ℝ) (x0 : E) (β : {β : ℝ // 0 < β}) :
    Uβ hatP F x0 β =
      smoothedPrimalObjective
        (ContinuousLinearMap.id ℝ (StrongDual ℝ E))
        hatP
        (fun t : StrongDual ℝ E ↦ -t x0 + (β : ℝ) * F x0)
        0
        F
        (β : ℝ) := sorry

-- Proof sketch: unfold `Uβ`, then expand `smoothedPrimalObjective_apply` and simplify the
-- specialized Chapter 6 maximand.
/-- Evaluating `Uβ` gives the textbook affine-term plus supremum formula. -/
@[simp] theorem Uβ_apply
    (hatP : Set E) (F : E → ℝ) (x0 : E) (β : {β : ℝ // 0 < β}) (s : StrongDual ℝ E) :
    Uβ hatP F x0 β s =
      -s x0 + β * F x0 +
        sSup ((fun u : E ↦ s u - β * F u) '' hatP) := sorry

-- Proof sketch: combine `Uβ_apply` with linearity of `s` to absorb the additive constant
-- `-s x₀ + β * F x₀` into the textbook payoff `u ↦ s (u - x₀) - β (F u - F x₀)`.
/-- Evaluating `Uβ` is the supremum of the textbook support-function payoff
`u ↦ s (u - x₀) - β (F u - F x₀)` over `hatP`. -/
theorem Uβ_textbook_formula
    (hatP : Set E) (F : E → ℝ) (x0 : E) (β : {β : ℝ // 0 < β}) (s : StrongDual ℝ E) :
    Uβ hatP F x0 β s =
      sSup ((fun u : E ↦ s (u - x0) - β * (F u - F x0)) '' hatP) := sorry

/-- The canonical feasible-maximizer owner for the support-function approximation `U_β`. The
base-point shift does not appear because it contributes only an additive constant in `u`. -/
abbrev Argmaxβ (hatP : Set E) (F : E → ℝ) (β : {β : ℝ // 0 < β}) :
    StrongDual ℝ E → Set E :=
  smoothedPrimalObjectiveArgmax
    (ContinuousLinearMap.id ℝ (StrongDual ℝ E))
    hatP
    0
    F
    (β : ℝ)

set_option linter.hashCommand false in
#check
  Uβ hatP F x0 β s

set_option linter.hashCommand false in
#check
  Argmaxβ hatP F β s

set_option linter.hashCommand false in
#check
  u ∈ Argmaxβ hatP F β s

end

-- Proof sketch: expand `Argmaxβ` with `mem_smoothedPrimalObjectiveArgmax_iff`, then rewrite the
-- maximand by separating the additive constant `-s x₀ + β * F x₀`, which does not affect `IsMaxOn`.
/-- Membership in the source-facing argmax owner `Argmaxβ` is exactly feasibility in `hatP`
together with maximality for the textbook payoff `u ↦ s (u - x₀) - β (F u - F x₀)`. -/
@[simp] theorem mem_Argmaxβ_iff
    {hatP : Set E} {F : E → ℝ} {x0 : E} {β : {β : ℝ // 0 < β}}
    {s : StrongDual ℝ E} {u : E} :
    u ∈ Argmaxβ hatP F β s ↔
      u ∈ hatP ∧
        IsMaxOn
          (fun v : E ↦ s (v - x0) - β * (F v - F x0))
          hatP
          u := sorry

end
