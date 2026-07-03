import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Assumption_6_2_1 (from Chap06) -/
noncomputable section

universe u

/- Assumption 6.2.1 lies in the chapter's fixed-parameter strong-convexity domain for the primal
smooth term.

Sampled owner-style declarations:
- project `S0On` with notation `𝒮^0_μ(Q)` in `Chap03/Definition_3_47`, the chapter's
  source-facing owner for positive-parameter strong convexity on a feasible set;
- project `mem_S0On_iff`, the source-facing specification theorem for that owner;
- project `StrongConvexOnClass.strongConvexOn`, the canonical projection from that owner to
  `StrongConvexOn`;
- mathlib `StrongConvexOn`, the ambient-norm core predicate reused throughout later chapters.

Best owner abstraction:
- source-facing: `hatf ∈ 𝒮^0_hatσ(Q₁)`;
- core/canonical: `StrongConvexOn Q₁ hatσ hatf`;
- bridge/view: `mem_S0On_iff`, which expands the source-facing owner to
  `0 < hatσ ∧ StrongConvexOn Q₁ hatσ hatf`.

Primitive data:
- the feasible set `Q₁`, the smooth part `hatf`, and the fixed modulus `hatσ`.

Derived API:
- positivity of the modulus `hatσ` via `StrongConvexOnClass.mu_pos`;
- the canonical core view `StrongConvexOn Q₁ hatσ hatf` via
  `StrongConvexOnClass.strongConvexOn`;
- the lower Chapter 2 `StrongConvexOnWith (normSeminorm ℝ E) ...` vocabulary only through the
  existing bridge already subsumed by the Chapter 3 owner.

Source/core/bridge triage:
- source-facing main entry: `hatf ∈ 𝒮^0_hatσ(Q₁)`;
- core/canonical companion: `StrongConvexOn Q₁ hatσ hatf`;
- bridge/view companion: `mem_S0On_iff`.

This numbered assumption adds no new mathematics beyond the chapter owner already introduced in
Definition 3.47, so this file now recalls that owner directly instead of centering the lower
ambient `StrongConvexOnWith (normSeminorm ...)` bridge.
-/

section

open scoped StrongConvex

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (Q₁ : Set E) (hatf : E → ℝ) (hatσ : ℝ)

/- Assumption 6.2.1 uses the chapter's source-facing fixed-parameter strong-convexity owner. -/
#check (hatf ∈ 𝒮^0_hatσ(Q₁))

/- The source-facing owner exposes the textbook form
`0 < hatσ ∧ StrongConvexOn Q₁ hatσ hatf`. -/
recall mem_S0On_iff

/- Membership in the chapter owner forces positivity of the fixed modulus. -/
recall StrongConvexOnClass.mu_pos

/- Membership in the chapter owner projects to the canonical core predicate `StrongConvexOn`. -/
recall StrongConvexOnClass.strongConvexOn

end

end

/-! ### Corollary_6_2_1 (from Chap06) -/
section

universe u

variable {𝕜 : Type u} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

-- Proof sketch: rewrite `1 - τ k` as `α ((k : ℤ) + 1) / α ((k : ℤ) - 1)` and clear this
-- positive denominator to reduce to Theorem 6.5.
/-- Corollary 6.2.1: for a fixed index `k`, if
`λ₁,k λ₂,k = α_k α_{k-1}` and `τ_k = 1 - α_{k+1} / α_{k-1}` with
`α_{k-1}, α_{k+1} > 0`, then the step-size condition
`τ_k^2 / (1 - τ_k) ≤ λ_{1,k} λ_{2,k}` is equivalent to
`(α_{k+1} - α_{k-1})^2 ≤ α_{k+1} α_k α_{k-1}^2`. -/
theorem step_size_condition_iff_alpha_three_term_inequality
    (α : Set.Ici (-1 : ℤ) → 𝕜) (lambda₁ lambda₂ τ : ℕ → 𝕜) (k : ℕ)
    (hα_pred_pos : 0 < α (switching_parameters_pred_index k))
    (hα_succ_pos : 0 < α (switching_parameters_succ_index k))
    (hprod : lambda₁ k * lambda₂ k =
      α (switching_parameters_curr_index k) * α (switching_parameters_pred_index k))
    (hτ : τ k = 1 - α (switching_parameters_succ_index k) / α (switching_parameters_pred_index k)) :
    τ k ^ (2 : ℕ) / (1 - τ k) ≤ lambda₁ k * lambda₂ k ↔
      (α (switching_parameters_succ_index k) - α (switching_parameters_pred_index k)) ^ (2 : ℕ) ≤
        α (switching_parameters_succ_index k) * α (switching_parameters_curr_index k) *
          (α (switching_parameters_pred_index k)) ^ (2 : ℕ) := sorry

end

/-! ### Lemma_6_2_1 (from Chap06) -/
universe u v

section

variable {X : Type u} {U : Type v}

/-- The raw duality gap at an excessive-gap pair is bounded by the smoothing budget
`μ₁ D₁ + μ₂ D₂`. -/
-- Proof sketch: combine the pointwise smoothing bounds at `xBar` and `uBar` with
-- `fμ₂ xBar ≤ φμ₁ uBar` to get
-- `f xBar - μ₂ * D₂ ≤ fμ₂ xBar ≤ φμ₁ uBar ≤ φ uBar + μ₁ * D₁`, then rearrange.
theorem raw_duality_gap_le_excessive_gap_budget
    {Q₁ : Set X} {Q₂ : Set U}
    {f fμ₂ : X → ℝ} {φ φμ₁ : U → ℝ}
    {xBar : Q₁} {uBar : Q₂}
    {D₁ D₂ μ₁ μ₂ : ℝ}
    (hfμ₂_lower : f xBar - μ₂ * D₂ ≤ fμ₂ xBar)
    (hφμ₁_upper : φμ₁ uBar ≤ φ uBar + μ₁ * D₁)
    (hexcessive_gap : satisfiesExcessiveGapCondition Q₁ Q₂ fμ₂ φμ₁ xBar uBar) :
    f xBar - φ uBar ≤ μ₁ * D₁ + μ₂ * D₂ := by
  have hgap : f xBar - μ₂ * D₂ ≤ φ uBar + μ₁ * D₁ :=
    (hfμ₂_lower.trans hexcessive_gap).trans hφμ₁_upper
  linarith

/-- Lemma 6.2.1 (1): the primal error at an excessive-gap pair is nonnegative. -/
-- Proof sketch: `h_primal` states that `fStar` is the minimum value of `f` on `Q₁`; apply it to
-- `xBar ∈ Q₁` to get `fStar ≤ f xBar`, then rearrange.
theorem excessive_gap_condition_primal_error_nonneg {Q₁ : Set X} {f : X → ℝ} {xBar : X}
    {fStar : ℝ} (h_primal : IsLeast (f '' Q₁) fStar) (hxBar : xBar ∈ Q₁) :
    0 ≤ f xBar - fStar := by
  exact sub_nonneg.mpr (h_primal.2 (Set.mem_image_of_mem f hxBar))

/-- Lemma 6.2.1 (2): the primal error at an excessive-gap pair is bounded above by the raw duality
gap. -/
-- Proof sketch: `h_dual` gives `φ uBar ≤ fStar`, so subtracting this inequality from `f xBar`
-- yields `f xBar - fStar ≤ f xBar - φ uBar`.
theorem excessive_gap_condition_primal_error_le_raw_gap {Q₂ : Set U} {f : X → ℝ}
    {φ : U → ℝ} {xBar : X} {uBar : U} {fStar : ℝ}
    (h_dual : IsGreatest (φ '' Q₂) fStar) (huBar : uBar ∈ Q₂) :
    f xBar - fStar ≤ f xBar - φ uBar := by
  exact sub_le_sub_left (h_dual.2 (Set.mem_image_of_mem φ huBar)) (f xBar)

/-- Lemma 6.2.1 (3): the dual error at an excessive-gap pair is nonnegative. -/
-- Proof sketch: `h_dual` states that `fStar` is the maximum value of `φ` on `Q₂`; apply it to
-- `uBar ∈ Q₂` to get `φ uBar ≤ fStar`, then rearrange.
theorem excessive_gap_condition_dual_error_nonneg {Q₂ : Set U} {φ : U → ℝ} {uBar : U}
    {fStar : ℝ}
    (h_dual : IsGreatest (φ '' Q₂) fStar) (huBar : uBar ∈ Q₂) :
    0 ≤ fStar - φ uBar := by
  exact sub_nonneg.mpr (h_dual.2 (Set.mem_image_of_mem φ huBar))

/-- Lemma 6.2.1 (4): the dual error at an excessive-gap pair is bounded above by the raw duality
gap. -/
-- Proof sketch: `h_primal` gives `fStar ≤ f xBar`, so subtracting `φ uBar` from this inequality
-- yields `fStar - φ uBar ≤ f xBar - φ uBar`.
theorem excessive_gap_condition_dual_error_le_raw_gap {Q₁ : Set X} {f : X → ℝ}
    {φ : U → ℝ} {xBar : X} {uBar : U} {fStar : ℝ}
    (h_primal : IsLeast (f '' Q₁) fStar) (hxBar : xBar ∈ Q₁) :
    fStar - φ uBar ≤ f xBar - φ uBar := by
  exact sub_le_sub_right (h_primal.2 (Set.mem_image_of_mem f hxBar)) (φ uBar)

end

/-! ### Text_6_2_1_Fixed_Horizon_Drawback_and_Excessive_Gap_Motivation (from Chap06) -/
/- Text 6.2.1 lies in the chapter's excessive-gap stopping-criterion domain.

Sampled owner-style declarations:
- `satisfiesExcessiveGapCondition` in `Chap06/Definition_6_34`, the source-facing owner for the
  chapter's excessive-gap certificate;
- `satisfiesExcessiveGapCondition_preserved_under_update` in `Chap06/Theorem_6_4`, the Chapter 6
  update theorem stated directly in terms of that same source-facing owner;
- `raw_duality_gap_le_excessive_gap_budget` in `Chap06/Lemma_6_2_1`, the chapter bridge from an
  excessive-gap certificate to a raw duality-gap budget bound.

Best owner abstraction:
- the chapter's excessive-gap certificate, not a generic scalar gap sequence.

Primitive data:
- the source-facing excessive-gap certificate `satisfiesExcessiveGapCondition Q₁ Q₂ fμ₂ φμ₁`;
- the local one-sided smoothing bounds `f xBar - μ₂ * D₂ ≤ fμ₂ xBar` and
  `φμ₁ uBar ≤ φ uBar + μ₁ * D₁`;
- the stopping inequality `μ₁ D₁ + μ₂ D₂ ≤ ε`.

Derived API:
- the stopping conclusion `f(xBar) - φ(uBar) ≤ ε`.

Source/core/bridge triage:
- source-facing: the chapter's excessive-gap certificate at the current primal-dual pair together
  with the stopping test on the smoothing budget;
- core/canonical: the chapter owner `satisfiesExcessiveGapCondition`;
- bridge/view: the raw duality-gap estimate obtained by combining the certificate with the
  smoothing bounds.
-/

universe u v

section

variable {X : Type u} {U : Type v}

-- Proof sketch: the excessive-gap certificate is exactly `fμ₂ xBar ≤ φμ₁ uBar`. Combine this
-- with the local smoothing bounds at `xBar` and `uBar` to obtain
-- `f xBar - φ uBar ≤ μ₁ D₁ + μ₂ D₂`, then use the stopping inequality
-- `μ₁ D₁ + μ₂ D₂ ≤ ε`.
/-- Text 6.2.1-Fixed-Horizon Drawback and Excessive-Gap Motivation: once a feasible pair
`(xBar, uBar)` satisfies the chapter's excessive-gap certificate and the current smoothing budget
obeys `μ₁ D₁ + μ₂ D₂ ≤ ε`, the raw duality gap is already `ε`-small. This source-facing stopping
criterion uses only the two smoothing inequalities at the current pair `(xBar, uBar)`, not global
smoothing bounds on all of `Q₁` and `Q₂`, so one can stop as soon as the current certificate
budget falls below `ε` instead of fixing a horizon in advance. -/
theorem raw_duality_gap_le_epsilon_of_satisfiesExcessiveGapCondition
    {Q₁ : Set X} {Q₂ : Set U}
    {f fμ₂ : X → ℝ} {φ φμ₁ : U → ℝ}
    {xBar : Q₁} {uBar : Q₂}
    {D₁ D₂ μ₁ μ₂ ε : ℝ}
    (hfμ₂_lower : f xBar - μ₂ * D₂ ≤ fμ₂ xBar)
    (hφμ₁_upper : φμ₁ uBar ≤ φ uBar + μ₁ * D₁)
    (hexcessive_gap : satisfiesExcessiveGapCondition Q₁ Q₂ fμ₂ φμ₁ xBar uBar)
    (hbudget : μ₁ * D₁ + μ₂ * D₂ ≤ ε) :
    f xBar - φ uBar ≤ ε := sorry

end

/-! ### Text_6_2_1_Implementability_Assumptions_for_Primal_Dual_Structure (from Chap06) -/
noncomputable section

open scoped ConstrainedArgmin Gradient

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

/- Text 6.2.1 lies in the chapter's structured primal-dual implementability domain.

Mandatory domain-style sampling before refinement:
- `StructuredObjectiveModel` in `Chap06/Definition_6_6`, the chapter owner for the ambient
  primal-dual data `Q₁`, `Q₂`, `\hat f`, `\hat φ`, `A`, and their bounded/closed/convex/
  continuous structure;
- `proximalMinimizationProblem` in `Chap06/Definition_6_26`, the canonical owner for the primal
  prox subproblem on `Q₁`;
- `smoothedPrimalObjectiveArgmax` in `Chap06/Definition_6_30`, the canonical owner for the
  regularized dual-oracle argmax set on `Q₂`;
- `η` in `Chap06/Proposition_6_23`, the chapter's positive-smoothing owner pattern
  `μ : {μ : ℝ // 0 < μ}` for a source-facing smoothing object.

Best owner abstraction:
- source-facing: `ImplementablePrimalDualStructure`;
- core/canonical: `StructuredObjectiveModel`, together with `proximalMinimizationProblem`,
  `smoothedPrimalObjectiveArgmax`, the positive smoothing-parameter subtype
  `{μ : ℝ // 0 < μ}`, `HasGradientWithinAt`, and `LipschitzOnWith`;
- bridge/view: the coercion to the primal prox solver, the raw `IsMinOn` / `IsMaxOn` companion
  lemmas, and the derived nonemptiness of `Q₁` and `Q₂` coming from the solver data.

Primitive data:
- the inherited structured-objective data from `StructuredObjectiveModel`;
- the prox terms `d₁`, `d₂`;
- a closed-form primal prox solver and a closed-form regularized dual oracle on the positive
  smoothing surface `μ : {μ : ℝ // 0 < μ}`;
- the within-gradient existence and Lipschitz constants for `hatf` on `Q₁` and `hatφ` on `Q₂`.

Derived API:
- the primal solver specification as membership in the canonical argmin set of
  `proximalMinimizationProblem`;
- the dual-oracle specification as membership in the canonical argmax set
  `smoothedPrimalObjectiveArgmax`;
- the inherited bounded/closed/convex/continuous structure from `StructuredObjectiveModel`;
- the raw minimizer and maximizer views and the induced nonemptiness of the feasible sets.

The previous version stored the ambient primal-dual data as loose parameters and thereby rebuilt a
parallel owner that dropped the inherited bounded/closed/convex/continuous structure already owned
by `StructuredObjectiveModel`. It also stored the tractability clauses as raw `IsMinOn` /
`IsMaxOn` formulas, duplicating the chapter owners already introduced for those subproblems, and
it made the dual oracle total at `μ = 0`. This refinement keeps the source-facing implementability
structure, but expresses it as additional data on top of the chapter owner `StructuredObjectiveModel`,
rewrites the solver API to the canonical owner declarations, and restricts the dual oracle to the
positive smoothing surface used elsewhere in Chapter 6.
-/

/-- Text 6.2.1-Implementability Assumptions for Primal-Dual Structure: an implementable
primal-dual representation provides closed-form solution operators for the primal proximal
subproblem on `Q₁` and, for each positive smoothing parameter `μ > 0`, the regularized dual
oracle subproblem on `Q₂`, and the functions `\hat f` and `\hat φ` have gradients that are
Lipschitz continuous on `Q₁` and `Q₂` with constants `L₁(\hat f)` and `L₂(\hat φ)`. -/
structure ImplementablePrimalDualStructure (E₁ : Type u) (E₂ : Type v)
    [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]
    extends StructuredObjectiveModel E₁ E₂ where
  /-- The primal prox term `d₁`. -/
  primalProxFunction : E₁ → ℝ
  /-- The dual prox term `d₂`. -/
  dualProxFunction : E₂ → ℝ
  /-- The closed-form primal proximal solver `s ↦ x(s)`. -/
  primalProxSolver : StrongDual ℝ E₁ → primalSet
  /-- The primal proximal solver belongs to the canonical argmin set of the proximal subproblem
  on the inherited primal set. -/
  primalProxSolver_spec :
    ∀ s : StrongDual ℝ E₁,
      primalProxSolver s ∈
        argmin[Set.univ]
          (proximalMinimizationProblem primalSet (fun x : primalSet ↦ primalProxFunction x) s)
  /-- The closed-form dual oracle `u_μ(x)` returns a feasible maximizer of the regularized dual
  subproblem on the inherited dual set for each positive smoothing parameter `μ`. -/
  dualOracleSolver : primalSet → {μ : ℝ // 0 < μ} → dualSet
  /-- The dual oracle belongs to the canonical argmax set of the regularized dual maximand on
  the inherited dual set. -/
  dualOracleSolver_spec :
    ∀ (x : primalSet) (μ : {μ : ℝ // 0 < μ}),
      (dualOracleSolver x μ : E₂) ∈
        smoothedPrimalObjectiveArgmax linearMap dualSet dualPenalty dualProxFunction μ x
  /-- The Lipschitz constant `L₁(\hat f)` for the gradient of `\hat f` on `Q₁`. -/
  smoothPartGradientLipschitzConstant : NNReal
  /-- The gradient of `\hat f` exists on `Q₁` as the canonical within-gradient. -/
  smoothPart_hasGradientWithinAt :
    ∀ ⦃x : E₁⦄, x ∈ primalSet →
      HasGradientWithinAt smoothPart (gradientWithin smoothPart primalSet x) primalSet x
  /-- The gradient of `\hat f` is Lipschitz on `Q₁` with constant `L₁(\hat f)`. -/
  smoothPart_gradient_lipschitz :
    LipschitzOnWith smoothPartGradientLipschitzConstant
      (gradientWithin smoothPart primalSet) primalSet
  /-- The Lipschitz constant `L₂(\hat φ)` for the gradient of `\hat φ` on `Q₂`. -/
  dualPenaltyGradientLipschitzConstant : NNReal
  /-- The gradient of `\hat φ` exists on `Q₂` as the canonical within-gradient. -/
  dualPenalty_hasGradientWithinAt :
    ∀ ⦃u : E₂⦄, u ∈ dualSet →
      HasGradientWithinAt dualPenalty (gradientWithin dualPenalty dualSet u) dualSet u
  /-- The gradient of `\hat φ` is Lipschitz on `Q₂` with constant `L₂(\hat φ)`. -/
  dualPenalty_gradient_lipschitz :
    LipschitzOnWith dualPenaltyGradientLipschitzConstant
      (gradientWithin dualPenalty dualSet) dualSet

namespace ImplementablePrimalDualStructure

/-- An implementable primal-dual structure can be evaluated as its closed-form primal proximal
solver `s ↦ x(s)` on the inherited primal set. -/
instance : CoeFun (ImplementablePrimalDualStructure E₁ E₂)
    (fun problem ↦ StrongDual ℝ E₁ → problem.primalSet) where
  coe problem := problem.primalProxSolver

@[simp] theorem coe_apply
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (s : StrongDual ℝ E₁) :
    problem s = problem.primalProxSolver s :=
  rfl

theorem primalSet_nonempty
    (problem : ImplementablePrimalDualStructure E₁ E₂) :
    problem.primalSet.Nonempty :=
  ⟨problem.primalProxSolver 0, (problem.primalProxSolver 0).property⟩

theorem dualSet_nonempty
    (problem : ImplementablePrimalDualStructure E₁ E₂) :
    problem.dualSet.Nonempty := by
  let μ : {μ : ℝ // 0 < μ} := ⟨1, by positivity⟩
  exact
    ⟨problem.dualOracleSolver (problem.primalProxSolver 0) μ,
      (problem.dualOracleSolver (problem.primalProxSolver 0) μ).property⟩

theorem primalProxSolver_isMinOn
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (s : StrongDual ℝ E₁) :
    IsMinOn
      (proximalMinimizationProblem problem.primalSet
        (fun x : problem.primalSet ↦ problem.primalProxFunction x) s)
      Set.univ (problem.primalProxSolver s) := by
  exact (mem_constrainedArgmin_iff.mp (problem.primalProxSolver_spec s)).2

theorem dualOracleSolver_isMaxOn
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (x : problem.primalSet) (μ : {μ : ℝ // 0 < μ}) :
    IsMaxOn
      (smoothedPrimalObjectiveMaximand problem.linearMap problem.dualPenalty
        problem.dualProxFunction μ x)
      problem.dualSet
      (problem.dualOracleSolver x μ) := by
  exact
    (mem_smoothedPrimalObjectiveArgmax_iff problem.linearMap problem.dualSet
      problem.dualPenalty problem.dualProxFunction μ x
      (problem.dualOracleSolver x μ)).mp (problem.dualOracleSolver_spec x μ) |>.2

end ImplementablePrimalDualStructure

end

/-! ### Theorem_6_2_1 (from Chap06) -/
/- Theorem 6.2.1 is exactly the Chapter 6 one-step excessive-gap preservation theorem already
owned by `satisfiesExcessiveGapCondition_preserved_under_update`. -/
recall satisfiesExcessiveGapCondition_preserved_under_update

/-! ### Definition_6_2 (from Chap06) -/
noncomputable section

open Module
open LinearMap (BilinForm)
open LinearMap.BilinForm
open scoped ConvexAnalysis BInducedNorm

universe u

/- Definition 6.2 lies in the chapter's Fenchel-smoothing / extended-real convex-analysis domain.

Sampled owner-style declarations:
- `fenchelConjugate` in `Chap06/Definition_6_1`, the chapter owner for Fenchel suprema in `EReal`
- `dom` in `Chap03/Definition_3_1_1_2`, the project owner for the effective domain of an
  extended-real-valued function
- `LinearMap.BilinForm.dualNorm` in `Chap04/Definition_4_3_4`, the Chapter 4 finite-dimensional
  owner for bilinear-form-induced support-function norms on `Module.Dual ℝ E`
- `IsMaxOn` in mathlib, the canonical attained-maximum owner used to recover textbook `max`
  formulas from supremum owners

Best owner abstraction:
- source-facing: `fenchelSmoothApproximation`
- core/canonical: `fenchelConjugate f`, `dom (fenchelConjugate f)`, and
  `LinearMap.BilinForm.dualNorm`
- bridge/view: the attained-maximum companions
  `fenchelSmoothApproximation_eq_maximand_of_isMaxOn` and
  `fenchelSmoothApproximation_toReal_eq_of_isMaxOn`

Primitive data:
- `B : BilinForm ℝ E`
- `[Fact B.toQuadraticMap.PosDef]`
- `f : E → EReal`
- `μ : NNReal`

Derived API:
- `fenchelSmoothApproximationMaximand`
- `fenchelSmoothApproximation_apply`
- `fenchelSmoothApproximation_toReal_eq_of_isMaxOn`

Source/core/bridge triage:
- source-facing: `fenchelSmoothApproximation`
- core/canonical: `dom`, `fenchelConjugate`, `LinearMap.BilinForm.dualNorm`
- bridge/view: the attained-maximum theorems turning the `EReal` supremum owner back into the
  textbook real-valued maximization formula when a maximizer exists

The source-facing object is the smoothing attached to a primal function through its Fenchel
conjugate. The previous raw-`fStar` surface promoted that derived dual function to a second public
owner. This refinement keeps `fenchelConjugate f` as the canonical dual input and defines the
smoothing directly from `f`. The owner remains `EReal`-valued so empty or unbounded dual fibers
retain their correct order-theoretic value, while the companion attained-maximum theorems recover
the textbook `f_μ : E → ℝ` / `max` formula on the finite-value regime.
-/

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

/-- The quadratically regularized affine functional used in the LecturesConvexOptimization_Nesterov_2018 smoothing formula,
built from the Fenchel conjugate of `f` and regularized by the Chapter 4 dual-norm owner
`‖s‖[B,*]`. -/
def fenchelSmoothApproximationMaximand
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (f : E → EReal) (μ : NNReal)
    (x : E) (s : Dual ℝ E) : EReal :=
  (s x : EReal) - fenchelConjugate f s - (((μ : ℝ) / 2) * ‖s‖[B,*] ^ 2 : ℝ)

/-- On `dom (fenchelConjugate f)`, the regularized maximand is the coercion of the corresponding
real-valued textbook expression. -/
theorem fenchelSmoothApproximationMaximand_eq_coe
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (f : E → EReal) (μ : NNReal) (x : E) {s : Dual ℝ E}
    (hs : s ∈ dom (fenchelConjugate f)) :
    fenchelSmoothApproximationMaximand B f μ x s =
      (((s x : ℝ) - (fenchelConjugate f s).toReal - ((μ : ℝ) / 2) * ‖s‖[B,*] ^ 2 : ℝ) : EReal) := by
  rw [fenchelSmoothApproximationMaximand]
  rw [show fenchelConjugate f s = ((fenchelConjugate f s).toReal : EReal) by
    exact (EReal.coe_toReal hs.1 hs.2).symm]
  norm_num

/-- Definition 6.2: the smooth approximation `f_μ` attached to `f` is the supremum over
`dom (fenchelConjugate f)` of the affine functional
`s ↦ ⟪s, x⟫ - (fenchelConjugate f) s`, regularized by
`(μ / 2) * ‖s‖[B,*]^2` for a nonnegative smoothing parameter `μ`. The owner lives in `EReal`, so
empty or unbounded supremum sets retain their correct extended-real values; the companion theorem
`fenchelSmoothApproximation_toReal_eq_of_isMaxOn` recovers the textbook real-valued maximum
whenever the supremum is attained on `dom (fenchelConjugate f)`. -/
def fenchelSmoothApproximation
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (f : E → EReal) (μ : NNReal) : E → EReal :=
  fun x ↦
    sSup (fenchelSmoothApproximationMaximand B f μ x '' dom (fenchelConjugate f))

-- Proof sketch: unfold `fenchelSmoothApproximation`; the right-hand side is exactly the defining
-- supremum formula over `dom (fenchelConjugate f)`.
/-- Evaluating the smooth approximation recovers the defining regularized supremum over
`dom (fenchelConjugate f)`. -/
@[simp] theorem fenchelSmoothApproximation_apply
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (f : E → EReal) (μ : NNReal) (x : E) :
    fenchelSmoothApproximation B f μ x =
      sSup (fenchelSmoothApproximationMaximand B f μ x '' dom (fenchelConjugate f)) :=
  rfl

private theorem fenchelSmoothApproximationMaximand_isGreatest
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (f : E → EReal) (μ : NNReal) (x : E) {s : Dual ℝ E}
    (hs : s ∈ dom (fenchelConjugate f))
    (hmax : IsMaxOn (fenchelSmoothApproximationMaximand B f μ x) (dom (fenchelConjugate f)) s) :
    IsGreatest
      (fenchelSmoothApproximationMaximand B f μ x '' dom (fenchelConjugate f))
      (fenchelSmoothApproximationMaximand B f μ x s) := by
  refine ⟨⟨s, hs, rfl⟩, ?_⟩
  intro y hy
  rcases hy with ⟨t, ht, rfl⟩
  exact (isMaxOn_iff.mp hmax) t ht

/-- If the dual supremum is attained at `s`, then the smooth approximation equals that attained
maximand value. -/
theorem fenchelSmoothApproximation_eq_maximand_of_isMaxOn
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (f : E → EReal) (μ : NNReal) (x : E) {s : Dual ℝ E}
    (hs : s ∈ dom (fenchelConjugate f))
    (hmax : IsMaxOn (fenchelSmoothApproximationMaximand B f μ x) (dom (fenchelConjugate f)) s) :
    fenchelSmoothApproximation B f μ x =
      fenchelSmoothApproximationMaximand B f μ x s := by
  rw [fenchelSmoothApproximation_apply]
  rw [(fenchelSmoothApproximationMaximand_isGreatest B f μ x hs hmax).csSup_eq]

/-- Under the textbook attained-maximum hypothesis, `f_μ(x)` is the displayed real-valued
maximum `⟪s, x⟫ - f^*(s) - (μ / 2) ‖s‖[B,*]^2`. -/
theorem fenchelSmoothApproximation_eq_coe_of_isMaxOn
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (f : E → EReal) (μ : NNReal) (x : E) {s : Dual ℝ E}
    (hs : s ∈ dom (fenchelConjugate f))
    (hmax : IsMaxOn (fenchelSmoothApproximationMaximand B f μ x) (dom (fenchelConjugate f)) s) :
    fenchelSmoothApproximation B f μ x =
      (((s x : ℝ) - (fenchelConjugate f s).toReal - ((μ : ℝ) / 2) * ‖s‖[B,*] ^ 2 : ℝ) : EReal) := by
  rw [fenchelSmoothApproximation_eq_maximand_of_isMaxOn B f μ x hs hmax]
  rw [fenchelSmoothApproximationMaximand_eq_coe B f μ x hs]

/-- Under the textbook attained-maximum hypothesis, the `EReal` owner recovers the stated
real-valued formula for `f_μ(x)`. -/
theorem fenchelSmoothApproximation_toReal_eq_of_isMaxOn
    (B : BilinForm ℝ E) [Fact B.toQuadraticMap.PosDef]
    (f : E → EReal) (μ : NNReal) (x : E) {s : Dual ℝ E}
    (hs : s ∈ dom (fenchelConjugate f))
    (hmax : IsMaxOn (fenchelSmoothApproximationMaximand B f μ x) (dom (fenchelConjugate f)) s) :
    (fenchelSmoothApproximation B f μ x).toReal =
      (s x : ℝ) - (fenchelConjugate f s).toReal - ((μ : ℝ) / 2) * ‖s‖[B,*] ^ 2 := by
  simpa using
    congrArg EReal.toReal (fenchelSmoothApproximation_eq_coe_of_isMaxOn B f μ x hs hmax)

/-! ### Lemma_6_2 (from Chap06) -/
/-
Lemma 6.2 lies in the chapter's prox-function smoothing / first-order smoothness domain.

Sampled owner-style declarations:
- `smoothedPrimalObjective` in `Definition_6_30`, the chapter's canonical regularized-max
  smoothing owner, specialized in `Theorem_6_1` to zero smooth part;
- `ContinuousLinearMap.flip` in `Proposition_6_3`, the chapter's canonical transpose owner for
  `A : E₁ →L[ℝ] StrongDual ℝ E₂`;
- `smoothedObjective_hasFDerivAt` in `Theorem_6_1`, the canonical derivative identification for
  the smoothed objective;
- `smoothedObjective_gradient_lipschitz` in `Theorem_6_1`, the chapter's canonical Lipschitz
  smoothness theorem for the derivative selection.

Best owner abstraction:
- source-facing: the prox-smoothed objective `f_μ` defined by regularized maximization over the
  feasible dual set;
- core/canonical: `smoothedPrimalObjective A Q 0 phiHat d2 μ` together with `A.flip`,
  `smoothedObjective_hasFDerivAt` and `smoothedObjective_gradient_lipschitz`;
- bridge/view: this numbered lemma file, which should only recall the upstream owner theorem
  pair instead of introducing a second smoothing construction.

Primitive data:
- the linear map `A`;
- the feasible set `Q`, dual penalty `phiHat`, prox-function `d2`, and smoothing parameter `μ`;
- the maximizer selection `uMu`;
- the positivity, closed-convex, differentiability, and strong-convexity hypotheses already
  required by `Theorem_6_1`.

Derived API:
- the canonical transpose field `x ↦ A.flip (uMu x)`;
- the derivative identification `smoothedObjective_hasFDerivAt`;
- the Lipschitz smoothness theorem `smoothedObjective_gradient_lipschitz`.

Source/core/bridge triage:
- source-facing: Lemma 6.2's smoothness statement for the prox-smoothed objective;
- core/canonical: `A.flip`, `smoothedObjective_hasFDerivAt`, and
  `smoothedObjective_gradient_lipschitz`;
- bridge/view: this recall-only numbered surface.

The previous version introduced an averaging-based Euclidean-ball smoothing operator. That was a
different construction from the chapter's structured prox-smoothing objective and duplicated the
existing owner theorem. This file now reuses the chapter owner directly, recalling both the
derivative identification for `f_μ` and the Lipschitz estimate for the canonical field
`x ↦ A.flip (uMu x)`.
-/

recall smoothedObjective_hasFDerivAt
recall smoothedObjective_gradient_lipschitz

/-! ### Lemma_6_2_2 (from Chap06) -/
noncomputable section

open scoped Gradient

universe u v

/- Lemma 6.2.2 lies in the chapter's smoothed primal objective / tangent-plane domain.

Sampled owner declarations:
- `smoothedPrimalObjectiveMaximand`, `smoothedPrimalObjective`, and
  `smoothedPrimalObjectiveArgmax` in `Chap06/Definition_6_30`, the chapter
  owners for the regularized dual maximand, the smoothed objective, and its
  canonical argmax set;
- `mem_smoothedPrimalObjectiveArgmax_iff` in `Chap06/Definition_6_30`, the
  thin bridge from argmax membership to the underlying feasible-maximizer
  conditions;
- `smoothedPrimalObjective_linearization_le_selected_dual_value` in
  `Chap06/Lemma_6_7`, the immediate source-facing chapter theorem that packages
  the supporting-hyperplane step for `hatf` together with the selected dual
  maximizer;
- `ConvexOn.lower_tangent_plane_of_hasGradientWithinAt` in
  `Chap02/Definition_2_2`, the project owner for the first-order supporting
  inequality on a convex feasible set;
- `smoothedPrimalObjective_argmax_unique_and_hasGradientWithinAt` in
  `Chap06/Proposition_6_24`, which confirms that the canonical Chapter 6
  gradient surface is expressed through `smoothedPrimalObjective`,
  `smoothedPrimalObjectiveArgmax`, and `A.flip`.

Best owner abstraction:
- source-facing: the one-point linearization bound at a selected dual argmax;
- core/canonical: `smoothedPrimalObjective`, `smoothedPrimalObjectiveArgmax`,
  `ConvexOn`, `HasGradientWithinAt`, and `A.flip`;
- bridge/view: a chosen point `u` in the canonical argmax owner together with
  the displayed gradient formula.

Primitive data:
- the dual-valued linear map `A`;
- the feasible sets `Q₁` and `Q₂`;
- the functions `hatf`, `hatφ`, and `d₂`;
- the smoothing parameter `μ₂`;
- the selected dual point `u`;
- convexity of `hatf` on `Q₁`;
- the canonical within-set gradient witness for `hatf` at the base point;
- the owner-level within-set gradient witness for the smoothed primal objective
  at the base point;
- membership of `u` in the canonical argmax set at `xhat`;
- pointwise nonnegativity of `d₂` at the selected dual point `u`.

Derived API:
- the value of the smoothed objective at the selected argmax;
- the supporting-hyperplane inequality for `hatf`;
- on `UniqueDiffWithinAt` sets, the displayed `gradientWithin` equality for the
  smoothed objective.

Source/core/bridge triage:
- source-facing: the theorem below;
- core/canonical: the owner declarations from `Definition_6_30` and
  `Definition_2_2`;
- bridge/view: the pointwise selected maximizer `u`.

The previous version introduced duplicate local owners
`smoothedObjectiveIntegrand`, `primalDualSmoothedObjective`, and
`IsSmoothedMaximizerSelectionOn`. Those were exact re-encodings of the Chapter 6
owners in `Definition_6_30`, so this file now states the source-facing lemma
directly against the canonical API.
-/

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

-- Proof sketch: apply `smoothedPrimalObjective_linearization_le_selected_dual_value`
-- at the selected dual point `u` and rewrite the affine pairing term
-- using the transpose identity
-- `⟪(InnerProductSpace.toDual ℝ E₁).symm (A.flip u), v⟫ = A v u`.
/-- Lemma 6.2.2: if `u` lies in the canonical argmax set of the
regularized dual representation of the smoothed primal objective, then the
affine linearization at `xhat` written with the explicit vector
`∇ \hat f(xhat) + A^* u` is bounded above by the selected dual value. -/
theorem smoothedPrimalObjective_linearization_le_selected_dual_value_of_explicit_gradient
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) {Q₁ : Set E₁} {Q₂ : Set E₂}
    {hatf : E₁ → ℝ} {hatφ d₂ : E₂ → ℝ} {μ₂ : ℝ} (hhatf_conv : ConvexOn ℝ Q₁ hatf)
    (hμ₂ : 0 ≤ μ₂) {u : E₂} {x xhat : E₁} (hx : x ∈ Q₁) (hxhat : xhat ∈ Q₁)
    (hu : u ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ₂ xhat)
    (hhatf_grad :
      HasGradientWithinAt hatf (gradientWithin hatf Q₁ xhat) Q₁ xhat)
    (hd₂_nonneg : 0 ≤ d₂ u) :
    smoothedPrimalObjective A Q₂ hatf hatφ d₂ μ₂ xhat +
      inner ℝ
        (gradientWithin hatf Q₁ xhat +
          (InnerProductSpace.toDual ℝ E₁).symm (A.flip u))
        (x - xhat) ≤
      hatf x + A x u - hatφ u := by
  have hlinear :=
    smoothedPrimalObjective_linearization_le_selected_dual_value
      A hhatf_conv hμ₂ hx hxhat hu hhatf_grad hd₂_nonneg
  have hpair :
      inner ℝ
          ((InnerProductSpace.toDual ℝ E₁).symm (A.flip u))
          (x - xhat) =
        A (x - xhat) u := by
    rw [InnerProductSpace.toDual_symm_apply, ContinuousLinearMap.flip_apply]
  rw [inner_add_left, hpair]
  simpa [add_assoc] using hlinear

-- Proof sketch: recover the canonical `gradientWithin` value from the explicit
-- within-set gradient witness using `HasFDerivWithinAt.fderivWithin` on the
-- `UniqueDiffWithinAt` set `Q₁` at `xhat`.
/-- On a `UniqueDiffWithinAt` feasible set, the owner-level gradient witness
used in Lemma 6.2.2 rewrites the canonical `gradientWithin` of the smoothed
primal objective to `∇ \hat f(xhat) + A^* u`. -/
theorem smoothedPrimalObjective_gradientWithin_eq_gradientWithin_add_selected_dual
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) {Q₁ : Set E₁} {Q₂ : Set E₂}
    {hatf : E₁ → ℝ} {hatφ d₂ : E₂ → ℝ} {μ₂ : ℝ} {u : E₂} {xhat : E₁}
    (hfμ₂_grad :
      HasGradientWithinAt (smoothedPrimalObjective A Q₂ hatf hatφ d₂ μ₂)
        (gradientWithin hatf Q₁ xhat +
          (InnerProductSpace.toDual ℝ E₁).symm (A.flip u)) Q₁ xhat)
    (hQ₁_unique : UniqueDiffWithinAt ℝ Q₁ xhat) :
    gradientWithin (smoothedPrimalObjective A Q₂ hatf hatφ d₂ μ₂) Q₁ xhat =
      gradientWithin hatf Q₁ xhat +
        (InnerProductSpace.toDual ℝ E₁).symm (A.flip u) := by
  simpa [gradientWithin] using
    congrArg ((InnerProductSpace.toDual ℝ E₁).symm)
      (hfμ₂_grad.hasFDerivWithinAt.fderivWithin hQ₁_unique)

-- Proof sketch: rewrite the canonical `gradientWithin` of the smoothed
-- objective using the explicit within-set gradient witness, then apply the
-- source-facing explicit-gradient theorem above.
/-- Companion bridge theorem for Lemma 6.2.2: on a `UniqueDiffWithinAt`
feasible set, an explicit within-set gradient witness for the smoothed primal
objective rewrites the canonical `gradientWithin` linearization to the
source-facing explicit-gradient form. -/
theorem
    smoothedPrimalObjective_gradientWithin_linearization_le_selected_dual_value_of_uniqueDiff
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) {Q₁ : Set E₁} {Q₂ : Set E₂}
    {hatf : E₁ → ℝ} {hatφ d₂ : E₂ → ℝ} {μ₂ : ℝ} (hhatf_conv : ConvexOn ℝ Q₁ hatf)
    (hμ₂ : 0 ≤ μ₂) {u : E₂} {x xhat : E₁} (hx : x ∈ Q₁) (hxhat : xhat ∈ Q₁)
    (hu : u ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ₂ xhat)
    (hhatf_grad :
      HasGradientWithinAt hatf (gradientWithin hatf Q₁ xhat) Q₁ xhat)
    (hfμ₂_grad :
      HasGradientWithinAt (smoothedPrimalObjective A Q₂ hatf hatφ d₂ μ₂)
        (gradientWithin hatf Q₁ xhat +
          (InnerProductSpace.toDual ℝ E₁).symm (A.flip u)) Q₁ xhat)
    (hQ₁_unique : UniqueDiffWithinAt ℝ Q₁ xhat)
    (hd₂_nonneg : 0 ≤ d₂ u) :
    smoothedPrimalObjective A Q₂ hatf hatφ d₂ μ₂ xhat +
      inner ℝ
        (gradientWithin (smoothedPrimalObjective A Q₂ hatf hatφ d₂ μ₂) Q₁ xhat)
        (x - xhat) ≤
      hatf x + A x u - hatφ u := by
  rw [smoothedPrimalObjective_gradientWithin_eq_gradientWithin_add_selected_dual
    A hfμ₂_grad hQ₁_unique]
  exact
    smoothedPrimalObjective_linearization_le_selected_dual_value_of_explicit_gradient
      A hhatf_conv hμ₂ hx hxhat hu hhatf_grad hd₂_nonneg

end

/-! ### Proposition_6_2 (from Chap06) -/
noncomputable section

open scoped ConvexAnalysis WithTopConvexAnalysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Proposition 6.2 lies in the chapter's extended-valued Fenchel / subdifferential domain.

Primary domain:
- Fenchel duality and extended-valued subgradients on real inner-product spaces.

Relevant sampled owner-style declarations:
- `dom` and `withTopToEReal` in `Definition_3_3`, the canonical effective-domain / codomain bridge;
- `IsSubgradientAt`, `subdifferential`, and the notation `∂ f(x)` in `Definition_3_1_5`, the
  chapter owner surface for extended-valued subgradients;
- `fenchelDual` and the notation `f⋆` in `Definition_3_1_2_1`, the source-facing Fenchel-dual
  owner induced from the dual-space owner `fenchelConjugate`;
- `subdifferential_subset_dom_fenchelDual_of_nonempty` in `Theorem_3_1_5_2`, the nearby owner
  theorem showing that nonempty `∂ f(x)` forces finiteness of `f⋆` at every subgradient.

Best owner abstraction:
- the existing source-facing owner surface `∂ f(x)` and `f⋆`.

Primitive data:
- a membership hypothesis `g ∈ ∂ f(x)`.

Derived API:
- the Fenchel--Young equality at a subgradient;
- the corresponding affine lower-support inequality for the dual function at the dual point.

Source/core/bridge triage:
- source-facing: Proposition 6.2's equality `f(x) + f*(g) = ⟪g, x⟫`;
- core/canonical: `dom`, `subdifferential`, `fenchelDual`;
- bridge/view: the second theorem below, which states the source-facing content of
  `x ∈ ∂ f*(g)` directly on the canonical `EReal`-valued owner `f⋆`, instead of rebuilding a
  parallel `WithTop ℝ`-valued conjugate wrapper just to reuse `subdifferential`.

The previous version duplicated the effective-domain, finite-real-part, subgradient,
subdifferential, and Fenchel-conjugate owners locally. This refinement removes those duplicate
wheels and keeps Proposition 6.2 on the existing chapter owner surface. The textbook hypotheses
that `f` is proper, convex, and finite-dimensional are not needed for the statement itself once
`g ∈ ∂ f(x)` is taken as primitive data, so they are removed from the public API.
-/

-- Proof sketch: the defining subgradient inequality with `y = x` gives one side, and evaluating
-- the supremum defining `f⋆(g)` at `x` gives the reverse side.
/-- Proposition 6.2: if `g ∈ ∂ f(x)`, then `f(x) + f*(g) = ⟪g, x⟫`. -/
theorem fenchelYoung_equality_of_mem_subdifferential
    {f : E → WithTop ℝ} {x g : E} (hg : g ∈ ∂ f(x)) :
    withTopToEReal (f x) + (f⋆) g = (inner ℝ g x : EReal) := by
  have hxdom : x ∈ dom f := (mem_subdifferential_iff.mp hg).1
  have hfx_ne_bot : withTopToEReal (f x) ≠ ⊥ := by
    change (((f x : WithTop ℝ) : WithBot (WithTop ℝ))) ≠ ⊥
    exact WithBot.coe_ne_bot
  have hfx_ne_top : withTopToEReal (f x) ≠ ⊤ := by
    have hx' : f x < ⊤ := mem_withTopEffectiveDomain_iff.mp hxdom
    change (((f x : WithTop ℝ) : WithBot (WithTop ℝ))) ≠ ⊤
    exact_mod_cast ne_of_lt hx'
  have hfx : ((withTopRealPart f x : ℝ) : EReal) = withTopToEReal (f x) := by
    simpa [withTopToEReal] using congrArg withTopToEReal (coe_withTopRealPart hxdom)
  have hsup_le : (f⋆) g ≤ (inner ℝ g x : EReal) - withTopToEReal (f x) := by
    rw [fenchelDual_apply]
    refine iSup_le ?_
    intro y
    by_cases hy : y ∈ dom f
    · have hsub := (mem_subdifferential_iff.mp hg).2 hy
      have hy' : ((withTopRealPart f y : ℝ) : EReal) = withTopToEReal (f y) := by
        simpa [withTopToEReal] using congrArg withTopToEReal (coe_withTopRealPart hy)
      have hreal : inner ℝ g y - withTopRealPart f y ≤ inner ℝ g x - withTopRealPart f x := by
        have hsub' : withTopRealPart f x + inner ℝ g (y - x) ≤ withTopRealPart f y := by
          have hsub'' := hsub
          rw [← coe_withTopRealPart hxdom] at hsub''
          rw [← coe_withTopRealPart hy] at hsub''
          exact_mod_cast hsub''
        rw [inner_sub_right] at hsub'
        linarith
      rw [← hy', ← hfx, ← EReal.coe_sub, ← EReal.coe_sub]
      exact_mod_cast hreal
    · have hy_top : f y = ⊤ := top_unique (not_lt.mp hy)
      rw [hy_top, withTopToEReal]
      change (⊥ : EReal) ≤ (inner ℝ g x : EReal) - withTopToEReal (f x)
      exact bot_le
  have hle : withTopToEReal (f x) + (f⋆) g ≤ (inner ℝ g x : EReal) := by
    have := EReal.add_le_of_le_sub hsup_le
    simpa [add_comm, add_left_comm, add_assoc] using this
  have hge : (inner ℝ g x : EReal) ≤ withTopToEReal (f x) + (f⋆) g := by
    rw [fenchelDual_apply]
    have htest : (inner ℝ g x : EReal) - withTopToEReal (f x) ≤ (f⋆) g := by
      exact le_iSup (fun y : E ↦ (inner ℝ g y : EReal) - withTopToEReal (f y)) x
    have hconv :
        (inner ℝ g x : EReal) - withTopToEReal (f x) ≤ (f⋆) g ↔
          (inner ℝ g x : EReal) ≤ (f⋆) g + withTopToEReal (f x) :=
      EReal.sub_le_iff_le_add (Or.inl hfx_ne_bot) (Or.inl hfx_ne_top)
    have : (inner ℝ g x : EReal) ≤ (f⋆) g + withTopToEReal (f x) := hconv.mp htest
    simpa [add_comm] using this
  exact antisymm hle hge

-- Proof sketch: combine the Fenchel--Young equality at `(x, g)` with the defining supremum lower
-- bound `(f⋆) h ≥ ⟪h, x⟫ - f(x)` obtained by testing the supremum at `x`.
/-- If `g ∈ ∂ f(x)`, then `x` satisfies the dual affine lower-support inequality at `g`, i.e. the
source-facing content of `x ∈ ∂ f*(g)` on the canonical owner `f⋆`. -/
theorem subgradient_inequality_fenchelDual_of_mem_subdifferential
    {f : E → WithTop ℝ} {x g : E} (hg : g ∈ ∂ f(x)) :
    g ∈ dom (f⋆) ∧
      ∀ ⦃h : E⦄, h ∈ dom (f⋆) →
        (f⋆) h ≥ (f⋆) g + (inner ℝ x (h - g) : EReal) := by
  refine ⟨subdifferential_subset_dom_fenchelDual hg, ?_⟩
  intro h hhdom
  have hxdom : x ∈ dom f := (mem_subdifferential_iff.mp hg).1
  have hfx_ne_bot : withTopToEReal (f x) ≠ ⊥ := by
    change (((f x : WithTop ℝ) : WithBot (WithTop ℝ))) ≠ ⊥
    exact WithBot.coe_ne_bot
  have hfx_ne_top : withTopToEReal (f x) ≠ ⊤ := by
    have hx' : f x < ⊤ := mem_withTopEffectiveDomain_iff.mp hxdom
    change (((f x : WithTop ℝ) : WithBot (WithTop ℝ))) ≠ ⊤
    exact_mod_cast ne_of_lt hx'
  have htest : (inner ℝ h x : EReal) - withTopToEReal (f x) ≤ (f⋆) h := by
    rw [fenchelDual_apply]
    exact le_iSup (fun y : E ↦ (inner ℝ h y : EReal) - withTopToEReal (f y)) x
  have hsupport : (f⋆) g + (inner ℝ x (h - g) : EReal) ≤
      (inner ℝ h x : EReal) - withTopToEReal (f x) := by
    have hsupport_add :
        (f⋆) g + (inner ℝ x (h - g) : EReal) + withTopToEReal (f x) ≤
          (inner ℝ h x : EReal) := by
      calc
        (f⋆) g + (inner ℝ x (h - g) : EReal) + withTopToEReal (f x)
            = withTopToEReal (f x) + (f⋆) g + (inner ℝ x (h - g) : EReal) := by
                ac_rfl
        _ = (inner ℝ g x : EReal) + (inner ℝ x (h - g) : EReal) := by
              rw [fenchelYoung_equality_of_mem_subdifferential hg]
        _ ≤ (inner ℝ h x : EReal) := by
              have hreal : inner ℝ g x + inner ℝ x (h - g) = inner ℝ h x := by
                rw [inner_sub_right, real_inner_comm x g, real_inner_comm x h]
                ring
              exact le_of_eq (by exact_mod_cast hreal)
    have hsub :
        (f⋆) g + (inner ℝ x (h - g) : EReal) ≤
            (inner ℝ h x : EReal) - withTopToEReal (f x) ↔
          (f⋆) g + (inner ℝ x (h - g) : EReal) + withTopToEReal (f x) ≤
            (inner ℝ h x : EReal) :=
      EReal.le_sub_iff_add_le (Or.inl hfx_ne_bot) (Or.inl hfx_ne_top)
    exact hsub.2 hsupport_add
  exact hsupport.trans htest

end

/-! ### Theorem_6_2 (from Chap06) -/
noncomputable section

open scoped BigOperators
open scoped ConstrainedArgmin
open scoped WithTopConvexAnalysis

universe u

/- Theorem 6.2 lies in the chapter's composite-acceleration / similar-triangles domain.

Sampled owner-style declarations:
- `CompositeLipschitzGradientModel` in `Definition_6_8`, the chapter owner for a composite
  problem together with its chosen gradient field, Lipschitz constant, prox-function, and
  tractable prox subproblems;
- `constrainedArgmin` with notation `argmin[Q] f` in `Chap01/Definition_1_3_3`, the project
  owner for constrained minimizers on a feasible set;
- `IsProxCenter` in `Definition_6_31`, the canonical normalized prox-center owner for the initial
  point of the prox term;
- `SimilarTrianglesMethod`, `similarTrianglesEstimatingWeight`, and
  `SimilarTrianglesMethod.interpolationPoint` in `Algorithm_6_1`, the canonical owner layer for
  method `(6.1.19)`;
- `similarTrianglesEstimatingUpdate` in `Algorithm_6_1`, the owner recursion for the estimating
  functions `φ_k`.

Best owner abstraction:
- source-facing: Theorem 6.2's explicit estimating-function lower bound and the resulting
  suboptimality estimate;
- core/canonical: `SimilarTrianglesMethod` over `CompositeLipschitzGradientModel`, together with
  the normalized prox-center owner `IsProxCenter model.feasibleSet model.proxFunction x0` and
  the constrained minimizer owner
  `argmin[model.feasibleSet] (fun x ↦ model.smoothPart x + withTopRealPart model.nonsmoothPart x)`;
- bridge/view: the closed-form estimating function on the feasible-set owner `model.feasibleSet`,
  using the canonical Chapter 3 finite real part `withTopRealPart model.nonsmoothPart` rather
  than a parallel global real-valued regularizer witness.

Primitive data:
- a similar-triangles method over the canonical composite Lipschitz-gradient owner;
- a normalized prox-center `x0` for the prox-function `d`;
- the closed convex regularizer `model.nonsmoothPart : E → WithTop ℝ`, already owned by the
  Chapter 3 composite problem structure;
- the explicit affine-model closed form of `φ_k` on the feasible-set subtype, where the
  regularizer is canonically read through `withTopRealPart`.

Derived API:
- the closed-form estimating function `estimatingFunction`;
- the bridge theorem comparing `method.φ` with the closed-form `φ_k`;
- the lower-bound and suboptimality statements of Theorem 6.2, with constrained optimality
  consumed through the Chapter 1 argmin owner rather than a parallel raw `IsMinOn` hypothesis.

Source/core/bridge triage:
- source-facing: the two theorem statements below;
- core/canonical: `SimilarTrianglesMethod`, `IsProxCenter`, and `argmin[Q] f`;
- bridge/view: `estimatingFunction` and `phi_eq_estimatingFunction`. -/

namespace SimilarTrianglesMethod

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {model : CompositeLipschitzGradientModel E} {x0 : model.feasibleSet}

/-- The closed-form estimating function `φ_k` from Theorem 6.2, written on the canonical
similar-triangles owner surface over the feasible-set subtype and using the chapter owner
`withTopRealPart model.nonsmoothPart` for the regularizer term. -/
def estimatingFunction
    (method : SimilarTrianglesMethod model x0)
    (k : ℕ) : model.feasibleSet → ℝ :=
  fun x ↦
    (model.L : ℝ) * model.proxFunction x +
      Finset.sum (Finset.range k) (fun i ↦
        similarTrianglesEstimatingWeight i *
          (model.smoothPart (method.interpolationPoint i) +
            model.smoothGradient (method.interpolationPoint i)
              (x - method.interpolationPoint i))) +
      (((k : ℝ) * (k + 1)) / 4) * withTopRealPart model.nonsmoothPart x

/-- Evaluating the explicit estimating function recovers the prox term, the accumulated affine
models of `model.smoothPart` at the interpolation points `y_i`, and the penalty term
`((k (k + 1)) / 4) withTopRealPart model.nonsmoothPart x` on the feasible set. -/
-- Proof sketch: unfold `estimatingFunction`.
@[simp] theorem estimatingFunction_apply
    (method : SimilarTrianglesMethod model x0)
    (k : ℕ) (x : model.feasibleSet) :
    method.estimatingFunction k x =
      (model.L : ℝ) * model.proxFunction x +
        Finset.sum (Finset.range k) (fun i ↦
          similarTrianglesEstimatingWeight i *
            (model.smoothPart (method.interpolationPoint i) +
              model.smoothGradient (method.interpolationPoint i)
                (x - method.interpolationPoint i))) +
        (((k : ℝ) * (k + 1)) / 4) * withTopRealPart model.nonsmoothPart x := sorry

-- Proof sketch: prove by induction on `k`, using `phi_zero`, `phi_succ`,
-- `similarTrianglesEstimatingUpdate_apply`, and the identity
-- `∑_{i=0}^{k-1} ((i + 1) / 2) = (k (k + 1)) / 4`, with the nonsmooth term rewritten on the
-- feasible set via `withTopRealPart`.
/-- On the feasible set `Q`, the recursive estimating-function owner `method.φ k` is the
extended-real coercion of the closed-form `φ_k` from Theorem 6.2. -/
theorem phi_eq_estimatingFunction
    (method : SimilarTrianglesMethod model x0)
    (k : ℕ) (x : model.feasibleSet) :
    method.φ k x = (method.estimatingFunction k x : WithTop ℝ) := sorry

-- Proof sketch: combine the quadratic-growth bound from the prox-center hypothesis at `k = 0`
-- with the standard estimating-sequence induction on feasible points using
-- `phi_eq_estimatingFunction`, the minimizing property `v_succ_isMin`, convexity of `f`, and
-- the update rules of `SimilarTrianglesMethod`.
/-- Theorem 6.2 [Chapter6_2.json:20]: equation `(6.1.20)` states that if `x_k`, `y_k`, and
`v_k` are generated by method `(6.1.19)`, then for every `k ≥ 0` and every feasible point
`x ∈ Q`,
`((k (k + 1)) / 4) \tilde f(x_k) + (L / 2) ‖v_k - x‖² ≤ φ_k(x)`, where
`\tilde f(x_k) = f(x_k) + Ψ(x_k)` is read through the canonical finite-real-part bridge on
`Q`. -/
theorem objective_le_estimatingFunction
    (method : SimilarTrianglesMethod model x0)
    (hx0 : IsProxCenter model.feasibleSet model.proxFunction (x0 : E))
    (k : ℕ) (x : model.feasibleSet) :
    (((k : ℝ) * (k + 1)) / 4) *
          (model.smoothPart (method k) + withTopRealPart model.nonsmoothPart (method k)) +
        ((model.L : ℝ) / 2) * ‖(method.v k : E) - x‖ ^ (2 : ℕ) ≤
      method.estimatingFunction k x := sorry

-- Proof sketch: apply `objective_le_estimatingFunction` with `x = xStar`, unpack the canonical
-- argmin owner hypothesis through `mem_constrainedArgmin_iff` to recover feasibility and the
-- minimizing property of `xStar` for the composite objective, and divide by
-- `((k (k + 1)) / 4)` for `k ≥ 1`.
/-- The suboptimality estimate `(6.1.21)` obtained from the estimating-function lower bound:
if `xStar` is an optimal solution of problem `(6.1.18)`, then for every `k ≥ 1` the iterate
suboptimality and the squared distance to `v_k` satisfy the displayed accelerated rate
estimate. -/
theorem suboptimality_bound
    (method : SimilarTrianglesMethod model x0)
    (hx0 : IsProxCenter model.feasibleSet model.proxFunction (x0 : E))
    (xStar : E)
    (hxStar : xStar ∈
      argmin[model.feasibleSet]
        (fun x ↦ model.smoothPart x + withTopRealPart model.nonsmoothPart x))
    {k : ℕ} (hk : 1 ≤ k) :
    (model.smoothPart (method k) + withTopRealPart model.nonsmoothPart (method k)) -
        (model.smoothPart xStar + withTopRealPart model.nonsmoothPart xStar) +
        (2 * (model.L : ℝ) / ((k : ℝ) * (k + 1))) * ‖(method.v k : E) - xStar‖ ^ (2 : ℕ) ≤
      (4 * (model.L : ℝ) * model.proxFunction xStar) / ((k : ℝ) * (k + 1)) := sorry

end SimilarTrianglesMethod

end

/-! ### Theorem_6_2_2 (from Chap06) -/
noncomputable section

open scoped ConstrainedArgmin

universe u v

section

variable
    {X : Type u} {U : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    {Q₁ : Set X} {Q₂ : Set U}
    (hQ₁ : Convex ℝ Q₁) (hQ₂ : Convex ℝ Q₂)
    {A₀ : X →L[ℝ] StrongDual ℝ U}
    {hatf : X → ℝ} {hatφ : U → ℝ} {d₁ : X → ℝ} {d₂ : U → ℝ}
    (xμ : ℝ → U → X)
    (hxμ :
      ∀ μ : ℝ, ∀ u : U,
        xμ μ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A₀ hatf d₁ μ u))
    (uμ : ℝ → X → U)
    (huμ :
      ∀ μ : ℝ, ∀ x : X, x ∈ Q₁ →
        uμ μ x ∈ smoothedPrimalObjectiveArgmax A₀ Q₂ hatφ d₂ μ x)
    (x₀ : Q₂ → Q₁) (V : Q₂ → Q₂)
    {fμ₂ : ℝ → X → ℝ} {φμ₁ : ℝ → U → ℝ}
    {fμ₂_zero : ℝ → Q₁ → ℝ} {φ_zero : Q₂ → ℝ}
    {initialPrimalSmoothing initialDualSmoothing : ℝ}
    (initialState : Q₁ × Q₂)

/- Theorem 6.2.2 lies in the chapter's alternating excessive-gap recursion / rate domain.

Mandatory domain-style sampling before refinement:
- `algorithm_6_3_primal_smoothing` and `algorithm_6_3_dual_smoothing` in
  `Chap06/Algorithm_6_3`, the source-facing smoothing-parameter recursions of Algorithm 6.3;
- `alternatingExcessiveGapPrimalIterate` and `alternatingExcessiveGapDualIterate` in
  `Chap06/Algorithm_6_3`, the source-facing owners of the actual alternating recursion;
- `algorithm_6_3_iterates_satisfy_excessive_gap_condition` in `Chap06/Theorem_6_6`, the chapter
  owner propagating the excessive-gap certificate along the actual Algorithm 6.3 recursion;
- `satisfiesExcessiveGapCondition` in `Chap06/Theorem_6_4`, the chapter owner of the excessive-gap
  certificate;
- `raw_duality_gap_le_excessive_gap_budget` in `Chap06/Lemma_6_2_1`, the chapter owner turning an
  excessive-gap certificate into the textbook raw-gap budget estimate.

Best owner abstraction:
- source-facing: the actual Algorithm 6.3 smoothing and iterate sequences;
- core/canonical: `algorithm_6_3_iterates_satisfy_excessive_gap_condition`,
  `satisfiesExcessiveGapCondition`, and `raw_duality_gap_le_excessive_gap_budget`;
- bridge/view: the rate theorem below, which composes the canonical propagation result with the
  raw-gap budget estimate.

Primitive data:
- the feasible sets and the Chapter 6 even/odd update-owner data used by Algorithm 6.3;
- the initial smoothing parameters `μ₁,0`, `μ₂,0`;
- the feasible initial state, the canonical propagation hypotheses from `Theorem_6_6`, and the
  stagewise smoothing bounds.

Derived API:
- the stagewise excessive-gap certificate for the actual Algorithm 6.3 iterates;
- the duality-gap rate bound obtained from that certificate and the smoothing budget estimate.

The previous version still fed Theorem 6.2.2 through external smoothing sequences. This
refinement instead reuses the source-facing smoothing owners from `Algorithm_6_3`, so the rate
theorem now speaks directly about the chapter's actual recursion.
-/

local notation "μ₁" =>
  algorithm_6_3_primal_smoothing initialPrimalSmoothing

local notation "μ₂" =>
  algorithm_6_3_dual_smoothing initialDualSmoothing

local notation "x̄" =>
  alternatingExcessiveGapPrimalIterate
    hQ₁
    hQ₂
    xμ
    hxμ
    uμ
    huμ
    x₀
    V
    initialPrimalSmoothing
    initialDualSmoothing
    initialState

local notation "ū" =>
  alternatingExcessiveGapDualIterate
    hQ₁
    hQ₂
    xμ
    hxμ
    uμ
    huμ
    x₀
    V
    initialPrimalSmoothing
    initialDualSmoothing
    initialState

local notation "x̄ₑ" =>
  fun k ↦
    algorithm_6_3_even_primal_iterate
      hQ₁
      hQ₂
      xμ
      hxμ
      uμ
      huμ
      initialPrimalSmoothing
      initialDualSmoothing
      (x̄ k, ū k)
      k

local notation "ūₑ" =>
  fun k ↦
    algorithm_6_3_even_dual_iterate
      hQ₁
      hQ₂
      xμ
      hxμ
      uμ
      huμ
      initialPrimalSmoothing
      initialDualSmoothing
      (x̄ k, ū k)
      k

local notation "x̄ₒ" =>
  fun k ↦
    algorithm_6_3_odd_primal_iterate
      hQ₁
      hQ₂
      uμ
      huμ
      x₀
      initialDualSmoothing
      (x̄ k, ū k)
      k

local notation "ūₒ" =>
  fun k ↦
    algorithm_6_3_odd_dual_iterate
      hQ₂
      uμ
      huμ
      V
      initialDualSmoothing
      (x̄ k, ū k)
      k

/-- Theorem 6.2.2: if the Algorithm 6.3 iterates start from an excessive-gap pair and each even
and odd update satisfy the canonical propagation hypotheses of `Theorem_6_6`, then every iterate
pair `(x̄_k, ū_k)` of the feasible Algorithm 6.3 recursion satisfies the Chapter 6 excessive-gap
certificate; if the smoothing budget also obeys the chapter rate estimate, then the raw duality
gap satisfies the same rate bound. -/
-- Proof sketch: first propagate the excessive-gap certificate along the actual Algorithm 6.3
-- recursion by applying `algorithm_6_3_iterates_satisfy_excessive_gap_condition`; then combine
-- the stagewise smoothing estimates with the propagated certificate to bound the raw duality gap
-- by `μ₁,k D₁ + μ₂,k D₂`, and finally apply `hbudget`.
theorem algorithm_6_3_excessive_gap_and_duality_gap_rate
    {A : X →L[ℝ] U}
    {f : X → ℝ} {φ : U → ℝ} {D₁ D₂ : ℝ}
    (hzero :
      satisfiesExcessiveGapCondition
        Q₁
        Q₂
        (fμ₂ (μ₂ 0))
        (φμ₁ (μ₁ 0))
        (x̄ 0)
        (ū 0))
    (heven_step :
      ∀ k : ℕ, Even k →
        satisfiesExcessiveGapCondition
          Q₁
          Q₂
          (fμ₂ (μ₂ k))
          (φμ₁ (μ₁ k))
          (x̄ k)
          (ū k) →
        satisfiesExcessiveGapCondition
          Q₁
          Q₂
          (fμ₂ (μ₂ (k + 1)))
          (φμ₁ (μ₁ (k + 1)))
          (x̄ₑ k)
          (ūₑ k))
    (hodd_source :
      ∀ k : ℕ, Odd k →
        satisfiesExcessiveGapCondition
          Q₁
          Q₂
          (fμ₂ (μ₂ k))
          (φμ₁ (μ₁ k))
          (x̄ k)
          (ū k) →
        satisfiesExcessiveGapConditionWithMu1Zero
          (fμ₂_zero (μ₂ k))
          φ_zero
          (x̄ k)
          (ū k))
    (hodd_step :
      ∀ k : ℕ, Odd k →
        satisfiesExcessiveGapConditionWithMu1Zero
          (fμ₂_zero (μ₂ k))
          φ_zero
          (x̄ k)
          (ū k) →
        satisfiesExcessiveGapConditionWithMu1Zero
          (fμ₂_zero (μ₂ (k + 1)))
          φ_zero
          (x̄ₒ k)
          (ūₒ k))
    (hodd_target :
      ∀ k : ℕ, Odd k →
        satisfiesExcessiveGapConditionWithMu1Zero
          (fμ₂_zero (μ₂ (k + 1)))
          φ_zero
          (x̄ₒ k)
          (ūₒ k) →
        satisfiesExcessiveGapCondition
          Q₁
          Q₂
          (fμ₂ (μ₂ (k + 1)))
          (φμ₁ (μ₁ (k + 1)))
          (x̄ₒ k)
          (ūₒ k))
    (hfμ₂_lower :
      ∀ k : ℕ,
        f (x̄ k) - μ₂ k * D₂ ≤ fμ₂ (μ₂ k) (x̄ k))
    (hφμ₁_upper :
      ∀ k : ℕ,
        φμ₁ (μ₁ k) (ū k) ≤ φ (ū k) + μ₁ k * D₁)
    (hbudget :
      ∀ k : ℕ,
        μ₁ k * D₁ + μ₂ k * D₂ ≤
          (4 * ‖A‖ * Real.sqrt (D₁ * D₂)) / ((k : ℝ) + 1)) :
    ∀ k : ℕ,
      satisfiesExcessiveGapCondition
        Q₁
        Q₂
        (fμ₂ (μ₂ k))
        (φμ₁ (μ₁ k))
        (x̄ k)
        (ū k) ∧
      f (x̄ k) - φ (ū k) ≤
        (4 * ‖A‖ * Real.sqrt (D₁ * D₂)) / ((k : ℝ) + 1) := sorry

end

/-! ### Lemma_6_2_3 (from Chap06) -/
noncomputable section

open scoped Gradient

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]

/-
Lemma 6.2.3 lies in the Chapter 6 smoothed dual / excessive-gap domain.

Sampled owner-style declarations:
- mathlib `IsMinOn`, the canonical minimizer owner for the two prox subproblems;
- `ConvexOn.lower_tangent_plane_of_hasGradientWithinAt` in `Chap02/Definition_2_2`, the chapter
  owner for the convex first-order lower bound used at `x₀`;
- `smoothedDualObjectiveMinimand` in `Chap06/Definition_6_32`, the nearby chapter owner showing
  that the primal prox point should be treated through its minimizing property rather than through
  an auxiliary wrapper;
- `IsSmoothedDualMinimizerSelection.isMinOn` in `Chap06/Definition_6_33`, the pointwise Chapter 6
  bridge from a selector to the actual minimizer property.

Best owner abstraction:
- core/canonical: the actual chosen points `uBar` and `xμ₁uBar` together with their
  `IsMinOn`-based minimizing data.

Primitive data:
- the feasible set `Q₁`, the smoothed objective `fμ₂`, the prox term `d₁`, and the points
  `x₀`, `xBar`, `uBar`, `xμ₁uBar`;
- the convexity and gradient data at `x₀`;
- the minimizing properties of `xBar` and `xμ₁uBar` for the two linearized prox models;
- the identity expressing `φμ₁ uBar`.

Derived API:
- the excessive-gap inequality `fμ₂ xBar ≤ φμ₁ uBar`.

Source/core/bridge triage:
- source-facing: the excessive-gap inequality for one chosen smoothed pair;
- core/canonical: the minimizer owners `IsMinOn` at the specific points `xBar` and `xμ₁uBar`;
- bridge/view: the identity giving `φμ₁ uBar` in terms of the selected prox point.

The previous statement kept whole selector functions `uμ₂` and `xμ₁` plus an auxiliary subtype
`Q₂`, even though the theorem only used the single values `uμ₂ x₀` and `xμ₁ (uμ₂ x₀)`. This is
not chapter-canonical data: the mathematics depends only on the chosen dual point and chosen prox
point together with their minimizing properties. The refined owner theorem therefore keeps those
points directly and deletes the parallel selector-function layer.
-/

-- Proof sketch: convexity of `fμ₂` and the gradient hypothesis give the affine lower bound
-- at `xBar`. Combining that bound with the minimizing property of `xBar` for the
-- `Lfμ₂`-weighted linearized prox model yields
-- `fμ₂ xBar ≤ fμ₂ x₀ + Lfμ₂ * (d₁ x₀ - d₁ xBar)`. The minimizing property of
-- `xμ₁uBar` for the `μ₁`-weighted model and the inequality `Lfμ₂ ≤ μ₁` then imply
-- `d₁ xμ₁uBar ≤ d₁ xBar`, and substituting this into the displayed identity for `φμ₁ uBar`
-- gives the excessive-gap inequality.
/-- Lemma 6.2.3: if `xBar ∈ Q₁` minimizes the linearized prox model
`x ↦ ⟪∇ f_{μ₂}(x₀), x - x₀⟫ + L₁(f_{μ₂}) d₁(x)` and `u_{μ₂}(x₀)` satisfies the standard
smoothed-gap identity through the selected primal prox point `xμ₁uBar`, then every
`μ₁ ≥ L₁(f_{μ₂})` yields the excessive-gap inequality `f_{μ₂}(xBar) ≤ φ_{μ₁}(uBar)`. -/
theorem smoothed_pair_excessive_gap_of_linearized_prox_minimizers
    {Q₁ : Set E₁} {fμ₂ : E₁ → ℝ} {φμ₁ : E₂ → ℝ} {d₁ : E₁ → ℝ}
    {x₀ xBar xμ₁uBar : Q₁} {uBar : E₂} {μ₁ Lfμ₂ : ℝ}
    (hconv : ConvexOn ℝ Q₁ fμ₂)
    (hfμ₂_grad : HasGradientWithinAt fμ₂ (gradientWithin fμ₂ Q₁ x₀) Q₁ x₀)
    (hbar_min :
      IsMinOn
        (fun x ↦ inner ℝ (gradientWithin fμ₂ Q₁ x₀) (x - x₀) + Lfμ₂ * d₁ x)
        Q₁
        xBar)
    (hxμ₁_min :
      IsMinOn
        (fun x ↦ inner ℝ (gradientWithin fμ₂ Q₁ x₀) x + μ₁ * d₁ x)
        Q₁
        xμ₁uBar)
    (hφμ₁ :
      φμ₁ uBar =
        fμ₂ x₀ + μ₁ * (d₁ x₀ - d₁ xμ₁uBar))
    (hμ₁ : Lfμ₂ ≤ μ₁) :
    fμ₂ xBar ≤ φμ₁ uBar := sorry

end
