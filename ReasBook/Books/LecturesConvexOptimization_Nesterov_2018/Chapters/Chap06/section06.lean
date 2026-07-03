import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_6 (from Chap06) -/
noncomputable section

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-- A structured objective model consists of bounded closed convex sets `Q₁ ⊆ E₁` and
`Q₂ ⊆ E₂`, continuous convex functions `\hat f` on `Q₁` and `\hat φ` on `Q₂`, and a linear
operator `A : E₁ → E₂*`. -/
structure StructuredObjectiveModel (E₁ : Type u) (E₂ : Type v)
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] where
  /-- The primal set `Q₁ ⊆ E₁`. -/
  primalSet : Set E₁
  /-- The primal set `Q₁` is bounded. -/
  primalSet_bounded : Bornology.IsBounded primalSet
  /-- The primal set `Q₁` is closed. -/
  primalSet_closed : IsClosed primalSet
  /-- The primal set `Q₁` is convex. -/
  primalSet_convex : Convex ℝ primalSet
  /-- The dual set `Q₂ ⊆ E₂`. -/
  dualSet : Set E₂
  /-- The dual set `Q₂` is bounded. -/
  dualSet_bounded : Bornology.IsBounded dualSet
  /-- The dual set `Q₂` is closed. -/
  dualSet_closed : IsClosed dualSet
  /-- The dual set `Q₂` is convex. -/
  dualSet_convex : Convex ℝ dualSet
  /-- The continuous convex term `\hat f : E₁ → ℝ`, considered on `Q₁`. -/
  smoothPart : E₁ → ℝ
  /-- The continuous convex term `\hat φ : E₂ → ℝ`, considered on `Q₂`. -/
  dualPenalty : E₂ → ℝ
  /-- The linear operator `A : E₁ → E₂*`. -/
  linearMap : E₁ →L[ℝ] StrongDual ℝ E₂
  /-- The term `\hat f` is continuous on `Q₁`. -/
  smoothPart_continuous : ContinuousOn smoothPart primalSet
  /-- The term `\hat f` is convex on `Q₁`. -/
  smoothPart_convex : ConvexOn ℝ primalSet smoothPart
  /-- The term `\hat φ` is continuous on `Q₂`. -/
  dualPenalty_continuous : ContinuousOn dualPenalty dualSet
  /-- The term `\hat φ` is convex on `Q₂`. -/
  dualPenalty_convex : ConvexOn ℝ dualSet dualPenalty

namespace StructuredObjectiveModel

/-- The affine-convex maximand `u ↦ ⟪A x, u⟫ - \hat φ(u)` associated to a fixed `x ∈ Q₁`. -/
def maximand (problem : StructuredObjectiveModel E₁ E₂) (x : problem.primalSet) :
    problem.dualSet → ℝ :=
  fun u ↦ problem.linearMap x u - problem.dualPenalty u

/-- Definition 6.6 [Chapter6_1.json:11]: for a structured objective model, the saddle function is
`Ψ(x, u) = \hat f(x) + ⟪A x, u⟫ - \hat φ(u)` on `Q₁ × Q₂`; this saddle-point reformulation is
the basis for the primal and adjoint value functions defined below. -/
def saddleFunction (problem : StructuredObjectiveModel E₁ E₂) :
    problem.primalSet → problem.dualSet → ℝ :=
  fun x u ↦ problem.smoothPart x + problem.linearMap x u - problem.dualPenalty u

-- Proof sketch: unfold `saddleFunction`; the statement is definitionally true.
/-- Evaluating the saddle function recovers `\hat f(x) + ⟪A x, u⟫ - \hat φ(u)`. -/
theorem saddleFunction_apply (problem : StructuredObjectiveModel E₁ E₂)
    (x : problem.primalSet) (u : problem.dualSet) :
    problem.saddleFunction x u =
      problem.smoothPart x + problem.linearMap x u - problem.dualPenalty u :=
  sorry

/-- The primal objective `f(x) = sup_{u ∈ Q₂} Ψ(x, u)` attached to a structured objective model,
viewed in `EReal` so the supremum is represented faithfully without extra attainment or
boundedness hypotheses on the saddle slice. -/
def objective (problem : StructuredObjectiveModel E₁ E₂) : problem.primalSet → EReal :=
  fun x ↦ sSup (Set.range fun u : problem.dualSet ↦ (problem.saddleFunction x u : EReal))

/-- A structured objective model can be evaluated as its objective on the primal set `Q₁`. -/
instance : CoeFun (StructuredObjectiveModel E₁ E₂) (fun problem ↦ problem.primalSet → EReal) where
  coe problem := problem.objective

-- Proof sketch: unfold `objective`; the value is the displayed supremum by reflexivity.
/-- Evaluating the structured objective recovers the extended-real supremum of the saddle slice
`u ↦ Ψ(x, u)` on `Q₂`. -/
theorem objective_apply (problem : StructuredObjectiveModel E₁ E₂) (x : problem.primalSet) :
    problem.objective x =
      sSup (Set.range fun u : problem.dualSet ↦ (problem.saddleFunction x u : EReal)) :=
  sorry

/-- The primal optimal value attached to a structured objective model, encoded as the infimum of
the objective values on `Q₁`, taken in `EReal` so empty or unbounded-below outer problems are
represented faithfully. This is the canonical value denoted `f^*` in the textbook; when the
infimum is attained and finite, it agrees with the corresponding minimum value. -/
def primalOptimalValue (problem : StructuredObjectiveModel E₁ E₂) : EReal :=
  sInf (Set.range problem.objective)

/-- The adjoint objective `φ(u) = inf_{x ∈ Q₁} Ψ(x, u)`, valued in `EReal` so the infimum is
represented faithfully without extra attainment assumptions on the primal slice. -/
def adjointObjective (problem : StructuredObjectiveModel E₁ E₂) : problem.dualSet → EReal :=
  fun u ↦ sInf (Set.range fun x : problem.primalSet ↦ (problem.saddleFunction x u : EReal))

/-- The adjoint optimal value `f_*`, encoded as the supremum of the adjoint objective over
`Q₂`, taken in `EReal` so empty or unbounded-above dual problems are represented faithfully; when
the supremum is attained and finite, it agrees with the corresponding maximum value. -/
def adjointOptimalValue (problem : StructuredObjectiveModel E₁ E₂) : EReal :=
  sSup (Set.range problem.adjointObjective)

-- Proof sketch: unfold `primalOptimalValue`; then unfold `problem.objective`.
/-- The primal optimal value is the infimum of the saddle-point maximization
`x ↦ sup_{u ∈ Q₂} Ψ(x, u)`. Under additional attainment or compactness hypotheses, this agrees
with the textbook minimum formula. -/
theorem primalOptimalValue_eq_saddle_form (problem : StructuredObjectiveModel E₁ E₂) :
    problem.primalOptimalValue =
      sInf (Set.range fun x : problem.primalSet ↦
        sSup (Set.range fun u : problem.dualSet ↦ (problem.saddleFunction x u : EReal))) :=
  sorry

-- Proof sketch: unfold `adjointObjective`; the formula is the defining infimum of the saddle slice.
/-- Evaluating the adjoint objective recovers the extended-real infimum of the saddle slice
`x ↦ Ψ(x, u)` on `Q₁`. -/
theorem adjointObjective_apply (problem : StructuredObjectiveModel E₁ E₂)
    (u : problem.dualSet) :
    problem.adjointObjective u =
      sInf (Set.range fun x : problem.primalSet ↦ (problem.saddleFunction x u : EReal)) :=
  sorry

-- Proof sketch: unfold `adjointOptimalValue`; the statement is the defining equality.
/-- Expanding `adjointOptimalValue` gives the supremum of the adjoint objective on `Q₂`. -/
theorem adjointOptimalValue_def (problem : StructuredObjectiveModel E₁ E₂) :
    problem.adjointOptimalValue = sSup (Set.range problem.adjointObjective) :=
  sorry

end StructuredObjectiveModel

end

/-! ### Lemma_6_6 (from Chap06) -/
universe u v

/-
Lemma 6.6 lies in the chapter's excessive-gap/error-bound domain.

Sampled owner-style declarations:
- `raw_duality_gap_le_excessive_gap_budget` in `Lemma_6_2_1`, the chapter owner for the budget
  bound on the raw duality gap;
- `IsLeast` and `IsGreatest`, the canonical order-theoretic owners for attained primal minima and
  dual maxima;
- the source-facing split error bounds in `Lemma_6_2_1`, which already separate the raw-gap bridge
  from the order-theoretic optimality consequences.

Best owner abstraction:
- source-facing: the combined primal/dual error estimate at an excessive-gap pair;
- core/canonical: `raw_duality_gap_le_excessive_gap_budget` together with `IsLeast` and
  `IsGreatest`;
- bridge/view: bundling the two error terms into the interval statement for
  `max (f xBar - fStar) (fStar - φ uBar)`.

Primitive data:
- attained primal/dual optimal values `h_primal` and `h_dual`;
- the local smoothing bounds at the current pair `(xBar, uBar)`;
- the chapter excessive-gap certificate at the current pair.

Derived API:
- the raw duality-gap budget bound;
- the separate primal and dual error bounds against the raw gap;
- the final `Set.Icc` statement for their maximum.

The previous version encoded the local smoothing bounds via extra primitive data
`d₁`, `d₂`, `xOf`, `uOf`, `h_D₁`, `h_D₂`, and defining equations, even though the theorem only
uses the resulting inequalities at `xBar` and `uBar`. This refinement keeps the source-facing
combined conclusion while moving the statement to the canonical owner-level inputs.
-/
-- Proof sketch: apply `raw_duality_gap_le_excessive_gap_budget` to the two local smoothing bounds
-- and the excessive-gap certificate to control `f xBar - φ uBar` by `μ₁ D₁ + μ₂ D₂`. The attained
-- primal minimum and dual maximum give `φ uBar ≤ fStar ≤ f xBar`, so both
-- `f xBar - fStar` and `fStar - φ uBar` are nonnegative and bounded above by the raw duality gap.
/-- Lemma 6.6: if the primal value `fStar` is the minimum of `f` on `Q₁`, the same value is the
maximum of `φ` on `Q₂`, and the local smoothing bounds together with the excessive-gap certificate
hold at `xBar ∈ Q₁` and `uBar ∈ Q₂`, then the primal and dual errors are both controlled by the
raw duality gap, which is at most `μ₁ D₁ + μ₂ D₂`. -/
theorem excessive_gap_bounds_primal_dual_errors
    {X : Type u} {U : Type v}
    {Q₁ : Set X} {Q₂ : Set U}
    {f fμ₂ : X → ℝ} {φ φμ₁ : U → ℝ}
    {xBar : X} {uBar : U}
    {fStar D₁ D₂ μ₁ μ₂ : ℝ}
    (h_primal : IsLeast (f '' Q₁) fStar)
    (h_dual : IsGreatest (φ '' Q₂) fStar)
    (hfμ₂_lower : f xBar - μ₂ * D₂ ≤ fμ₂ xBar)
    (hφμ₁_upper : φμ₁ uBar ≤ φ uBar + μ₁ * D₁)
    (hxBar : xBar ∈ Q₁)
    (huBar : uBar ∈ Q₂)
    (hexcessive_gap :
      satisfiesExcessiveGapCondition Q₁ Q₂ fμ₂ φμ₁ ⟨xBar, hxBar⟩ ⟨uBar, huBar⟩) :
    max (f xBar - fStar) (fStar - φ uBar) ∈ Set.Icc 0 (f xBar - φ uBar) ∧
      f xBar - φ uBar ≤ μ₁ * D₁ + μ₂ * D₂ := by
  let xBarQ : Q₁ := ⟨xBar, hxBar⟩
  let uBarQ : Q₂ := ⟨uBar, huBar⟩
  have hfμ₂_lower' : f xBarQ - μ₂ * D₂ ≤ fμ₂ xBarQ := by
    simpa [xBarQ] using hfμ₂_lower
  have hφμ₁_upper' : φμ₁ uBarQ ≤ φ uBarQ + μ₁ * D₁ := by
    simpa [uBarQ] using hφμ₁_upper
  have hexcessive_gap' :
      satisfiesExcessiveGapCondition Q₁ Q₂ fμ₂ φμ₁ xBarQ uBarQ := by
    simpa [xBarQ, uBarQ] using hexcessive_gap
  have hraw_gap :
      f xBar - φ uBar ≤ μ₁ * D₁ + μ₂ * D₂ :=
    by
      simpa [xBarQ, uBarQ] using
        (raw_duality_gap_le_excessive_gap_budget hfμ₂_lower' hφμ₁_upper' hexcessive_gap')
  have hφ_le_fStar : φ uBar ≤ fStar :=
    h_dual.2 (Set.mem_image_of_mem φ huBar)
  have hfStar_le_f : fStar ≤ f xBar :=
    h_primal.2 (Set.mem_image_of_mem f hxBar)
  have hprimal_nonneg : 0 ≤ f xBar - fStar :=
    sub_nonneg.mpr hfStar_le_f
  have hprimal_le_raw_gap : f xBar - fStar ≤ f xBar - φ uBar :=
    sub_le_sub_left hφ_le_fStar (f xBar)
  have hdual_nonneg : 0 ≤ fStar - φ uBar :=
    sub_nonneg.mpr hφ_le_fStar
  have hdual_le_raw_gap : fStar - φ uBar ≤ f xBar - φ uBar :=
    sub_le_sub_right hfStar_le_f (φ uBar)
  have hmax_nonneg : 0 ≤ max (f xBar - fStar) (fStar - φ uBar) :=
    le_trans hprimal_nonneg (le_max_left _ _)
  have hmax_le_raw_gap :
      max (f xBar - fStar) (fStar - φ uBar) ≤ f xBar - φ uBar :=
    max_le_iff.mpr ⟨hprimal_le_raw_gap, hdual_le_raw_gap⟩
  exact ⟨Set.mem_Icc.mpr ⟨hmax_nonneg, hmax_le_raw_gap⟩, hraw_gap⟩

/-! ### Proposition_6_6 (from Chap06) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Proposition 6.6 lies in the convex dual-smoothing uniqueness domain.

Sampled owner-style declarations:
- mathlib `IsMaxOn` and `isMaxOn_iff`, the canonical maximizer owner and its textbook expansion;
- mathlib `StrongConvexOn`, the canonical owner for the displayed `1`-strong convexity estimate;
- mathlib `StrongConvexOn.strictConvexOn`, the passage from strong convexity to strict convexity;
- mathlib `StrictConcaveOn.eq_of_isMaxOn`, the canonical uniqueness theorem for maximizers of a
  strictly concave function.

Best owner abstraction:
- source-facing: uniqueness of a feasible maximizer of the regularized dual maximand;
- core/canonical: `u ∈ Q₂`, `IsMaxOn (...) Q₂ u`, and `StrongConvexOn Q₂ 1 d₂`;
- bridge/view: the derived strict concavity of `u ↦ ℓ u - φ u - μ * d₂ u` on `Q₂`.

Primitive data:
- the feasible set `Q₂`;
- the linear functional `ℓ`;
- the dual penalty `φ`;
- the prox term `d₂`;
- the positivity hypothesis `0 < μ`;
- the convexity hypothesis `ConvexOn ℝ Q₂ φ`;
- the strong-convexity hypothesis `StrongConvexOn Q₂ 1 d₂`.

Derived API:
- the feasible-maximizer hypotheses `u ∈ Q₂`, `v ∈ Q₂`, `IsMaxOn (...) Q₂ u`,
  and `IsMaxOn (...) Q₂ v`;
- uniqueness via `StrictConcaveOn.eq_of_isMaxOn`.

Source/core/bridge triage:
- source-facing: `smoothed_maximizer_unique`;
- core/canonical: `IsMaxOn` and `StrongConvexOn`;
- bridge/view: strict concavity of the regularized maximand.

The previous file duplicated the canonical maximizer owner by introducing the local wrapper
`IsOptimalSolutionOn`, and it restated the strong-convexity owner as a raw Jensen inequality.
This refinement deletes that parallel API and states the proposition directly through the
canonical owners already used across the chapter and mathlib.
-/

-- Proof sketch: `StrongConvexOn Q₂ 1 d₂` makes `u ↦ -μ * d₂ u` strictly concave on `Q₂` when
-- `μ > 0`, the affine term `ℓ` is both convex and concave, and `-φ` is concave because `φ` is
-- convex. Hence the regularized maximand is strictly concave on `Q₂`, and
-- `StrictConcaveOn.eq_of_isMaxOn` shows that two feasible maximizers coincide.
/-- Proposition 6.6: if `\hat φ` is convex on `Q₂`, `d₂` is `1`-strongly convex on `Q₂`, and
`μ > 0`, then the maximization problem
`max_{u ∈ Q₂} {ℓ(u) - \hat φ(u) - μ d₂(u)}` has at most one feasible maximizer. In particular,
whenever the smoothed maximizer exists, it is uniquely defined. -/
theorem smoothed_maximizer_unique
    {Q₂ : Set E} (ℓ : E →L[ℝ] ℝ) {d₂ φ : E → ℝ}
    (hφ : ConvexOn ℝ Q₂ φ) (hd₂ : StrongConvexOn Q₂ 1 d₂) {μ : ℝ} (hμ : 0 < μ)
    {u v : E} (hu_mem : u ∈ Q₂) (hv_mem : v ∈ Q₂)
    (hu : IsMaxOn (fun w ↦ ℓ w - φ w - μ * d₂ w) Q₂ u)
    (hv : IsMaxOn (fun w ↦ ℓ w - φ w - μ * d₂ w) Q₂ v) :
    u = v := by
  have hμd₂ : StrictConvexOn ℝ Q₂ (fun w ↦ μ * d₂ w) := by
    have hd₂_strict : StrictConvexOn ℝ Q₂ d₂ :=
      hd₂.strictConvexOn zero_lt_one
    refine ⟨hd₂.1, ?_⟩
    intro x hx y hy hxy a b ha hb hab
    have hstrict := hd₂_strict.2 hx hy hxy ha hb hab
    calc
      μ * d₂ (a • x + b • y) < μ * (a • d₂ x + b • d₂ y) :=
        mul_lt_mul_of_pos_left hstrict hμ
      _ = a • (μ * d₂ x) + b • (μ * d₂ y) := by ring
  have hstrict :
      StrictConcaveOn ℝ Q₂ (fun w ↦ ℓ w - φ w - μ * d₂ w) :=
    (ℓ.toLinearMap.concaveOn hd₂.1).sub hφ |>.sub_strictConvexOn hμd₂
  exact hstrict.eq_of_isMaxOn hu hv hu_mem hv_mem

end

/-! ### Theorem_6_6 (from Chap06) -/
noncomputable section

open scoped ConstrainedArgmin

universe u v

section

variable {X : Type u} {U : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
variable {Q₁ : Set X} {Q₂ : Set U}
variable (hQ₁ : Convex ℝ Q₁) (hQ₂ : Convex ℝ Q₂)
variable {A : X →L[ℝ] StrongDual ℝ U}
variable {hatf : X → ℝ} {hatφ : U → ℝ} {d₁ : X → ℝ} {d₂ : U → ℝ}
variable (xμ : ℝ → U → X)
variable
    (hxμ :
      ∀ μ : ℝ, ∀ u : U,
        xμ μ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ u))
variable (uμ : ℝ → X → U)
variable
    (huμ :
      ∀ μ : ℝ, ∀ x : X, x ∈ Q₁ →
        uμ μ x ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ x)
variable (x₀ : Q₂ → Q₁) (V : Q₂ → Q₂)
variable {fμ₂ : ℝ → X → ℝ} {φμ₁ : ℝ → U → ℝ}
variable {fμ₂_zero : ℝ → Q₁ → ℝ} {φ_zero : Q₂ → ℝ}
variable {initialPrimalSmoothing initialDualSmoothing : ℝ}
variable (initialState : Q₁ × Q₂)

/- Theorem 6.6 lies in the chapter's alternating excessive-gap propagation domain.

Primary mathematical domain:
- parity-split propagation of the Chapter 6 excessive-gap certificate along the iterates generated
  by Algorithm 6.3.

Sampled owner-style declarations:
- `algorithm_6_3_step_size` in `Chap06/Algorithm_6_3`, the Algorithm 6.3 owner of the step-size
  sequence `τ_k = 2 / (k + 3)`;
- `algorithm_6_3_primal_smoothing` and `algorithm_6_3_dual_smoothing` in
  `Chap06/Algorithm_6_3`, the source-facing owners of the smoothing recursions
  `μ₁,k`, `μ₂,k`;
- `alternatingExcessiveGapPrimalIterate` and `alternatingExcessiveGapDualIterate` in
  `Chap06/Algorithm_6_3`, the source-facing owners of the actual Algorithm 6.3 iterates;
- `satisfiesExcessiveGapCondition` in `Chap06/Theorem_6_4` and
  `satisfiesExcessiveGapConditionWithMu1Zero` in `Chap06/Definition_6_39`, the chapter owners of
  the two certificate layers used by the even and odd updates.

Best owner abstraction:
- source-facing: the actual Algorithm 6.3 iterate and smoothing sequences;
- core/canonical: the Algorithm 6.3 recursion lemmas from `Chap06/Algorithm_6_3` and the two
  Chapter 6 excessive-gap certificate predicates;
- bridge/view: the induction theorem below, which turns the one-step even and odd propagation
  rules into a certificate for every iterate.

Primitive data:
- the initial state `( \bar x₀, \bar u₀ )`;
- the initial smoothing parameters `μ₁,0`, `μ₂,0`;
- the Chapter 6 even and odd update-owner data;
- the stagewise even-step and odd-step certificate propagation rules.

Derived API:
- the general excessive-gap certificate for every iterate pair of Algorithm 6.3.

The previous version restated this theorem for arbitrary iterate and smoothing sequences satisfying
the same parity split and kept local duplicate certificate aliases. This file now consumes the
actual Algorithm 6.3 owners together with the chapter certificate owners directly, so the chapter
has one public recursion surface instead of generic duplicates.
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

-- Proof sketch: argue by induction on `k`. The base case is `hzero`. For the inductive step,
-- split into the parity of `k`. On even steps, use the canonical Algorithm 6.3 recurrence lemmas
-- for `x̄` and `ū`, then apply `heven_step`. On odd steps, pass from the general certificate to
-- the `μ₁ = 0` certificate via `hodd_source`, propagate it across the odd update with
-- `hodd_step`, rewrite the iterate `(k + 1)` using the canonical Algorithm 6.3 odd-step
-- recurrence lemmas, and return to the general certificate using `hodd_target`.
/-- Theorem 6.6: if the initial Algorithm 6.3 iterate pair satisfies the Chapter 6 excessive-gap
condition, if each even step preserves the general excessive-gap certificate, and if each odd step
passes through the `μ₁ = 0` excessive-gap certificate before returning to the general one, then
every Algorithm 6.3 iterate pair satisfies the general excessive-gap condition. -/
theorem algorithm_6_3_iterates_satisfy_excessive_gap_condition
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
    (k : ℕ) :
    satisfiesExcessiveGapCondition
      Q₁
      Q₂
      (fμ₂ (μ₂ k))
      (φμ₁ (μ₁ k))
      (x̄ k)
      (ū k) := sorry

end
