import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_6_2_3 (from Chap06) -/
noncomputable section

open scoped ConstrainedArgmin

universe u v

/- Theorem 6.2.3 lies in the Chapter 6 excessive-gap / adjoint-gradient update domain.

Mandatory domain-style sampling before refinement:
- `satisfiesExcessiveGapConditionWithMu1Zero` in `Chap06/Definition_6_38`, the `μ₁ = 0`
  excessive-gap owner already built on the chapter certificate owner;
- `smoothedPrimalObjective`, `smoothedPrimalObjectiveArgmax`, and
  `smoothedDualObjectiveMinimand` in `Chap06/Definition_6_30` and `Chap06/Definition_6_32`, the
  Chapter 6 owners for the smoothed primal value, the dual oracle argmax set, and the
  zero-smoothing primal minimizer subproblem;
- `IsAdjointGradientMappingOn` in `Chap06/Definition_6_39`, the source-facing owner for the
  feasible adjoint gradient update map;
- `tau_mem_Icc` in `Chap06/Theorem_6_4`, the chapter helper turning `0 < τ < 1` into the
  canonical convex-combination parameter `τ ∈ Set.Icc (0 : ℝ) 1`;
- `predicted_primal_point`, `updated_dual_point`, and `updated_primal_point` in
  `Chap06/Theorem_6_4`, whose source-facing update-owner shape matches the odd-step updates here.

Best owner abstraction:
- source-facing: the odd-step update points `\hat u`, `\bar x_+`, and `\bar u_+` together with
  preservation of `satisfiesExcessiveGapConditionWithMu1Zero`;
- core/canonical: `satisfiesExcessiveGapConditionWithMu1Zero`, `smoothedPrimalObjective`,
  `smoothedDualObjective`, `smoothedPrimalObjectiveArgmax`,
  `smoothedDualObjectiveMinimand`, `IsAdjointGradientMappingOn`, and the convex-combination owner
  `τ ∈ Set.Icc (0 : ℝ) 1`;
- bridge/view: the subtype-valued update maps below, which keep the updated points feasible
  without introducing a second certificate owner.

Primitive data:
- the convex feasible sets `Q₁`, `Q₂`;
- the Chapter 6 zero-smoothing primal minimizer and positive-smoothing dual argmax data selecting
  `x₀`, the fixed oracle `u_{μ₂}`, and the adjoint gradient map `V`;
- the current feasible pair `(xBar, uBar)` and the step size `τ`.

Derived API:
- the reduced smoothing parameter `μ₂⁺ = (1 - τ) μ₂` from the positive source parameter
  `μ₂ : {μ : ℝ // 0 < μ}`;
- the feasible update points `predictedDualPoint`, `updatedPrimalPoint`, and `updatedDualPoint`;
- the preserved `μ₁ = 0` excessive-gap certificate.

The previous file exposed separate public membership lemmas whose only role was to build the
subtype-valued update points, and it parameterized the odd-step updates by an artificial family
`Q₁ → ℝ → Q₂` instead of the fixed source oracle `u_{μ₂}`. The refinement keeps the source-facing
update owners, reuses the chapter's `τ ∈ Set.Icc` owner shape from `Theorem_6_4`, and states the
main theorem on the actual Chapter 6 primal and dual value owners rather than on arbitrary raw
functions.
-/

namespace StronglyConvexDualUpdate

section Updates

section DualUpdates

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-- The reduced dual smoothing parameter `μ₂⁺ = (1 - τ) μ₂`. -/
def reducedDualSmoothing (μ₂ τ : ℝ) : ℝ :=
  (1 - τ) * μ₂

/-- Expanding `reducedDualSmoothing` recovers the formula `μ₂⁺ = (1 - τ) μ₂`. -/
theorem reducedDualSmoothing_def (μ₂ τ : ℝ) :
    reducedDualSmoothing μ₂ τ = (1 - τ) * μ₂ :=
  rfl

/-- The intermediate dual point `\hat u = (1 - τ) \bar u + τ u_{μ₂}(\bar x)`. -/
def predictedDualPoint
    {Q₁ : Set E₁} {Q₂ : Set E₂}
    (hQ₂ : Convex ℝ Q₂) (uμ₂ : Q₁ → Q₂)
    (xBar : Q₁) (uBar : Q₂) (τ : ℝ)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) : Q₂ :=
  ⟨(1 - τ) • (uBar : E₂) + τ • (uμ₂ xBar : E₂),
    by
      have hu :
          (uBar : E₂) + τ • ((uμ₂ xBar : Q₂) - (uBar : E₂)) ∈ Q₂ :=
        hQ₂.add_smul_sub_mem uBar.property (uμ₂ xBar).property hτ
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, smul_add, add_smul] using hu⟩

/-- Expanding `predictedDualPoint` recovers
`\hat u = (1 - τ) \bar u + τ u_{μ₂}(\bar x)`. -/
@[simp] theorem predictedDualPoint_val
    {Q₁ : Set E₁} {Q₂ : Set E₂}
    (hQ₂ : Convex ℝ Q₂) (uμ₂ : Q₁ → Q₂)
    (xBar : Q₁) (uBar : Q₂) (τ : ℝ)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    (predictedDualPoint hQ₂ uμ₂ xBar uBar τ hτ : E₂) =
      (1 - τ) • (uBar : E₂) + τ • (uμ₂ xBar : E₂) :=
  rfl

/-- The updated dual point `\bar u_+ = V(\hat u)`. -/
def updatedDualPoint
    {Q₁ : Set E₁} {Q₂ : Set E₂}
    (hQ₂ : Convex ℝ Q₂) (uμ₂ : Q₁ → Q₂) (V : Q₂ → Q₂)
    (xBar : Q₁) (uBar : Q₂) (τ : ℝ)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) : Q₂ :=
  V (predictedDualPoint hQ₂ uμ₂ xBar uBar τ hτ)

/-- Expanding `updatedDualPoint` recovers `\bar u_+ = V(\hat u)`. -/
@[simp] theorem updatedDualPoint_val
    {Q₁ : Set E₁} {Q₂ : Set E₂}
    (hQ₂ : Convex ℝ Q₂) (uμ₂ : Q₁ → Q₂) (V : Q₂ → Q₂)
    (xBar : Q₁) (uBar : Q₂) (τ : ℝ)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    (updatedDualPoint hQ₂ uμ₂ V xBar uBar τ hτ : E₂) =
      V (predictedDualPoint hQ₂ uμ₂ xBar uBar τ hτ) :=
  rfl

end DualUpdates

section PrimalUpdate

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-- The updated primal point `\bar x_+ = (1 - τ) \bar x + τ x₀(\hat u)`. -/
def updatedPrimalPoint
    {Q₁ : Set E₁} {Q₂ : Set E₂}
    (hQ₁ : Convex ℝ Q₁) (hQ₂ : Convex ℝ Q₂)
    (x₀ : Q₂ → Q₁) (uμ₂ : Q₁ → Q₂)
    (xBar : Q₁) (uBar : Q₂) (τ : ℝ)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) : Q₁ :=
  ⟨(1 - τ) • (xBar : E₁) +
      τ •
        (x₀ (predictedDualPoint hQ₂ uμ₂ xBar uBar τ hτ) : E₁),
    by
      let uHat := predictedDualPoint hQ₂ uμ₂ xBar uBar τ hτ
      have hx :
          (xBar : E₁) + τ • ((x₀ uHat : Q₁) - (xBar : E₁)) ∈ Q₁ :=
        hQ₁.add_smul_sub_mem xBar.property (x₀ uHat).property hτ
      simpa [uHat, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, smul_add, add_smul]
        using hx⟩

/-- Expanding `updatedPrimalPoint` recovers
`\bar x_+ = (1 - τ) \bar x + τ x₀(\hat u)`. -/
@[simp] theorem updatedPrimalPoint_val
    {Q₁ : Set E₁} {Q₂ : Set E₂}
    (hQ₁ : Convex ℝ Q₁) (hQ₂ : Convex ℝ Q₂)
    (x₀ : Q₂ → Q₁) (uμ₂ : Q₁ → Q₂)
    (xBar : Q₁) (uBar : Q₂) (τ : ℝ)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    (updatedPrimalPoint hQ₁ hQ₂ x₀ uμ₂ xBar uBar τ hτ : E₁) =
      (1 - τ) • (xBar : E₁) +
        τ • (x₀ (predictedDualPoint hQ₂ uμ₂ xBar uBar τ hτ) : E₁) :=
  rfl

end PrimalUpdate

end Updates

section Theorem

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

/-- A feasible-set endomorphism is an adjoint gradient mapping when it selects, at each feasible
base point `u`, a maximizer of the quadratic model
`v ↦ ⟪∇ φ(u), v - u⟫ - (Lphi / 2) * ‖v - u‖²` on `Q₂`. -/
def IsAdjointGradientMappingOn
    (Q₂ : Set E₂) (φ : E₂ → ℝ) (Lphi : ℝ) (V : Q₂ → Q₂) : Prop :=
  ∀ u : Q₂,
    IsMaxOn
      (fun v : E₂ ↦
        inner ℝ (gradientWithin φ Q₂ (u : E₂)) (v - (u : E₂)) -
          (Lphi / 2) * ‖v - (u : E₂)‖ ^ (2 : ℕ))
      Q₂
      (V u : E₂)

-- Proof sketch: use convexity of `Q₂` and `Q₁` to keep `\hat u` and `\bar x_+` feasible, apply
-- the `μ₁ = 0` excessive-gap hypothesis for the actual Chapter 6 owners
-- `smoothedPrimalObjective` and `smoothedDualObjective`, use the canonical `argmin` and `argmax`
-- hypotheses for `x₀` and `u_{μ₂}`, and then use the source-facing owner
-- `IsAdjointGradientMappingOn` for the finite-real-part dual objective to see that
-- `\bar u_+ = V(\hat u)` lies in the canonical adjoint-gradient argmax set at `\hat u`,
-- together with
-- the step-size bound
-- `τ^2 / (1 - τ) ≤ μ₂ / L₂(φ)` to recover the updated inequality at smoothing parameter
-- `μ₂⁺ = (1 - τ) μ₂`.
/-- Theorem 6.2.3: if `(\bar x, \bar u)` satisfies the excessive-gap condition with `μ₁ = 0`
for the actual Chapter 6 smoothed primal owner `smoothedPrimalObjective` and the zero-smoothing
dual owner `smoothedDualObjective`, if `x₀` selects the canonical zero-smoothing primal minimizer
at every feasible dual point, if `u_{μ₂}` selects the canonical argmax owner of the smoothed
primal maximand at the positive smoothing parameter `μ₂`, if
`τ ∈ (0, 1)` satisfies `τ^2 / (1 - τ) ≤ μ₂ / L₂(φ)`, and if `V : Q₂ → Q₂` is an adjoint
gradient mapping on the finite-real-part dual objective, then the updated pair
`\bar x_+ = (1 - τ) \bar x + τ x₀(\hat u)` and `\bar u_+` again satisfies the excessive-gap
condition with `μ₁ = 0` and smoothing parameter `μ₂⁺ = (1 - τ) μ₂`. -/
theorem excessive_gap_condition_preserved
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {Q₂ : Set E₂}
    (hQ₁ : Convex ℝ Q₁) (hQ₂ : Convex ℝ Q₂)
    {hatf : E₁ → ℝ} {hatφ d₂ : E₂ → ℝ}
    (x₀ : Q₂ → Q₁) (uμ₂ : Q₁ → Q₂) (V : Q₂ → Q₂)
    {xBar : Q₁} {uBar : Q₂} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ} {L₂φ : NNReal}
    (hgap :
      satisfiesExcessiveGapConditionWithMu1Zero
        (fun x : Q₁ ↦ smoothedPrimalObjective A Q₂ hatf hatφ d₂ (μ₂ : ℝ) x)
        (fun u : Q₂ ↦
          extendedRealRealPart
            (smoothedDualObjective A Q₁ hatf hatφ (fun _ : E₁ ↦ 0) 0) u)
        xBar
        uBar)
    (hx₀ :
      ∀ u : Q₂,
        (x₀ u : E₁) ∈
          argmin[Q₁]
            (smoothedDualObjectiveMinimand A hatf (fun _ : E₁ ↦ 0) 0 u))
    (huμ₂ :
      ∀ x : Q₁,
        (uμ₂ x : E₂) ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ (μ₂ : ℝ) x)
    (hτ : 0 < τ) (hτ_lt : τ < 1)
    (hstep : τ ^ (2 : ℕ) / (1 - τ) ≤ (μ₂ : ℝ) / (L₂φ : ℝ))
    (hV :
      IsAdjointGradientMappingOn
        Q₂
        (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ (fun _ : E₁ ↦ 0) 0))
        (L₂φ : ℝ)
        V) :
    satisfiesExcessiveGapConditionWithMu1Zero
      (fun x : Q₁ ↦
        smoothedPrimalObjective A Q₂ hatf hatφ d₂ (reducedDualSmoothing μ₂ τ) x)
      (fun u : Q₂ ↦
        extendedRealRealPart
          (smoothedDualObjective A Q₁ hatf hatφ (fun _ : E₁ ↦ 0) 0) u)
      (updatedPrimalPoint hQ₁ hQ₂ x₀ uμ₂ xBar uBar τ
        (tau_mem_Icc hτ hτ_lt))
      (updatedDualPoint hQ₂ uμ₂ V xBar uBar τ
        (tau_mem_Icc hτ hτ_lt)) := sorry

end Theorem

end StronglyConvexDualUpdate

/-! ### Lemma_6_2_4 (from Chap06) -/
-- Proof sketch: the owner recurrence on `switching_parameters α` scales both coordinates at once.
-- Then inspect the appropriate coordinate according to the parity of `k`, using the owner
-- theorems from `Definition_6_36` to read off `α_{k+1}` and `α_{k-1}`.
/-- Lemma 6.2.4: if the switching-parameter sequence attached to `α_k` satisfies the contraction
rule `parameters_{k+1} = (1 - τ_k) parameters_k`, then for every `k ≥ 0`,
`α_{k+1} = (1 - τ_k) α_{k-1}`. -/
theorem alpha_succ_eq_one_sub_tau_mul_pred_of_alternating_scalar_updates
    (α : Set.Ici (-1 : ℤ) → ℝ) (τ : ℕ → ℝ)
    (hparameters :
      ∀ k : ℕ, switching_parameters α (k + 1) = (1 - τ k) • switching_parameters α k)
    (k : ℕ) :
    α (switching_parameters_succ_index k) =
      (1 - τ k) * α (switching_parameters_pred_index k) := sorry

/-! ### Theorem_6_2_4 (from Chap06) -/
universe u v

section

variable {X : Type u} {U : Type v}
  {f : X → ℝ} {φ : U → ℝ}
  {fμ₂ : ℝ → X → ℝ}
  {barx : ℕ → X} {baru : ℕ → U}
  {L2phi D2 : ℝ}

/- Theorem 6.2.4 lies in the chapter's excessive-gap / smoothing-rate domain.

Mandatory domain-style sampling before refinement:
- `satisfiesExcessiveGapCondition` in `Chap06/Definition_6_34`, the chapter owner for the
  stagewise smoothed inequality;
- `raw_duality_gap_le_excessive_gap_budget` in `Chap06/Lemma_6_2_1`, the canonical bridge from a
  smoothed certificate plus one-sided smoothing bounds to a raw primal-dual gap estimate;
- `satisfiesExcessiveGapConditionWithMu1Zero` in `Chap06/Definition_6_38`, the `μ₁ = 0`
  specialization of the same certificate owner;
- `scheme_6_2_37_primal_dual_gap_le_rate` in `Chap06/Theorem_6_8`, which later reuses the exact
  theorem below as the chapter owner for this rate statement.

Best owner abstraction:
- source-facing: the explicit primal-dual gap rate along scheme `(6.2.37)`;
- core/canonical: `raw_duality_gap_le_excessive_gap_budget` together with the Chapter 6
  excessive-gap owner specialized to `μ₁ = 0`;
- bridge/view: the specialization below where the smoothed dual value is the unsmoothed dual
  objective `φ` and the smoothing parameter is fixed to
  `μ₂,k = 4 L₂(φ) / ((k + 1) (k + 2))`.

Primitive data:
- the lower smoothing estimate `f x - μ₂ D₂ ≤ f_{μ₂}(x)`;
- the stagewise certificate `f_{μ₂,k}(\bar x_k) ≤ φ(\bar u_k)`.

Derived API:
- the explicit rate
  `f(\bar x_k) - φ(\bar u_k) ≤ 4 L₂(φ) D₂ / ((k + 1) (k + 2))`.

Source/core/bridge triage:
- source-facing: the theorem statement below;
- core/canonical: `satisfiesExcessiveGapCondition` and
  `raw_duality_gap_le_excessive_gap_budget`;
- bridge/view: the `μ₁ = 0` specialization at the stagewise smoothing parameter.

The previous file kept the theorem as a free-standing arithmetic statement with a placeholder
proof. The public statement already matches the source, so the refinement keeps that source-facing
surface and reuses the chapter's canonical excessive-gap bridge in the proof instead of repeating
the same duality-gap algebra locally.
-/

-- Proof sketch: for each `k`, evaluate the lower smoothing estimate
-- `f x ≤ f_{μ₂} x + μ₂ D₂` at
-- `μ₂ = 4 L₂(φ) / ((k + 1) (k + 2))` and `x = \bar x_k`, then combine it with the stagewise
-- scheme inequality `f_{μ₂}(\bar x_k) ≤ φ(\bar u_k)` from `(6.2.37)` and rearrange.
/-- Theorem 6.2.4: assume that problem `(6.2.1)` satisfies Assumption `6.2.1`, and let
`{(\bar x_k, \bar u_k)}_{k \ge 0}` be the sequence generated by scheme `(6.2.37)`. If at each
stage `k` the scheme yields the smoothed inequality
`f_{μ₂,k}(\bar x_k) ≤ φ(\bar u_k)` with
`μ₂,k = 4 L₂(φ) / ((k + 1) (k + 2))`, and if the smoothing family satisfies
`f(x) - μ₂ D₂ ≤ f_{μ₂}(x)` for every `μ₂` and `x`, then
`f(\bar x_k) - φ(\bar u_k) ≤ 4 L₂(φ) D₂ / ((k + 1) (k + 2))` for every integer `k ≥ 0`. -/
theorem scheme_6_2_37_primal_dual_gap_le_rate
    (happrox : ∀ μ₂ x, f x - μ₂ * D2 ≤ fμ₂ μ₂ x)
    (hscheme :
      ∀ k : ℕ,
        fμ₂ ((4 * L2phi) / (((k : ℝ) + 1) * ((k : ℝ) + 2))) (barx k) ≤ φ (baru k))
    (k : ℕ) :
    f (barx k) - φ (baru k) ≤
      (4 * L2phi * D2) / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := sorry

end

/-! ### Lemma_6_2_5 (from Chap06) -/
noncomputable section

open scoped ConstrainedArgmin ConvexAnalysis Gradient StrongConvex

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

/- Lemma 6.2.5 lies in the chapter's attained dual-objective / constrained-minimization domain.

Mandatory domain-style sampling before refinement:
- `smoothedDualObjectiveMinimand` and `smoothedDualObjective` in `Chap06/Proposition_6_25`, the
  chapter owners for the constrained `EReal` dual value and its primal slice;
- the canonical `argmin[Q₁]` owner surface for pointwise minimizer data;
- `StructuredObjectiveModel.adjointObjective` in `Chap06/Definition_6_6`, the more general
  chapter owner for the same dual-value construction;
- `StructuredObjectiveModel.adjointObjective_eq_of_isMinOn` in
  `Chap06/Text_6_1_2_Adjoint_Problem_Tractability_Caveat`, the attained-infimum bridge from the
  canonical owner to the textbook pointwise formula.

Best owner abstraction:
- source-facing: the unsmoothed dual objective from Lemma 6.2.5 and its selected minimizer
  surface;
- core/canonical: the zero-smoothing specialization
  `smoothedDualObjective A Q₁ hatf hatφ 0 0` together with
  `∀ u : E₂, x₀ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf 0 0 u)`;
- bridge/view: the vector-gradient formula obtained from the dual-valued owner through the Hilbert
  space Riesz equivalence.

Primitive data:
- the dual-valued linear map `A : E₁ →L[ℝ] StrongDual ℝ E₂`;
- the feasible set `Q₁`;
- the functions `hatf` and `hatφ`;
- a pointwise minimizer witness in the canonical argmin surface
  `∀ u : E₂, x₀ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf 0 0 u)`.

Derived API:
- the zero-smoothing dual owner `smoothedDualObjective A Q₁ hatf hatφ 0 0`;
- its effective-domain and gradient consequences below;
- the source-facing uniqueness, concavity, and Lipschitz-gradient statements of Lemma 6.2.5.

The previous version depended on a broken recall chain through `Definition_6_33` and used a
parallel selector wrapper that is not part of the available chapter API. This refinement keeps
only the actual zero-smoothing owners from `Proposition_6_25` together with the canonical
pointwise `argmin[Q₁]` surface.
-/

section OwnerLayer

/-- The minimizer of the zero-smoothing primal slice is unique when the primal smooth part
satisfies the chapter's source-facing strong-convexity owner `hatf ∈ 𝒮^0_σ(Q₁)`. -/
-- Proof sketch: `hhatf.strongConvexOn` gives the canonical owner `StrongConvexOn Q₁ σ hatf`,
-- which already includes convexity of `Q₁`; adding the affine term `x ↦ A x u` preserves
-- `σ`-strong convexity, and a strongly convex function has at most one minimizer.
theorem dualObjectiveMinimand_minimizer_unique
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) {Q₁ : Set E₁} {hatf : E₁ → ℝ} {σ : ℝ}
    (hhatf : hatf ∈ 𝒮^0_σ(Q₁))
    {u : E₂} {x y : E₁}
    (hx : IsMinOn (smoothedDualObjectiveMinimand A hatf 0 0 u) Q₁ x)
    (hy : IsMinOn (smoothedDualObjectiveMinimand A hatf 0 0 u) Q₁ y) :
    x = y := sorry

/- The source text states that `\hat φ` is concave, but with `φ = \tilde φ - \hat φ` and the
claimed concavity of `φ`, the sign-compatible assumption is that `\hat φ` is convex. The
statement skeleton below follows that sign convention. -/

/-- Lemma 6.2.5 (1): in owner form, if `\hat φ` is convex, then the finite real part of the
canonical zero-smoothing `EReal` dual objective is concave on its effective domain. -/
-- Proof sketch: `u ↦ (.mk Q₁ (smoothedDualObjectiveMinimand A hatf 0 0 u)).optimalValue` is the
-- infimum of affine functions of `u`, hence concave on the finite-value domain. The term
-- `-\hat φ` is concave because `\hat φ` is convex, so the sum remains concave.
theorem dualObjective_concave
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) {Q₁ : Set E₁} {hatf : E₁ → ℝ} {hatφ : E₂ → ℝ}
    (hhatφ_convex : ConvexOn ℝ Set.univ hatφ) :
    ConcaveOn ℝ (dom (smoothedDualObjective A Q₁ hatf hatφ 0 0))
      (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0)) := sorry

/-- The canonical zero-smoothing dual objective is finite everywhere, so its effective domain is
all of `E₂`. -/
-- Proof sketch: `smoothedDualObjective A Q₁ hatf hatφ 0 0` is defined by coercing a real-valued
-- expression into `EReal`, so every point lies in its effective domain.
theorem dualObjective_dom_eq_univ
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) {Q₁ : Set E₁} {hatf : E₁ → ℝ} {hatφ : E₂ → ℝ} :
    dom (smoothedDualObjective A Q₁ hatf hatφ 0 0) = Set.univ := sorry

end OwnerLayer

section GradientLayer

/-- Lemma 6.2.5 (2): under the same assumptions and differentiability of `\hat φ`, the
zero-smoothing dual objective has gradient
`-\nabla \hat φ(u) + (InnerProductSpace.toDual ℝ E₂).symm (A (x₀ u))` at every `u`, expressed on
the finite real part of the canonical `EReal` owner. -/
-- Proof sketch: `hhatf` supplies the chapter source-facing owner `hatf ∈ 𝒮^0_σ(Q₁)`, hence
-- uniqueness of the pointwise argmin selection, so Danskin's theorem identifies the gradient of
-- `\tilde φ` with the Riesz representative of `A (x₀ u)`. Subtract the gradient of the
-- differentiable term `\hat φ`.
theorem dualObjective_hasGradientAt
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {hatf : E₁ → ℝ} {hatφ : E₂ → ℝ}
    {x₀ : E₂ → E₁} {σ : ℝ}
    (hhatf : hatf ∈ 𝒮^0_σ(Q₁))
    (hhatφ_diff : Differentiable ℝ hatφ)
    (hx₀ : ∀ u : E₂, x₀ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf 0 0 u))
    (u : E₂) :
    HasGradientAt
      (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0))
      (-∇ hatφ u + (InnerProductSpace.toDual ℝ E₂).symm (A (x₀ u))) u := sorry

/-- Lemma 6.2.5 (3): in owner form, if `\hat φ` is differentiable and `∇ \hat φ` is Lipschitz with
constant `L₂(\hat φ)`, then the actual gradient of the finite real part of the canonical
zero-smoothing dual objective is Lipschitz with constant `(1 / σ) ‖A‖² + L₂(\hat φ)`. The
explicit vector-field formula remains the companion bridge theorem
`dualObjective_hasGradientAt`. -/
-- Proof sketch: `hhatφ_diff` supplies the primitive differentiability data needed for
-- `dualObjective_hasGradientAt` to identify the actual gradient field of
-- `extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0)` with the explicit source-side
-- formula `u ↦ -∇ hatφ u + (InnerProductSpace.toDual ℝ E₂).symm (A (x₀ u))`. Then compare the
-- first-order optimality conditions at two dual points, using `hhatf.mu_pos` and
-- `hhatf.strongConvexOn` for the positive modulus and canonical strong-convexity view, to bound
-- the selected dual term, and finally combine that bound with the assumed Lipschitz estimate for
-- `∇ hatφ`.
theorem dualObjective_gradient_lipschitz
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {hatf : E₁ → ℝ} {hatφ : E₂ → ℝ} {x₀ : E₂ → E₁}
    {σ : ℝ} {Lhatφ : NNReal}
    (hhatf : hatf ∈ 𝒮^0_σ(Q₁))
    (hx₀ : ∀ u : E₂, x₀ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf 0 0 u))
    (hhatφ_diff : Differentiable ℝ hatφ)
    (hhatφ_lipschitz : LipschitzWith Lhatφ (∇ hatφ)) :
    LipschitzWith
      (Lhatφ + Real.toNNReal ((1 / σ) * ‖A‖ ^ (2 : ℕ)))
      (∇ (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0))) := sorry

end GradientLayer

end

/-! ### Lemma_6_2_6 (from Chap06) -/
noncomputable section

open scoped ConstrainedArgmin Gradient

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

/- Lemma 6.2.6 lies in Chapter 6's attained dual-objective / linearization domain.

Mandatory domain-style sampling before refinement:
- `smoothedDualObjectiveMinimand` and `smoothedDualObjective` in `Chap06/Proposition_6_25`, the
  canonical Chapter 6 owner surface for the zero-smoothing dual slice used here;
- `smoothedDualObjective_argmin_unique_and_hasGradientWithinAt` in `Chap06/Proposition_6_25`, the
  local gradient owner for attained smoothed-dual slices;
- `StructuredObjectiveModel.adjointObjective` in `Chap06/Definition_6_6`, the more general
  chapter owner for the same dual value construction.

Best owner abstraction:
- source-facing: the linearization lower bound at a fixed dual point `uHat`, expressed through a
  primal argmin witness for the corresponding zero-smoothing slice;
- core/canonical: `smoothedDualObjective A Q₁ hatf hatφ 0 0` and
  `argmin[Q₁] (smoothedDualObjectiveMinimand A hatf 0 0 uHat)`;
- bridge/view: the displayed real-valued lower bound in the theorem below.

This file should not define or recall a second public owner for the unsmoothed dual value. The
refinement below therefore uses the chapter's zero-smoothing `smoothedDualObjective` surface
directly.
-/

/-- Lemma 6.2.6: for `u, \hat u ∈ Q₂`, if `xHat` solves the fixed-`\hat u` zero-smoothing primal
slice, then the affine linearization of the dual objective at `\hat u` dominates
`-\hat φ(u) + A xHat u + \hat f(xHat)`. -/
-- Proof sketch: expand the zero-smoothing smoothed-dual owner at `uHat`, use the argmin witness
-- `hxHat` for the attained primal slice, identify the dual gradient from `hdual_grad`, and apply
-- the first-order convexity inequality for `hatφ` on `Q₂`.
theorem dualObjective_linearization_lower_bound
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) {Q₁ : Set E₁} {Q₂ : Set E₂}
    {hatf : E₁ → ℝ} {hatφ : E₂ → ℝ}
    (hhatφ_convex : ConvexOn ℝ Q₂ hatφ)
    {u uHat : E₂} {xHat : E₁}
    (hxHat : xHat ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf 0 0 uHat))
    (hu : u ∈ Q₂) (huHat : uHat ∈ Q₂)
    (hhatφ_grad : HasGradientAt hatφ (∇ hatφ uHat) uHat)
    (hdual_grad :
      HasGradientAt
        (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0))
        (-∇ hatφ uHat + (InnerProductSpace.toDual ℝ E₂).symm (A xHat)) uHat) :
    extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0) uHat +
      inner ℝ (∇ (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ 0 0)) uHat)
        (u - uHat) ≥
        -hatφ u + A xHat u + hatf xHat := sorry

end

/-! ### Lemma_6_2_7 (from Chap06) -/
universe u v

/- Lemma 6.2.7 lies in the Chapter 6 excessive-gap / one-sided smoothing domain.

Mandatory domain-style sampling before refinement:
- `satisfiesExcessiveGapCondition` in `Chap06/Theorem_6_4`, the chapter owner for the
  excessive-gap certificate `fμ₂ xBar ≤ φμ₁ uBar`;
- `raw_duality_gap_le_excessive_gap_budget` in `Chap06/Lemma_6_2_1`, the owner theorem turning a
  local smoothing lower bound and an excessive-gap certificate into a raw-gap upper bound;
- `satisfiesExcessiveGapConditionWithMu1Zero` in `Chap06/Definition_6_38`, the `μ₁ = 0`
  specialization already built on the same owner abstraction.

Best owner abstraction:
- source-facing: the raw primal-dual gap bound at one pair `(xBar, uBar)`;
- core/canonical: `satisfiesExcessiveGapCondition` together with interval membership in
  `Set.Icc`;
- bridge/view: the additional weak-duality lower bound `φ uBar ≤ f xBar`.

Primitive data:
- the local lower smoothing estimate at `xBar`;
- the excessive-gap certificate at `(xBar, uBar)`;
- the weak-duality inequality at `(xBar, uBar)`.

Derived API:
- the canonical interval bound
  `f xBar - φ uBar ∈ Set.Icc 0 (μ₂ * D₂)`.

Source/core/bridge triage:
- source-facing: Lemma 6.2.7's bound on the raw primal-dual gap;
- core/canonical: `satisfiesExcessiveGapCondition` and
  `raw_duality_gap_le_excessive_gap_budget`;
- bridge/view: the weak-duality lower bound furnishing the left endpoint `0`.

The previous version used the opposite inequality `φ uBar ≤ fμ₂ xBar`, which cannot imply the
advertised upper bound `f xBar - φ uBar ≤ μ₂ * D₂`, and it kept unused positivity hypotheses and
a global `∀ x` smoothing assumption. The refined statement keeps only the mathematically necessary
local data and reuses the chapter owner certificate directly.
-/

section

variable {X : Type u} {U : Type v}

-- Proof sketch: the excessive-gap certificate is exactly `fμ₂ xBar ≤ φ uBar`, so
-- `raw_duality_gap_le_excessive_gap_budget` with `μ₁ = 0` yields the upper bound
-- `f xBar - φ uBar ≤ μ₂ * D₂`. The separate weak-duality hypothesis `φ uBar ≤ f xBar` gives the
-- lower bound `0 ≤ f xBar - φ uBar`.
/-- Lemma 6.2.7: if `fμ₂` satisfies the local lower estimate
`f xBar - μ₂ D₂ ≤ fμ₂ xBar`, if `(xBar, uBar)` satisfies the Chapter 6 excessive-gap
certificate `fμ₂ xBar ≤ φ uBar`, and if the raw weak-duality inequality `φ uBar ≤ f xBar`
holds at the same pair, then the primal-dual gap at `(xBar, uBar)` lies in the interval
`[0, μ₂ D₂]`. -/
theorem primal_dual_gap_bound_of_smoothed_lower_estimate
    {Q₁ : Set X} {Q₂ : Set U}
    {f fμ₂ : X → ℝ} {φ : U → ℝ}
    {μ₂ D₂ : ℝ} {xBar : Q₁} {uBar : Q₂}
    (hfμ₂_lower : f xBar - μ₂ * D₂ ≤ fμ₂ xBar)
    (hexcessive_gap : satisfiesExcessiveGapCondition Q₁ Q₂ fμ₂ φ xBar uBar)
    (hweak : φ uBar ≤ f xBar) :
    f xBar - φ uBar ∈ Set.Icc 0 (μ₂ * D₂) := sorry

end

/-! ### Lemma_6_2_8 (from Chap06) -/
noncomputable section

open scoped Gradient

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

/-
Lemma 6.2.8 lies in Chapter 6's smoothed-primal-objective / excessive-gap domain.

Sampled owner declarations:
- `smoothedPrimalObjective` and `smoothedPrimalObjective_apply` in `Chap06/Definition_6_30`, the
  chapter owner for the value `f_{μ₂}`;
- `smoothedPrimalObjective_linearization_le_selected_dual_value` in `Chap06/Lemma_6_7`, the
  earlier chapter theorem already phrased on that owner surface;
- `smoothedPrimalObjective_at_x0_le_dual_value_at_V` in `Chap06/Lemma_6_13`, the downstream file
  that had been bridging this expanded theorem back to the owner declaration.

Best owner abstraction:
- source-facing: the one-point excessive-gap inequality at `barx = x₀(u₀)` and `baru = V(u₀)`;
- core/canonical: `smoothedPrimalObjective`;
- bridge/view: the quadratic-model maximality of `V u₀` together with the identities and the
  penalty-corrected upper model for `-\hat φ` at `u₀`.

Primitive data:
- the primal-dual data `A`, `Q₂`, `hatf`, `hatφ`, `d₂`;
- the selections `x₀`, `V`, the base point `u₀`, and the Lipschitz constant `L₂φ`;
- the convexity, differentiability, Lipschitz, and penalty-corrected model hypotheses at `u₀`.

Derived API:
- the expanded formula
  `hatf (x₀ u₀) + sSup (smoothedPrimalObjectiveMaximand A hatφ d₂ (L₂φ : ℝ) (x₀ u₀) '' Q₂)`;
- the owner `smoothedPrimalObjective A Q₂ hatf hatφ d₂ (L₂φ : ℝ) (x₀ u₀)`.

This file should state the theorem directly on the chapter owner surface instead of keeping a
parallel hand-expanded `hatf + sSup (...)` statement.
-/

-- Proof sketch: apply the quadratic lower model of `φ` coming from the Lipschitz gradient
-- hypothesis at `u₀`, use that `V u₀` maximizes this model on `Q₂`, then substitute the identities
-- expressing `φ u₀` and `∇ φ(u₀)` through `x₀ u₀`. The assumed penalty-corrected upper bound for
-- `-\hat φ` turns the
-- resulting expression into the maximand defining `f_{L₂(φ)}(x₀(u₀))`.
/-- Lemma 6.2.8: if `∇ φ` is `L₂(φ)`-Lipschitz on the convex set `Q₂`, if `V(u₀)` maximizes the
quadratic model of `φ` at `u₀`, and if the identities and penalty-corrected upper model from the
preceding setup
hold at `u₀`, then the excessive-gap inequality `(6.2.31)` is valid for
`μ₂ = L₂(φ)`, `\bar x = x₀(u₀)`, and `\bar u = V(u₀)`, namely
`f_{L₂(φ)}(x₀(u₀)) ≤ φ(V(u₀))`. -/
theorem smoothed_primal_objective_at_x0_le_dual_value_at_V
    (A : E₁ →L[ℝ] StrongDual ℝ E₂) {Q₂ : Set E₂}
    {φ hatφ : E₂ → ℝ} {hatf : E₁ → ℝ} {d₂ : E₂ → ℝ}
    {x₀ : E₂ → E₁} {V : E₂ → E₂} {u₀ : E₂} {L₂φ : NNReal}
    (hQ₂_convex : Convex ℝ Q₂)
    (hu₀ : u₀ ∈ Q₂)
    (hφ_hasGradientWithinAt :
      ∀ ⦃u : E₂⦄, u ∈ Q₂ →
        HasGradientWithinAt φ (gradientWithin φ Q₂ u) Q₂ u)
    (hφ_gradient_lipschitz :
      LipschitzOnWith L₂φ (fun u ↦ gradientWithin φ Q₂ u) Q₂)
    (hV_max :
      IsMaxOn
        (fun u ↦
          φ u₀ +
            inner ℝ (gradientWithin φ Q₂ u₀) (u - u₀) -
              ((L₂φ : ℝ) / 2) * ‖u - u₀‖ ^ (2 : ℕ))
        Q₂
        (V u₀))
    (hφ_eq :
      φ u₀ = -hatφ u₀ + A (x₀ u₀) u₀ + hatf (x₀ u₀))
    (hgradφ_eq :
      gradientWithin φ Q₂ u₀ =
        (InnerProductSpace.toDual ℝ E₂).symm (A (x₀ u₀)) - gradientWithin hatφ Q₂ u₀)
    (hhatφ_model :
      ∀ ⦃u : E₂⦄, u ∈ Q₂ →
        -hatφ u ≤
          -hatφ u₀ - inner ℝ (gradientWithin hatφ Q₂ u₀) (u - u₀) +
            (L₂φ : ℝ) * d₂ u -
            ((L₂φ : ℝ) / 2) * ‖u - u₀‖ ^ (2 : ℕ)) :
    smoothedPrimalObjective A Q₂ hatf hatφ d₂ (L₂φ : ℝ) (x₀ u₀) ≤
      φ (V u₀) := sorry
