import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap06.Definition_6_38
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap06.Definition_6_39
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap06.Theorem_6_4

-- Declarations for this item will be appended below by the statement pipeline.

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
