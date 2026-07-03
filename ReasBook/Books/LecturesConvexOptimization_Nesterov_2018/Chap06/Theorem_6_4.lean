import Mathlib
import Nesterov.Chap01.Definition_1_3_3
import Nesterov.Chap03.Definition_3_1_1_3
import Nesterov.Chap06.Definition_6_30
import Nesterov.Chap06.Proposition_6_25

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConstrainedArgmin Gradient

universe u v

/-- The chapter excessive-gap condition on a feasible pair `(xBar, uBar)` is the inequality
`f_{μ₂}(xBar) ≤ φ_{μ₁}(uBar)`. -/
abbrev satisfiesExcessiveGapCondition
    {X : Type u} {U : Type v}
    (Q₁ : Set X) (Q₂ : Set U)
    (fμ₂ : X → ℝ) (φμ₁ : U → ℝ)
    (xBar : Q₁) (uBar : Q₂) : Prop :=
  fμ₂ xBar ≤ φμ₁ uBar

section Updates

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

/- Theorem 6.4 lies in the Chapter 6 excessive-gap / smoothing-update domain.

Mandatory domain-style sampling before refinement:
- `satisfiesExcessiveGapCondition` below, the source-facing owner for the excessive-gap
  certificate;
- `smoothedPrimalObjective` and `smoothedPrimalObjectiveArgmax` in `Chap06/Definition_6_30`, the
  Chapter 6 owners for the smoothed primal objective and the dual oracle maximizer set;
- `smoothedDualObjective` and `smoothedDualObjectiveMinimand` in `Chap06/Proposition_6_25`, whose
  finite real part and argmin surface give the real-valued dual quantity and primal oracle data
  used in the chapter;
- `constrainedArgmin` / `argmin[Q]` and `mem_constrainedArgmin_iff` in
  `Chap01/Definition_1_3_3`, the canonical feasible-minimizer owner and its membership bridge.

Best owner abstraction:
- source-facing: the update maps `\hat x`, `\bar u_+`, `\bar x_+` together with the preservation
  of `satisfiesExcessiveGapCondition`;
- core/canonical: `satisfiesExcessiveGapCondition`, `smoothedPrimalObjective`,
  `smoothedDualObjective`, `smoothedDualObjectiveMinimand`, `smoothedPrimalObjectiveArgmax`, and
  the direct argmin surface `xμ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand ... u)`;
- bridge/view: the subtype-valued update maps below, which turn the oracle-owner hypotheses into
  feasible updated points without introducing a second excessive-gap predicate.

Primitive data:
- the feasible sets `Q₁`, `Q₂` and their convexity;
- the Chapter 6 smoothing owners and oracle-selection hypotheses;
- the direct pointwise argmin data defining the primal oracle selections;
- the current feasible pair `(barx, baru)` and the step size `τ`.

Derived API:
- the updated smoothing parameter `μ₁⁺ = (1 - τ) μ₁`;
- the feasible updated points `\hat x`, `\bar u_+`, and `\bar x_+`;
- the source-facing preservation theorem stated directly through
  `satisfiesExcessiveGapCondition`.

The previous version rebuilt these notions through a new bundled owner `ExcessiveGapFramework`
and a second predicate `framework.excessive_gap_condition`. This file now keeps the textbook
update objects directly and states Theorem 6.4 on top of the existing Chapter 6 owners.
-/

/-- The updated primal smoothing parameter `μ₁⁺ = (1 - τ) μ₁`. -/
def reduced_primal_smoothing (μ₁ τ : ℝ) : ℝ :=
  (1 - τ) * μ₁

/-- Expanding `reduced_primal_smoothing` recovers the formula `μ₁⁺ = (1 - τ) μ₁`. -/
theorem reduced_primal_smoothing_def
    (μ₁ τ : ℝ) :
    reduced_primal_smoothing μ₁ τ = (1 - τ) * μ₁ := sorry

/-- A step size in `(0, 1)` defines the convex-combination parameter used by the Chapter 6
updates. -/
theorem tau_mem_Icc
    {τ : ℝ} (hτ : 0 < τ) (hτ_lt : τ < 1) :
    τ ∈ Set.Icc (0 : ℝ) 1 := sorry

-- Proof sketch: unpack the selected point `xμ₁ baru` from the canonical argmin owner, use
-- `mem_constrainedArgmin_iff` to recover feasibility in `Q₁`, and then apply convexity of `Q₁`
-- to the convex combination with `barx`.
/-- The convex combination defining `\hat x` stays in the feasible primal set `Q₁`. -/
theorem predicted_primal_point_mem
    {Q₁ : Set E₁} (hQ₁ : Convex ℝ Q₁)
    {A : E₁ →L[ℝ] StrongDual ℝ E₂} {hatf d₁ : E₁ → ℝ} {μ₁ : ℝ}
    {xμ₁ : E₂ → E₁}
    (hxμ₁ :
      ∀ u : E₂, xμ₁ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u))
    {Q₂ : Set E₂} (barx : Q₁) (baru : Q₂)
    (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    (1 - τ) • (barx : E₁) + τ • xμ₁ baru ∈ Q₁ := sorry

/-- The intermediate primal point
`\hat x = (1 - τ) \bar x + τ x_{μ₁}(\bar u)` as a feasible point of `Q₁`. -/
def predicted_primal_point
    {Q₁ : Set E₁} (hQ₁ : Convex ℝ Q₁)
    {A : E₁ →L[ℝ] StrongDual ℝ E₂} {hatf d₁ : E₁ → ℝ} {μ₁ : ℝ}
    {xμ₁ : E₂ → E₁}
    (hxμ₁ :
      ∀ u : E₂, xμ₁ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u))
    {Q₂ : Set E₂} (barx : Q₁) (baru : Q₂)
    (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    Q₁ :=
  ⟨(1 - τ) • (barx : E₁) + τ • xμ₁ baru,
    predicted_primal_point_mem hQ₁ hxμ₁ barx baru τ hτ⟩

/-- Expanding `predicted_primal_point` recovers
`\hat x = (1 - τ) \bar x + τ x_{μ₁}(\bar u)`. -/
@[simp] theorem predicted_primal_point_val
    {Q₁ : Set E₁} (hQ₁ : Convex ℝ Q₁)
    {A : E₁ →L[ℝ] StrongDual ℝ E₂} {hatf d₁ : E₁ → ℝ} {μ₁ : ℝ}
    {xμ₁ : E₂ → E₁}
    (hxμ₁ :
      ∀ u : E₂, xμ₁ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u))
    {Q₂ : Set E₂} (barx : Q₁) (baru : Q₂)
    (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    (predicted_primal_point hQ₁ hxμ₁ barx baru τ hτ : E₁) =
      (1 - τ) • (barx : E₁) + τ • xμ₁ baru := sorry

-- Proof sketch: unpack the selected maximizer `uμ₂ xHat` with
-- `mem_smoothedPrimalObjectiveArgmax_iff` to recover feasibility in `Q₂`, and then use convexity
-- of `Q₂` for the convex combination with `baru`.
/-- The convex combination defining `\bar u_+` stays in the feasible dual set `Q₂`. -/
theorem updated_dual_point_mem
    {Q₁ : Set E₁} {Q₂ : Set E₂} (hQ₂ : Convex ℝ Q₂)
    {A : E₁ →L[ℝ] StrongDual ℝ E₂} {hatφ d₂ : E₂ → ℝ} {μ₂ : ℝ}
    {uμ₂ : E₁ → E₂}
    (huμ₂ : ∀ ⦃x : E₁⦄, x ∈ Q₁ → uμ₂ x ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ₂ x)
    (baru : Q₂) (xHat : Q₁)
    (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    (1 - τ) • (baru : E₂) + τ • uμ₂ xHat ∈ Q₂ := sorry

/-- The updated dual point
`\bar u_+ = (1 - τ) \bar u + τ u_{μ₂}(\hat x)` as a feasible point of `Q₂`. -/
def updated_dual_point
    {Q₁ : Set E₁} {Q₂ : Set E₂} (hQ₂ : Convex ℝ Q₂)
    {A : E₁ →L[ℝ] StrongDual ℝ E₂} {hatφ d₂ : E₂ → ℝ} {μ₂ : ℝ}
    {uμ₂ : E₁ → E₂}
    (huμ₂ : ∀ ⦃x : E₁⦄, x ∈ Q₁ → uμ₂ x ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ₂ x)
    (baru : Q₂) (xHat : Q₁)
    (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    Q₂ :=
  ⟨(1 - τ) • (baru : E₂) + τ • uμ₂ xHat,
    updated_dual_point_mem hQ₂ huμ₂ baru xHat τ hτ⟩

/-- Expanding `updated_dual_point` recovers
`\bar u_+ = (1 - τ) \bar u + τ u_{μ₂}(\hat x)`. -/
@[simp] theorem updated_dual_point_val
    {Q₁ : Set E₁} {Q₂ : Set E₂} (hQ₂ : Convex ℝ Q₂)
    {A : E₁ →L[ℝ] StrongDual ℝ E₂} {hatφ d₂ : E₂ → ℝ} {μ₂ : ℝ}
    {uμ₂ : E₁ → E₂}
    (huμ₂ : ∀ ⦃x : E₁⦄, x ∈ Q₁ → uμ₂ x ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ₂ x)
    (baru : Q₂) (xHat : Q₁)
    (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    (updated_dual_point hQ₂ huμ₂ baru xHat τ hτ : E₂) =
      (1 - τ) • (baru : E₂) + τ • uμ₂ xHat := sorry

-- Proof sketch: unpack the selected point `xμ₁ uBarPlus` from the canonical argmin owner, use
-- `mem_constrainedArgmin_iff` to recover feasibility in `Q₁`, and then apply convexity of `Q₁`
-- to the convex combination with `barx`.
/-- The convex combination defining `\bar x_+` stays in the feasible primal set `Q₁`. -/
theorem updated_primal_point_mem
    {Q₁ : Set E₁} (hQ₁ : Convex ℝ Q₁)
    {A : E₁ →L[ℝ] StrongDual ℝ E₂} {hatf d₁ : E₁ → ℝ} {μ₁ : ℝ}
    {xμ₁ : E₂ → E₁}
    (hxμ₁ :
      ∀ u : E₂, xμ₁ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u))
    {Q₂ : Set E₂} (barx : Q₁) (uBarPlus : Q₂)
    (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    (1 - τ) • (barx : E₁) + τ • xμ₁ uBarPlus ∈ Q₁ := sorry

/-- The updated primal point
`\bar x_+ = (1 - τ) \bar x + τ x_{μ₁⁺}(\bar u_+)` as a feasible point of `Q₁`. -/
def updated_primal_point
    {Q₁ : Set E₁} (hQ₁ : Convex ℝ Q₁)
    {A : E₁ →L[ℝ] StrongDual ℝ E₂} {hatf d₁ : E₁ → ℝ} {μ₁ : ℝ}
    {xμ₁ : E₂ → E₁}
    (hxμ₁ :
      ∀ u : E₂, xμ₁ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u))
    {Q₂ : Set E₂} (barx : Q₁) (uBarPlus : Q₂)
    (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    Q₁ :=
  ⟨(1 - τ) • (barx : E₁) + τ • xμ₁ uBarPlus,
    updated_primal_point_mem hQ₁ hxμ₁ barx uBarPlus τ hτ⟩

/-- Expanding `updated_primal_point` recovers
`\bar x_+ = (1 - τ) \bar x + τ x_{μ₁⁺}(\bar u_+)`. -/
@[simp] theorem updated_primal_point_val
    {Q₁ : Set E₁} (hQ₁ : Convex ℝ Q₁)
    {A : E₁ →L[ℝ] StrongDual ℝ E₂} {hatf d₁ : E₁ → ℝ} {μ₁ : ℝ}
    {xμ₁ : E₂ → E₁}
    (hxμ₁ :
      ∀ u : E₂, xμ₁ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u))
    {Q₂ : Set E₂} (barx : Q₁) (uBarPlus : Q₂)
    (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    (updated_primal_point hQ₁ hxμ₁ barx uBarPlus τ hτ : E₁) =
      (1 - τ) • (barx : E₁) + τ • xμ₁ uBarPlus := sorry

end Updates

section Theorem

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

-- Proof sketch: use the subtype-valued update maps to keep all iterates in `Q₁` and `Q₂`,
-- expand the update formulas
-- `\hat x = (1 - τ) \bar x + τ x_{μ₁}(\bar u)`,
-- `\bar u_+ = (1 - τ) \bar u + τ u_{μ₂}(\hat x)`,
-- `\bar x_+ = (1 - τ) \bar x + τ x_{μ₁⁺}(\bar u_+)`,
-- and combine the initial excessive-gap certificate with the gradient-Lipschitz estimate for the
-- actual Chapter 6 smoothed primal objective and the oracle optimality hypotheses.
/-- Theorem 6.4: if `( \bar x, \bar u )` satisfies the Chapter 6 excessive-gap condition for the
actual smoothed objective owners `smoothedPrimalObjective` and `smoothedDualObjective`, if
`x_{μ₁}` and `x_{μ₁⁺}` are primal oracle selections through the canonical argmin surface
`xμ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand ... u)`, if `u_{μ₂}` selects the canonical
argmax owner `smoothedPrimalObjectiveArgmax`, and if
`τ² / (1 - τ) ≤ μ₁ / L₁(f_{μ₂})`, then the updated pair
`\bar u_+ = (1 - τ) \bar u + τ u_{μ₂}(\hat x)` and
`\bar x_+ = (1 - τ) \bar x + τ x_{μ₁⁺}(\bar u_+)`, with
`\hat x = (1 - τ) \bar x + τ x_{μ₁}(\bar u)` and `μ₁⁺ = (1 - τ) μ₁`,
again satisfies `satisfiesExcessiveGapCondition`. -/
theorem satisfiesExcessiveGapCondition_preserved_under_update
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {Q₂ : Set E₂}
    (hQ₁ : Convex ℝ Q₁) (hQ₂ : Convex ℝ Q₂)
    {hatf : E₁ → ℝ} {hatφ : E₂ → ℝ} {d₁ : E₁ → ℝ} {d₂ : E₂ → ℝ}
    {μ₁ μ₂ τ : ℝ} {xμ : ℝ → E₂ → E₁} {uμ₂ : E₁ → E₂} {Lfμ₂ : NNReal}
    {barx : Q₁} {baru : Q₂}
    (hgap :
      satisfiesExcessiveGapCondition
        Q₁ Q₂
        (smoothedPrimalObjective A Q₂ hatf hatφ d₂ μ₂)
        (extendedRealRealPart (smoothedDualObjective A Q₁ hatf hatφ d₁ μ₁))
        barx baru)
    (hxμ₁ :
      ∀ u : E₂, xμ μ₁ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u))
    (hxμ₁_plus :
      ∀ u : E₂,
        xμ (reduced_primal_smoothing μ₁ τ) u ∈
          argmin[Q₁]
            (smoothedDualObjectiveMinimand A hatf d₁ (reduced_primal_smoothing μ₁ τ) u))
    (huμ₂ :
      ∀ ⦃x : E₁⦄, x ∈ Q₁ →
        uμ₂ x ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ₂ x)
    (hfμ₂_gradient_lipschitz :
      LipschitzOnWith Lfμ₂
        (fun x ↦ gradientWithin (smoothedPrimalObjective A Q₂ hatf hatφ d₂ μ₂) Q₁ x)
        Q₁)
    (hτ : 0 < τ) (hτ_lt : τ < 1)
    (hstep : τ ^ (2 : ℕ) / (1 - τ) ≤ μ₁ / (Lfμ₂ : ℝ)) :
    satisfiesExcessiveGapCondition
      Q₁ Q₂
      (smoothedPrimalObjective A Q₂ hatf hatφ d₂ μ₂)
      (extendedRealRealPart
        (smoothedDualObjective A Q₁ hatf hatφ d₁ (reduced_primal_smoothing μ₁ τ)))
      (updated_primal_point hQ₁ hxμ₁_plus barx
        (updated_dual_point hQ₂ huμ₂ baru
          (predicted_primal_point hQ₁ hxμ₁ barx baru τ (tau_mem_Icc hτ hτ_lt))
          τ (tau_mem_Icc hτ hτ_lt))
        τ (tau_mem_Icc hτ hτ_lt))
      (updated_dual_point hQ₂ huμ₂ baru
        (predicted_primal_point hQ₁ hxμ₁ barx baru τ (tau_mem_Icc hτ hτ_lt))
        τ (tau_mem_Icc hτ hτ_lt)) := sorry

end Theorem

end
