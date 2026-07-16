import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap06.Definition_6_30

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
