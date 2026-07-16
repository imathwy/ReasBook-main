import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap06.Definition_6_30

noncomputable section

universe u v

/- Lemma 6.7 lies in the chapter's smoothed primal objective / tangent-plane domain.

Sampled owner declarations:
- `smoothedPrimalObjectiveArgmax`, `smoothedPrimalObjectiveMaximand`, and
  `smoothedPrimalObjective` in `Chap06/Definition_6_30`, the chapter owners for the selected dual
  maximizer, the regularized dual maximand, and its supremum objective;
- `mem_smoothedPrimalObjectiveArgmax_iff` in `Chap06/Definition_6_30`, the thin bridge from the
  argmax owner to the underlying feasible-maximizer conditions;
- `ConvexOn.lower_tangent_plane_of_hasGradientWithinAt` in `Chap02/Definition_2_2`, the
  project owner for the first-order supporting inequality on a convex feasible set;
- mathlib `HasGradientWithinAt` / `gradientWithin`, the canonical within-set gradient layer.

Best owner abstraction:
- source-facing: Lemma 6.7's one-point linearization bound at a selected dual maximizer;
- core/canonical: `smoothedPrimalObjectiveArgmax`, `smoothedPrimalObjective`, `ConvexOn`, and
  `HasGradientWithinAt`;
- bridge/view: `mem_smoothedPrimalObjectiveArgmax_iff`, unpacking the argmax owner to feasibility
  and `IsMaxOn`.

Primitive data:
- `A`, `Q₁`, `Q₂`, `hatf`, `hatφ`, `d₂`, `μ₂`, `x`, `xhat`, and `u`;
- convexity of `hatf` on `Q₁`, which already packages convexity of `Q₁`;
- the source-facing argmax membership hypothesis at `xhat`;
- the within-set gradient witness for `hatf` at `xhat`;
- the sign hypotheses `0 ≤ μ₂` and `0 ≤ d₂ u`.

Derived API:
- the canonical smoothed objective value at `xhat`;
- the tangent-plane inequality for `hatf` at `xhat`;
- the bridge from argmax membership to the underlying `IsMaxOn` witness;
- the resulting affine upper bound against the selected dual value.

Source/core/bridge triage:
- source-facing: the theorem below;
- core/canonical: the owner declarations from `Definition_6_30`;
- bridge/view: the pointwise maximizer witness `u`.

The previous version rebuilt local owners `smoothedObjectiveIntegrand` and
`primalDualSmoothedObjective`. Those were exact duplicates of the chapter owners in
`Definition_6_30`, so this file now states the source-facing lemma directly against the canonical
API.
-/

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

-- Proof sketch: expand `smoothedPrimalObjective` at `xhat`, unpack the argmax membership `hu`
-- with `mem_smoothedPrimalObjectiveArgmax_iff` to bound the supremum term by the selected dual
-- value, apply the supporting-hyperplane inequality for the
-- convex function `hatf` at `xhat`, rewrite the affine pairing term as `A x u`, and drop the
-- nonpositive term `-μ₂ * d₂ u` using `μ₂ ≥ 0` and `d₂ u ≥ 0`.
/-- Lemma 6.7: if `u ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ₂ xhat`, then the affine
linearization of the smoothed primal objective at `xhat ∈ Q₁`, with the smooth contribution
written as `∇ \hat f(xhat)`, is bounded above by `\hat f(x) + ⟪A x, u⟫ - \hat φ(u)` for every
`x ∈ Q₁`. -/
theorem smoothedPrimalObjective_linearization_le_selected_dual_value
    (A : E₁ →L[ℝ] StrongDual ℝ E₂)
    {Q₁ : Set E₁} {Q₂ : Set E₂} {hatf : E₁ → ℝ} {hatφ d₂ : E₂ → ℝ} {μ₂ : ℝ}
    (hhatf_conv : ConvexOn ℝ Q₁ hatf) (hμ₂ : 0 ≤ μ₂)
    {x xhat : E₁} (hx : x ∈ Q₁) (hxhat : xhat ∈ Q₁) {u : E₂}
    (hu : u ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ₂ xhat)
    (hhatf_grad : HasGradientWithinAt hatf (gradientWithin hatf Q₁ xhat) Q₁ xhat)
    (hd₂_nonneg : 0 ≤ d₂ u) :
    smoothedPrimalObjective A Q₂ hatf hatφ d₂ μ₂ xhat +
      inner ℝ (gradientWithin hatf Q₁ xhat) (x - xhat) +
      A (x - xhat) u ≤
      hatf x + A x u - hatφ u := by
  sorry

end
