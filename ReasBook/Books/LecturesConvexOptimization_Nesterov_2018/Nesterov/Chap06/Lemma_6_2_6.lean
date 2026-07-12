import LecturesConvexOptimization_Nesterov_2018.Chap02.Definition_2_2
import LecturesConvexOptimization_Nesterov_2018.Chap06.Proposition_6_25

-- Declarations for this item will be appended below by the statement pipeline.

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
