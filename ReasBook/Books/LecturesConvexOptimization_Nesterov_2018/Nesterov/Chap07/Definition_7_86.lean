import Mathlib.Tactic.Recall
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.Definition_3_1_5
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap07.Lemma_7_20

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped RelativeScaleTransformNotation

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/- Definition 7.86 lies in the chapter's relative-scale subgradient-transform domain.

Primary domain:
- convex analysis of the half-squared transform `x ↦ (1 / 2) * f(x)^2` on a real
  inner-product space.

Relevant owner-style declarations sampled before refinement:
- `IsSubgradientAt` in `Chap03/Definition_3_1_5`
- `relativeScaleTransformedSubgradient` in `Chap07/Lemma_7_20`
- `relativeScaleTransformedObjective` in `Chap07/Lemma_7_20`

Best owner abstraction:
- the Chapter 7 owners `relativeScaleTransformedObjective` and
  `relativeScaleTransformedSubgradient`, with the Chapter 3 owner predicate `IsSubgradientAt`
  providing the extended-valued subgradient surface.

Primitive data:
- a real-valued objective `f : V → ℝ`
- a base point `x` and a subgradient vector `g`

Derived API:
- the notation-level formulas for `f̂` and `ĝ[f; x] g`
- the `IsSubgradientAt` bridge theorem below

Source/core/bridge triage:
- source-facing: Definition 7.86's transformed objective and transformed subgradient
- core/canonical: the existing Chapter 7 owners in `Lemma_7_20`
- bridge/view: the `IsSubgradientAt` theorem in this file

The transformed objective and transformed subgradient are already owned upstream in
`Lemma_7_20`, so this file reuses those owners directly and keeps only the extended-valued
subgradient bridge that is specific to the Definition 7.86 surface.
-/

/- Definition 7.86 reuses the Chapter 7 transformed-subgradient owner from `Lemma_7_20`. -/
recall relativeScaleTransformedSubgradient

/- Definition 7.86 reuses the owner expansion of the transformed subgradient. -/
recall relativeScaleTransformedSubgradient_def

/- Definition 7.86 reuses the Chapter 7 transformed-objective owner from `Lemma_7_20`. -/
recall relativeScaleTransformedObjective

/- Definition 7.86 reuses the owner expansion of the transformed objective. -/
recall relativeScaleTransformedObjective_apply

/-- If `g` is a subgradient of `f` at `x` and `f x` is nonnegative, then `f(x) • g` is a
subgradient of the transformed objective `f̂` at `x`. -/
-- Proof sketch: from `hg`, for each `y` we have `f y - f x ≥ ⟪g, y - x⟫`. Multiply by the
-- nonnegative scalar `f x`, then add the square term `(1 / 2) * (f y - f x)^2 ≥ 0` and expand to
-- obtain the supporting inequality for `f̂` with subgradient `ĝ[f; x] g`.
theorem IsSubgradientAt.relativeScaleTransformedObjective
    {f : V → ℝ} {x g : V}
    (hg : IsSubgradientAt (fun y ↦ (f y : WithTop ℝ)) x g) (hx_nonneg : 0 ≤ f x) :
    IsSubgradientAt (fun y ↦ (f̂ y : WithTop ℝ)) x (ĝ[f; x] g) := sorry

end
