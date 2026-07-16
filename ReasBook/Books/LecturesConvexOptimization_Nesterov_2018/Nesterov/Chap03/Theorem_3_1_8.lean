import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.PointwiseSupremumOn
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.Definition_3_1_1_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped WithTopConvexAnalysis

variable {ι : Type u} {X : Type v}

/- Theorem 3.1.8 lies in the chapter's `WithTop ℝ`-valued closed-convex pointwise-supremum
domain.

Sampled owner-style declarations in this domain:
- `pointwiseSupremumOn` and `pointwiseSupremumOn_apply` from `PointwiseSupremumOn`
- `dom` and `constrainedEpigraph` from `Definition_3_3`
- `ClosedConvexOn` from `Definition_3_1_1_5`
- `ConvexOn ℝ (dom f) (withTopRealPart f)` as the canonical convexity view behind
  `ClosedConvexOn`

Best owner abstraction:
- core/canonical owners reused from earlier chapter files:
  `pointwiseSupremumOn`, `dom`, and `ClosedConvexOn`
- bridge/view layer: the feasible-domain restriction
  `pointwiseSupremumOnEffectiveDomain Q Δ φ = Q ∩ dom (pointwiseSupremumOn Δ φ)`

Primitive data:
- the parameter subset `Δ : Set ι`
- the slice family `φ : X → ι → WithTop ℝ`
- the owner function `pointwiseSupremumOn Δ φ`

Derived API:
- `pointwiseSupremumOn_apply`
- `pointwiseSupremumOnEffectiveDomain`
- `mem_pointwiseSupremumOnEffectiveDomain_iff`
- `mem_pointwiseSupremumOnEffectiveDomain_iff_lt_top`
- `ClosedConvexOn.pointwise_sSup`

Source/core/bridge triage:
- source-facing: Theorem 3.1.8 itself, namely the closed-convexity theorem below
- core/canonical: `pointwiseSupremumOn`, `dom`, `ClosedConvexOn`
- bridge/view: `pointwiseSupremumOnEffectiveDomain`

This file reuses the generic owner `pointwiseSupremumOn`, and it does not keep a parallel
primitive notion of “finite-value domain”: that domain is derived canonically from the upstream
owner `dom` applied to `pointwiseSupremumOn Δ φ`, then intersected with the ambient feasible set
`Q`. -/

/-- The finite-value domain of the pointwise supremum over `Δ` inside `Q`, expressed through the
chapter owner `dom`. -/
abbrev pointwiseSupremumOnEffectiveDomain
    (Q : Set X) (Δ : Set ι) (φ : X → ι → WithTop ℝ) : Set X :=
  Q ∩ dom (pointwiseSupremumOn Δ φ)

/-- Membership in `pointwiseSupremumOnEffectiveDomain Q Δ φ` means lying in `Q` and in the
canonical effective domain of `pointwiseSupremumOn Δ φ`. -/
@[simp]
theorem mem_pointwiseSupremumOnEffectiveDomain_iff
    {Q : Set X} {Δ : Set ι} {φ : X → ι → WithTop ℝ} {x : X} :
    x ∈ pointwiseSupremumOnEffectiveDomain Q Δ φ ↔
      x ∈ Q ∧ x ∈ dom (pointwiseSupremumOn Δ φ) :=
  Iff.rfl

/-- Membership in `pointwiseSupremumOnEffectiveDomain Q Δ φ` can be read as a finiteness
condition on the pointwise supremum. -/
theorem mem_pointwiseSupremumOnEffectiveDomain_iff_lt_top
    {Q : Set X} {Δ : Set ι} {φ : X → ι → WithTop ℝ} {x : X} :
    x ∈ pointwiseSupremumOnEffectiveDomain Q Δ φ ↔
      x ∈ Q ∧ pointwiseSupremumOn Δ φ x < ⊤ := by
  rw [mem_pointwiseSupremumOnEffectiveDomain_iff, mem_withTopEffectiveDomain_iff]

section

variable [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]

namespace ClosedConvexOn

/-- Theorem 3.1.8: if every slice `x ↦ φ(x, y)` with `y ∈ Δ` is closed and convex on `Q`, then
the pointwise supremum `x ↦ sup_{y ∈ Δ} φ(x, y)` is closed and convex on the finite-value domain
`{x ∈ Q | sup_{y ∈ Δ} φ(x, y) < +∞}`. -/
-- Proof sketch: the constrained epigraph of `pointwiseSupremumOn Δ φ` over
-- `pointwiseSupremumOnEffectiveDomain Q Δ φ` is the intersection over `y ∈ Δ` of the constrained
-- epigraphs of the slices `x ↦ φ x y`. Intersections preserve closedness and convexity, and the
-- finiteness-on-domain clause is built into `pointwiseSupremumOnEffectiveDomain`.
theorem pointwise_sSup
    {Q : Set X} {Δ : Set ι} {φ : X → ι → WithTop ℝ}
    (hΔ : Δ.Nonempty)
    (hφ : ∀ y ∈ Δ, ClosedConvexOn Q (fun x ↦ φ x y)) :
    ClosedConvexOn (pointwiseSupremumOnEffectiveDomain Q Δ φ) (pointwiseSupremumOn Δ φ) := sorry

end ClosedConvexOn

end

end
