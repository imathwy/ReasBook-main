import Nesterov.Chap03.Theorem_3_1_8
import Nesterov.Chap03.Definition_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Set
open scoped WithTopConvexAnalysis

universe u v

variable {ι : Type u} {X : Type v}

/- Lemma 3.1.14 sits in the chapter's extended-valued convex-analysis domain of subset-indexed
pointwise suprema and constrained subdifferentials.

Sampled owner declarations:
- `pointwiseSupremumOn`
- `pointwiseSupremumOnEffectiveDomain`
- `ClosedConvexOn.pointwise_sSup`
- `constrainedSubdifferential`

Best owner abstraction:
- the subset-indexed pointwise-supremum owner surface from `Theorem_3_1_8`, together with the
  earlier owner notions `ClosedConvexOn` and `constrainedSubdifferential`

Primitive data:
- the owner pointwise-supremum object `pointwiseSupremumOn Δ φ`
- the owner finite-value domain `pointwiseSupremumOnEffectiveDomain Q Δ φ`
- the earlier chapter owners `ClosedConvexOn` and `constrainedSubdifferential`

Derived API in this file:
- the active-index set `activePointwiseSupremumOnIndices Δ φ x`
- the membership bridge `mem_activePointwiseSupremumOnIndices_iff`
- the active-slice convex-hull inclusion theorem

Source/core/bridge triage:
- source-facing: `activePointwiseSupremumOnIndices`,
  `convexHull_activePointwiseSupremumOnSubdifferentials_subset`
- core/canonical: `pointwiseSupremumOn`, `pointwiseSupremumOnEffectiveDomain`,
  `ClosedConvexOn`, `constrainedSubdifferential`, `ClosedConvexOn.pointwise_sSup`
- bridge/view: `mem_activePointwiseSupremumOnIndices_iff`

This file therefore adds only the active-slice layer from the source text and reuses the earlier
chapter owners directly instead of re-declaring them locally. Its source-facing inclusion theorem
inherits the intrinsic real-inner-product-space ambient assumptions already required by
`constrainedSubdifferential`, instead of freezing that theorem to the textbook Euclidean model. -/

/-- The active parameter set `I(x)` for the subset-indexed pointwise supremum over `Δ`. -/
def activePointwiseSupremumOnIndices
    (Δ : Set ι) (φ : X → ι → WithTop ℝ) (x : X) : Set ι :=
  {y | y ∈ Δ ∧ φ x y = pointwiseSupremumOn Δ φ x}

/-- Membership in `activePointwiseSupremumOnIndices Δ φ x` means that `y ∈ Δ` attains the
pointwise supremum value at `x`. -/
@[simp]
theorem mem_activePointwiseSupremumOnIndices_iff
    {Δ : Set ι} {φ : X → ι → WithTop ℝ} {x : X} {y : ι} :
    y ∈ activePointwiseSupremumOnIndices Δ φ x ↔
      y ∈ Δ ∧ φ x y = pointwiseSupremumOn Δ φ x :=
  Iff.rfl

variable {E : Type v} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Lemma 3.1.14, active-slice inclusion part: at every
`x ∈ pointwiseSupremumOnEffectiveDomain Q Δ φ`, the constrained subdifferential of
`pointwiseSupremumOn Δ φ` over `pointwiseSupremumOnEffectiveDomain Q Δ φ` contains the convex
hull of the constrained subdifferentials of the active slices `y ∈ I(x)`.

The closed-convex part of Lemma 3.1.14 is the separate owner theorem
`ClosedConvexOn.pointwise_sSup`. -/
-- Proof sketch: every `g ∈ constrainedSubdifferential Q (fun z ↦ φ z y) x` with active `y`
-- satisfies the subgradient inequality for `pointwiseSupremumOn Δ φ` because
-- `pointwiseSupremumOn Δ φ z ≥ φ z y` for all `z ∈ Q` and activity gives
-- `φ x y = pointwiseSupremumOn Δ φ x`. The target constrained subdifferential is convex, so it
-- contains the convex hull of the union of those active-slice subdifferentials.
theorem convexHull_activePointwiseSupremumOnSubdifferentials_subset
    {Q : Set E} {Δ : Set ι} {φ : E → ι → WithTop ℝ} {x : E}
    (hx : x ∈ pointwiseSupremumOnEffectiveDomain Q Δ φ) :
    convexHull ℝ
        (⋃ y ∈ activePointwiseSupremumOnIndices Δ φ x,
          ∂[Q] (fun z ↦ φ z y) (x)) ⊆
      ∂[pointwiseSupremumOnEffectiveDomain Q Δ φ] (pointwiseSupremumOn Δ φ) (x) := sorry

end
