import Mathlib
import StacksProject_2024.stacks_project.Chap29.Lemma_29_36_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace AlgebraicGeometry

-- Semantic recall: mathlib owns the affine-neighborhood standard-smooth criterion through
-- `Scheme.Hom.smoothLocus`, while the current chapter also uses the source-facing pointwise owner
-- `Scheme.Hom.SmoothAt`. This file keeps the fixed-target-affine-open criterion source-facing and
-- exposes the `SmoothAt`/`smoothLocus` bridge needed by nearby Chapter 29 files.

namespace Scheme.Hom

/-- Under the ambient locally finitely presented hypothesis, the pointwise smoothness owner
`f.SmoothAt x` is equivalent to membership in the smooth locus. -/
theorem smoothAt_iff_mem_smoothLocus
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] (x : X) :
    f.SmoothAt x ↔ x ∈ f.smoothLocus := sorry

/-- Lemma 29.34.11: fix an affine open neighborhood `V` of `f x`. Then `f` is smooth at `x`,
formalized by the canonical pointwise owner `f.SmoothAt x`, if and only if there exists an affine
open neighborhood `U` of `x` contained in `f ⁻¹ᵁ V` such that the induced morphism `U ⟶ V` is
standard smooth. -/
@[stacks 01V7]
theorem smoothAt_iff_exists_affineOpen_restrict_isStandardSmooth
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (x : X) (V : S.affineOpens) (hxV : f x ∈ (V : S.Opens)) :
    f.SmoothAt x ↔
      ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
        ∃ e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens),
          (f.appLE (V : S.Opens) (U : X.Opens) e).hom.IsStandardSmooth := sorry

/-- Lemma 29.34.11, restated using the smooth locus owner from mathlib. -/
theorem mem_smoothLocus_iff_exists_affineOpen_restrict_isStandardSmooth
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (x : X) (V : S.affineOpens) (hxV : f x ∈ (V : S.Opens)) :
    x ∈ f.smoothLocus ↔
      ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
        ∃ e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens),
          (f.appLE (V : S.Opens) (U : X.Opens) e).hom.IsStandardSmooth := by
  rw [← f.smoothAt_iff_mem_smoothLocus x]
  exact f.smoothAt_iff_exists_affineOpen_restrict_isStandardSmooth x V hxV

end Scheme.Hom

end AlgebraicGeometry
