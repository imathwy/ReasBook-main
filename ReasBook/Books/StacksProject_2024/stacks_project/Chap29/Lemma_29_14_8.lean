import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap29.Lemma_29_14_7_Core

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace RingHom

-- Semantic recall / owner check:
-- - the generic base-change owner is `RingHom.IsStableUnderBaseChange`;
-- - the canonical owner for the local-isomorphism/open-immersion clause is
--   `RingHom.Locally RingHom.IsStandardOpenImmersion`;
-- - the chapter-local predicate `RingHom.isIsoOnLocalRings`, introduced in
--   `Lemma_29_14_7_Core`, is kept here only as a source-facing companion bridge to that
--   canonical owner.

/-- Lemma 29.14.8 (2): the open-immersion ring-map condition, expressed as being locally a
standard open immersion on the target, is stable under base change. -/
theorem openImmersion_isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange (RingHom.Locally RingHom.IsStandardOpenImmersion) :=
  RingHom.locally_isStableUnderBaseChange
    RingHom.IsStandardOpenImmersion.respectsIso
    RingHom.IsStandardOpenImmersion.isStableUnderBaseChange

/-- The source-facing local-ring predicate from `Lemma_29_14_7_Core` is the affine bridge to the
canonical locally standard-open-immersion owner. -/
theorem isIsoOnLocalRings_iff_locally_isStandardOpenImmersion
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A) :
    RingHom.isIsoOnLocalRings φ ↔ RingHom.Locally RingHom.IsStandardOpenImmersion φ := by
  sorry

/-- Lemma 29.14.8 (1): the local-ring clause is obtained from the canonical local-isomorphism/open
immersion owner by the affine bridge
`RingHom.isIsoOnLocalRings_iff_locally_isStandardOpenImmersion`. -/
theorem isIsoOnLocalRings_isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange RingHom.isIsoOnLocalRings := by
  intro R S R' S' _ _ _ _ _ _ _ _ _ _ _ _
  intro hφ
  rw [isIsoOnLocalRings_iff_locally_isStandardOpenImmersion] at hφ ⊢
  exact openImmersion_isStableUnderBaseChange R S R' S' hφ

end RingHom
