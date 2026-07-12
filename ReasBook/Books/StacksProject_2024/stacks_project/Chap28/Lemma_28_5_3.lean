import Mathlib.AlgebraicGeometry.Noetherian

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` was unavailable on this turn because of rate limiting, so the
-- owner/API choice was checked against nearby Chapter 28/29 files and the mathlib `Noetherian`
-- / `Immersion` APIs. The source is best recorded on the canonical scheme-morphism predicate
-- `QuasiCompact`, with hypotheses `[IsImmersion f]` and `[IsLocallyNoetherian X]`; the proof is
-- the thin bridge through the canonical immersion factorization
-- `f = f.liftCoborder ≫ f.coborderRange.ι`.

/-- Lemma 28.5.3: any immersion into a locally Noetherian scheme is quasi-compact. -/
@[stacks 01OX]
theorem quasiCompact_of_isImmersion_of_isLocallyNoetherian
    {Z X : Scheme.{u}} {f : Z ⟶ X} [IsImmersion f] [IsLocallyNoetherian X] :
    QuasiCompact f := by
  let i := f.coborderRange.ι
  let _ : QuasiCompact f.liftCoborder := inferInstance
  let _ : QuasiCompact i := inferInstance
  have hcomp := quasiCompact_comp f.liftCoborder i
  simpa [i, f.liftCoborder_ι] using hcomp

end AlgebraicGeometry
