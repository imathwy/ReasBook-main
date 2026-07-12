import Mathlib.AlgebraicGeometry.OpenImmersion

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

namespace AlgebraicGeometry

/- Source/core/bridge triage for Lemma 26.9.2:
- `source-facing`: an open immersion into a scheme carries the canonical induced scheme structure on
  its source, and an open subset of a scheme carries the canonical open-subscheme structure;
- `core/canonical`: the owners are `PresheafedSpace.IsOpenImmersion.toScheme`,
  `LocallyRingedSpace.IsOpenImmersion.isoRestrict`, and `Scheme.Opens.toScheme`;
- `bridge/view`: the file only keeps companion recalls for the underlying locally ringed space
  identification and the restriction isomorphism. -/

-- Semantic recall: the canonical owners here are the open subset `V : X.Opens`, the restricted
-- locally ringed space `X.toLocallyRingedSpace.restrict V.isOpenEmbedding`, and the associated
-- open subscheme `V.toScheme`. The source-facing statement should expose those owners directly
-- rather than a duplicate wrapper definition for the induced scheme structure.

/- Lemma 26.9.2 (1): the canonical scheme owner on the source of an open immersion into a scheme
is `PresheafedSpace.IsOpenImmersion.toScheme`. -/
#check PresheafedSpace.IsOpenImmersion.toScheme

/- Companion check: the induced scheme has the expected underlying locally ringed space. -/
#check PresheafedSpace.IsOpenImmersion.toScheme_toLocallyRingedSpace

/-
Lemma 26.9.2 (1): the more precise identification with the image open of `j` is exactly the
canonical open-immersion isomorphism `LocallyRingedSpace.IsOpenImmersion.isoRestrict`.
-/
#check LocallyRingedSpace.IsOpenImmersion.isoRestrict

/-
Lemma 26.9.2 (2): any open subspace of a scheme is the canonical open subscheme `U.toScheme`,
with its canonical inclusion into `X`.
-/
#check Scheme.Opens.toScheme

/- Companion check: the inclusion of the canonical open subscheme is `U.ι`. -/
#check Scheme.Opens.ι

end AlgebraicGeometry
