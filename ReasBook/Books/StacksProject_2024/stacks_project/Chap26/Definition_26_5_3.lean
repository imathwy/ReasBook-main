import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

-- Semantic recall: the canonical affine owners for this definition are
-- `AlgebraicGeometry.Spec.structureSheaf`, `AlgebraicGeometry.Spec_sheaf`, `(Spec R)`, and
-- `AlgebraicGeometry.tilde`; Chapter 26 later reuses the companion API from `Lemma_26_7_1` and
-- the affine global-sections comparison `tildeGlobalSectionsIso` from `Lemma_26_5_4`.

/- Definition 26.5.3 (1): the structure sheaf on `Spec(R)` is the canonical affine structure sheaf
`AlgebraicGeometry.Spec.structureSheaf R`, and the affine scheme owner `Spec R` carries exactly
this sheaf. -/
recall Spec.structureSheaf
recall Spec_sheaf

/- Definition 26.5.3 (2): the spectrum of `R` as a locally ringed space is the affine scheme
`Spec R`, viewed on its locally ringed-space side as `(Spec R).toLocallyRingedSpace`. -/
recall Scheme.forgetToLocallyRingedSpace

section

variable (R : CommRingCat)
variable (M : ModuleCat R)

#check (Spec R).toLocallyRingedSpace

/- Definition 26.5.3 (3): for an `R`-module `M`, the associated `\mathcal O_{Spec(R)}`-module is
the canonical affine module sheaf `AlgebraicGeometry.tilde M`, written source-facingly as
`\widetilde M`. -/
-- The source-facing associated-module-sheaf API keeps `tilde` as the owner; later Chapter 26
-- files add companion lemmas around this canonical affine construction.
recall AlgebraicGeometry.tilde
#check AlgebraicGeometry.tilde M

end

end AlgebraicGeometry
