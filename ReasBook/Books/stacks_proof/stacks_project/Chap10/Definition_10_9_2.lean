import Mathlib.RingTheory.Localization.Defs
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (A : Type u) [CommRing A] (S : Submonoid A)

/- Definition 10.9.2: for a commutative ring `A` and a submonoid `S`, the canonical ring
`Localization S` is the localization of `A` with respect to `S`. -/
recall Localization

/- Companion recall: the owner abstraction for the statement that `Localization S` is the
localization of `A` with respect to `S` is the canonical instance
`Localization.isLocalization : IsLocalization S (Localization S)`. -/
recall Localization.isLocalization

/- Companion recall: the natural localization map `A → Localization S`, sending `x` to `x / 1`,
is the canonical ring homomorphism `algebraMap A (Localization S)`, characterized by
`Localization.mk_one_eq_algebraMap`. -/
recall Localization.mk_one_eq_algebraMap

end
