import Mathlib.RingTheory.Localization.Defs
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v

variable {A : Type u} [CommRing A]
variable (S : Submonoid A)
variable {B : Type v} [CommRing B]

/- Domain triage:
* source-facing clauses: the universal property of the localization map `A → Localization S`.
* core/canonical owner: `IsLocalization`.
* primitive data: the localization instance and `algebraMap A (Localization S)`.
* derived API used here: `IsLocalization.lift`, `IsLocalization.lift_comp`,
  `IsLocalization.ringHom_ext`, and `IsLocalization.lift_unique`.
-/

/- Proposition 10.9.3 (1): if `f : A →+* B` sends every element of `S` to a unit, then the
universal property of localization is exactly the canonical owner construction
`IsLocalization.lift`. -/
recall IsLocalization.lift

/- Proposition 10.9.3 (2): the canonical lift commutes with the localization map. This is exactly
`IsLocalization.lift_comp`. -/
recall IsLocalization.lift_comp

/-
Companion recall: equality of ring homomorphisms out of a localization is already controlled by
precomposition with the localization map.
-/
recall IsLocalization.ringHom_ext

/- Proposition 10.9.3 (3): any ring homomorphism `Localization S →+* B` agreeing with `f` after
precomposition with the localization map is equal to the canonical lift. This is exactly
`IsLocalization.lift_unique`. -/
recall IsLocalization.lift_unique

end
