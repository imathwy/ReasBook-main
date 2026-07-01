import Mathlib.RingTheory.Localization.Defs
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {A : Type u} [CommRing A] (S : Submonoid A)

/- Lemma 10.9.4 is a `bridge/view` item. Its owner abstraction is the canonical localization
theorem `IsLocalization.subsingleton_iff`; the textbook statement is its specialization to
`Localization S`. -/
recall IsLocalization.subsingleton_iff

end
