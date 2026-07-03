import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R] (S : Submonoid R)
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (N : Submodule R M)

/- Layering for this item:
* source-facing statement: localization respects quotients.
* core/canonical owner: `localizedQuotientEquiv`.
* bridge/view: its symmetric form gives the textbook orientation.
-/

/- Lemma 10.9.13: localization respects quotients. Mathlib's canonical comparison is
`localizedQuotientEquiv S N`, which identifies the quotient of the localized module by the
localized submodule with the localization of the quotient. -/
recall localizedQuotientEquiv

/- Companion check: the textbook-oriented equivalence
`S⁻¹ (M ⧸ N) ≃ (S⁻¹ M) ⧸ S⁻¹ N` is the inverse of the canonical library comparison. -/
#check (localizedQuotientEquiv S N).symm

end
