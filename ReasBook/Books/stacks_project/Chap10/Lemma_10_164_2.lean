import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.RingTheory.RingHom.FaithfullyFlat

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/- Domain triage:
* primary domain: commutative algebra of faithfully flat ring maps and reduced rings;
* sampled owner-style declarations: `RingHom.FaithfullyFlat`,
  `RingHom.FaithfullyFlat.injective`, `RingHom.faithfullyFlat_algebraMap_iff`,
  and `isReduced_of_injective`;
* core/canonical owners: `RingHom.FaithfullyFlat` for the map property and
  `isReduced_of_injective` for reducedness descent along injective maps;
* primitive vs. derived API: the only primitive input is `hff : f.FaithfullyFlat`; injectivity of
  `f` is derived canonically as `hff.injective`, so no extra wrapper or auxiliary data belongs in
  the public surface;
* layer split: this theorem is a source-facing bridge obtained by composing those canonical owner
  facts, not a replacement owner.
-/

-- Proof sketch: by Lemma `10.82.15`, a faithfully flat ring map is injective; then reducedness
-- descends along injective morphisms via the canonical theorem `isReduced_of_injective`.
/-- Lemma 10.164.2: if `f : R →+* S` is faithfully flat and `S` is reduced, then `R` is reduced. -/
theorem isReduced_of_faithfullyFlat (f : R →+* S) (hff : f.FaithfullyFlat) [IsReduced S] :
    IsReduced R :=
  isReduced_of_injective f hff.injective

end
