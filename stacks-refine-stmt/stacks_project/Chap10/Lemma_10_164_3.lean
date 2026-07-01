import Mathlib
import stacks_project.Chap10.Definition_10_37_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/- Domain triage:
* primary domain: commutative algebra of faithfully flat descent for normal rings;
* sampled owner-style declarations: `IsNormalRing`, `RingHom.FaithfullyFlat`,
  `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective`, and `Localization.localRingHom` together
  with the chapter owner theorem `isNormalRing_of_flat_of_fiber`;
* core/canonical owners: `IsNormalRing` for the target property and `RingHom.FaithfullyFlat` for
  the map property;
* primitive vs. derived API: the primitive inputs are only the ring map `f`, the faithful-flatness
  witness `hff`, and the target normality instance on `S`; the induced lying-over primes,
  localized maps, and local faithful-flatness are canonical derived data and should not become
  extra public structure;
* layer split: this theorem is a source-facing descent statement, not a replacement owner.
-/

-- Proof sketch: unpack `IsNormalRing` primewise. For each `p : PrimeSpectrum R`, use
-- `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective` to choose `q : PrimeSpectrum S` above
-- `p`. The induced local map `Localization.AtPrime p.asIdeal → Localization.AtPrime q.asIdeal` is
-- the canonical `Localization.localRingHom`; it is flat by localization and faithfully flat since
-- it is a flat local map. Because `S` is normal, the target localization is a normal domain. This
-- gives that the source localization is a normal domain, so the defining owner predicate
-- `IsNormalRing R` holds.
/-- Lemma 10.164.3: a faithfully flat morphism from `R` to a normal ring `S` forces `R` to be a
normal ring. -/
theorem isNormalRing_of_faithfullyFlat (f : R →+* S) (hff : f.FaithfullyFlat) [IsNormalRing S] :
    IsNormalRing R := sorry

end
