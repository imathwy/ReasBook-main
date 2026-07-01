import Mathlib.RingTheory.Jacobson.Ring

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {A : Type u} [CommRing A]

/- Domain-style sampling:
- primary domain: Jacobson rings, Jacobson-radical membership, and away-localization in
  commutative algebra;
- sampled owner declarations of the same kind:
  `Ring.jacobson`,
  `Definition_15_10_1`'s canonical Zariski-pair surface `I ≤ Ring.jacobson A`,
  `isJacobsonRing_localization`,
  `isJacobsonRing_of_isNoetherianRing_of_primeIdeal_isMaximal_or_infinite_primesOver`;
- best owner abstraction: an arbitrary away-localization target `S` with `[Algebra A S]` and
  `[IsLocalization.Away f S]`, of which `Localization.Away f` is the canonical model;
- primitive data: `f : A`, the Jacobson-radical membership `hf : f ∈ Ring.jacobson A`, and the
  ambient away-localization owner structure on `S`;
- derived API: the Zariski-pair formulation obtained from `I ≤ Ring.jacobson A` and `f ∈ I`; the
  concrete ring `Localization.Away f` is only a specialization of the owner-level statement.

Layer triage:
- `source-facing`: `isJacobsonRing_of_isLocalizationAway_of_mem_of_le_jacobson`;
- `core/canonical`: `isJacobsonRing_of_isLocalizationAway_of_mem_jacobson`, proved from the
  chapter Jacobson criterion
  `isJacobsonRing_of_isNoetherianRing_of_primeIdeal_isMaximal_or_infinite_primesOver` together
  with mathlib's away-localization infrastructure;
- `bridge/view`: the specialization `S = Localization.Away f`, supplied automatically by the
  canonical `IsLocalization.Away` instance.
-/

-- Proof sketch: apply the Noetherian Jacobson criterion to an arbitrary away-localization target
-- `S`. For a nonmaximal prime of `S`, contract to a prime of `A` and use `f ∈ Ring.jacobson A`
-- to show the corresponding quotient has dimension at least `1`; the local domain criterion from
-- Chapter 10 then gives infinitely many primes above it, so Lemma `10.61.4` makes `S` Jacobson.
variable [IsNoetherianRing A]

/-- Lemma 15.10.5 in canonical owner form: if `A` is Noetherian and `f ∈ Ring.jacobson A`, then
any away localization of `A` at `f` is a Jacobson ring. The textbook ring `Localization.Away f`
is the special case `S = Localization.Away f`. -/
theorem isJacobsonRing_of_isLocalizationAway_of_mem_jacobson
    {S : Type v} [CommRing S] [Algebra A S] (f : A) [IsLocalization.Away f S]
    (hf : f ∈ Ring.jacobson A) :
    IsJacobsonRing S := by
  sorry

/-- Lemma 15.10.5 in the textbook Zariski-pair form: if `(A, I)` is a Zariski pair with `A`
Noetherian and `f ∈ I`, then any away localization of `A` at `f` is a Jacobson ring. The
textbook ring `Localization.Away f` is the special case `S = Localization.Away f`. -/
theorem isJacobsonRing_of_isLocalizationAway_of_mem_of_le_jacobson
    {S : Type v} [CommRing S] [Algebra A S] (I : Ideal A) (hI : I ≤ Ring.jacobson A)
    (f : A) [IsLocalization.Away f S] (hf : f ∈ I) :
    IsJacobsonRing S :=
  isJacobsonRing_of_isLocalizationAway_of_mem_jacobson f (hI hf)

end
