import Mathlib.Tactic.Recall
import StacksProject_2024.Chap10.Definition_10_162_1
import StacksProject_2024.Chap10.Lemma_10_162_8
import StacksProject_2024.Chap10.Proposition_10_162_15_Nagata
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-- Helper for Chap10 Proposition 10 162 16: every prime quotient of a field is `N-2`. -/
private lemma fieldPrimeQuotientIsN2
    (K : Type u) [Field K] (p : Ideal K) [p.IsPrime] : IsN2Ring (K ⧸ p) := by
  -- The only prime ideal of a field is `⊥`, so transport the field `N-2` instance across the
  -- quotient equivalence.
  have hp : p = ⊥ := Ideal.eq_bot_of_prime p
  subst p
  letI : IsN2Ring K := instIsN2Ring K
  exact isN2Ring_of_ringEquiv (RingEquiv.quotientBot K).symm

/- Domain-style sampling:
- primary domain: commutative algebra of Nagata rings and universally Japanese rings, together
  with the standard source-facing permanence and example classes listed in Proposition 10.162.16;
- sampled owner declarations in the same chapter:
  `NagataRing`,
  `UniversallyJapaneseRing`,
  `nagataRing_of_noetherian_completeLocalRing`,
  `nagataRing_tfae_finiteType_algebra_nagata_universallyJapanese_noetherian`.
- best owner abstraction: `NagataRing` is the source-facing owner for the proposition, while
  `UniversallyJapaneseRing` is the canonical downstream bridge owner derived from it.
- primitive data vs. derived API:
  the primitive data here are only the source-faithful hypotheses for the field, complete-local,
  Dedekind-domain, and integer examples;
  the finite-type stability theorem and the `NagataRing → UniversallyJapaneseRing` bridge are
  derived owner API and should be reused from the chapter TFAE proposition rather than rebuilt as
  parallel local proof packages.

Source/core/bridge triage:
- `source-facing`: the example instances and the named finite-type closure theorem recorded in this
  proposition;
- `core/canonical`: the owner classes `NagataRing` and `UniversallyJapaneseRing`, plus the
  complete-local criterion `nagataRing_of_noetherian_completeLocalRing`;
- `bridge/view`: extracting the finite-type closure and universally-Japanese consequences from the
  earlier owner theorem
  `nagataRing_tfae_finiteType_algebra_nagata_universallyJapanese_noetherian`.
-/

section

variable (K : Type u) [Field K]

/-- Fields are Nagata rings. -/
-- Proof sketch: a field is Noetherian, and its only prime ideal is `(0)`, so every prime quotient
-- is again a field; fields are `N-2`.
instance : NagataRing K := by
  -- A field is Noetherian, and the helper supplies `N-2` for each prime quotient.
  constructor
  intro p hp
  exact fieldPrimeQuotientIsN2 K p

end

section

variable (R : Type u) [CommRing R] [IsCompleteLocalRing R] [IsNoetherianRing R]

/- Noetherian complete local rings are Nagata rings. This is the source-facing owner from
`Lemma_10_162_8`, reused directly here instead of keeping a second parallel instance. -/
recall nagataRing_of_noetherian_completeLocalRing

end

section

variable (R : Type u) [CommRing R] [IsDedekindDomain R] [CharZero (FractionRing R)]

/-- Helper for Chap10 Proposition 10 162 16: a Dedekind domain with characteristic-zero fraction
field is `N-2`. -/
private lemma dedekindDomainIsN2_of_fractionRing_charZero : IsN2Ring R := by
  -- Dedekind domains are normal Noetherian domains, so `N-1` upgrades to `N-2` in characteristic
  -- zero.
  have hN1 : IsN1Ring R := isN1Ring_of_isIntegrallyClosed_noetherian_domain
  exact (isN1Ring_iff_isN2Ring_of_noetherian_of_fractionRing_charZero R).mp hN1

/-- Helper for Chap10 Proposition 10 162 16: every prime quotient of such a Dedekind domain is
`N-2`. -/
private lemma dedekindPrimeQuotientIsN2_of_fractionRing_charZero
    (p : Ideal R) [p.IsPrime] : IsN2Ring (R ⧸ p) := by
  -- The zero prime quotient is transported from `R`; every nonzero prime is maximal, hence has
  -- field quotient.
  by_cases hpbot : p = ⊥
  · subst p
    letI : IsN2Ring R := dedekindDomainIsN2_of_fractionRing_charZero R
    exact isN2Ring_of_ringEquiv (RingEquiv.quotientBot R).symm
  · have hpprime : p.IsPrime := inferInstance
    have hpmax : p.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hpbot hpprime
    letI : p.IsMaximal := hpmax
    letI : Field (R ⧸ p) := Ideal.Quotient.field p
    exact instIsN2Ring (R ⧸ p)

/-- Chap10 Proposition 10 162 16: Dedekind domains whose fraction field has characteristic zero
are Nagata rings. -/
-- Proof sketch: a Dedekind domain is Noetherian. For a prime ideal `p`, either `p = ⊥`, in which
-- case `R ⧸ p = R` is `N-2` by Lemma `10.161.11`, or `p` is maximal, in which case `R ⧸ p` is a
-- field and hence `N-2`.
instance nagataRing_of_isDedekindDomain_of_fractionRing_charZero : NagataRing R := by
  -- Dedekind domains are Noetherian, and the helper proves the required `N-2` quotient condition.
  constructor
  intro p hp
  exact dedekindPrimeQuotientIsN2_of_fractionRing_charZero R p

end

section

/- The ring of integers is a Nagata ring. This is the direct specialization of the canonical
Dedekind-domain characteristic-zero owner instance above, so no separate `ℤ`-specific instance is
kept here. -/
#check (inferInstance : NagataRing ℤ)

end

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

-- Proof sketch: finite type algebras over a Noetherian ring are Noetherian. For a prime ideal
-- `q` of `S`, the quotient `S ⧸ q` is a finite type domain over `R ⧸ (q.comap (algebraMap R S))`,
-- and the latter is `N-2` because `R` is Nagata. Thus `S ⧸ q` is `N-2`, giving the Nagata
-- property for `S`.
/-- Finite type ring extensions of Nagata rings are Nagata. Together with the field,
complete-local, `ℤ`, and Dedekind-domain cases, this yields the full list of Nagata rings in
Chap10 Proposition 10 162 16. -/
@[stacks 0335]
theorem nagataRing_of_finiteType (R : Type u) {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [NagataRing R] [Algebra.FiniteType R S] : NagataRing S := by
  let hR : NagataRing R := inferInstance
  have htfae :
      List.TFAE
        [ NagataRing R,
          ∀ (T : Type v) [CommRing T] [Algebra R T] [Algebra.FiniteType R T], NagataRing T,
          UniversallyJapaneseRing.{u, v} R ∧ IsNoetherianRing R ] :=
    nagataRing_tfae_finiteType_algebra_nagata_universallyJapanese_noetherian
  let hFiniteType := (htfae.out 0 1).1 hR
  exact hFiniteType S

end
