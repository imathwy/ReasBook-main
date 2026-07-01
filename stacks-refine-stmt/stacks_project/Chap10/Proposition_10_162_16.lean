import Mathlib.Tactic.Recall
import stacks_project.Chap10.Definition_10_162_1
import stacks_project.Chap10.Lemma_10_162_8
import stacks_project.Chap10.Proposition_10_162_15_Nagata

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

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
instance : NagataRing K := sorry

end

section

variable (R : Type u) [CommRing R] [IsCompleteLocalRing R] [IsNoetherianRing R]

/- Noetherian complete local rings are Nagata rings. This is the source-facing owner from
`Lemma_10_162_8`, reused directly here instead of keeping a second parallel instance. -/
recall nagataRing_of_noetherian_completeLocalRing

end

section

variable (R : Type u) [CommRing R] [IsDedekindDomain R] [CharZero (FractionRing R)]

/-- Dedekind domains whose fraction field has characteristic zero are Nagata rings. -/
-- Proof sketch: a Dedekind domain is Noetherian. For a prime ideal `p`, either `p = ⊥`, in which
-- case `R ⧸ p = R` is `N-2` by Lemma `10.161.11`, or `p` is maximal, in which case `R ⧸ p` is a
-- field and hence `N-2`.
instance nagataRing_of_isDedekindDomain_of_fractionRing_charZero : NagataRing R := sorry

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
/-- Proposition 10.162.16: finite type ring extensions of Nagata rings are Nagata. Together with
the field, complete-local, `ℤ`, and Dedekind-domain cases, this yields the full list of Nagata
rings in the proposition. -/
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
