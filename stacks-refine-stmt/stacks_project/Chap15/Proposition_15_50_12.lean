import Mathlib
import stacks_project.Chap10.Definition_10_160_1
import stacks_project.Chap15.Definition_15_50_1
import stacks_project.Chap15.Proposition_15_50_10
import stacks_project.Chap15.Proposition_15_50_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Domain-style sampling:
- primary domain: commutative algebra of `G`-rings and their permanence properties;
- sampled owner declarations of the same kind:
  `IsGRing`,
  `CompletedLocalizationAtPrime`,
  `isGRing_of_essFiniteType`,
  the complete-local `IsGRing` instance from Proposition `15.50.6`;
- best owner abstraction: the chapter owner class `IsGRing`;
- primitive vs. derived:
  the primitive public data are the ambient ring/algebra hypotheses in each source clause;
  the field and complete-local examples are direct owner recall, the Dedekind-domain clause is a
  source-facing owner instance, and the finite-type clause is only a thin source-facing
  specialization of the canonical essentially-finite-type transfer theorem.

Source/core/bridge triage:
- `source-facing`: the Dedekind-domain and finite-type clauses recorded in this proposition;
- `core/canonical`: `IsGRing` and `isGRing_of_essFiniteType`;
- `bridge/view`: the finite-type specialization and the `ℤ` specialization of the
  Dedekind-domain characteristic-zero instance.
-/

section

variable (K : Type u) [Field K]

/- Proposition 15.50.12: fields are `G`-rings. This is the canonical field instance from
Definition `15.50.1`. -/
#check (inferInstance : IsGRing K)

end

section

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]

/- Proposition 15.50.12: a Noetherian complete local ring is a `G`-ring. This is the
canonical instance supplied by Proposition `15.50.6`. -/
#check (inferInstance : IsGRing R)

end

section

variable (R : Type u) [CommRing R] [IsDedekindDomain R] [CharZero (FractionRing R)]

-- Proof sketch: a Dedekind domain is Noetherian and has Krull dimension at most `1`. Localizing
-- at a nonzero prime gives a discrete valuation ring, whose completion is again a discrete
-- valuation ring, so the defining formal fibres are geometrically regular; the zero prime gives
-- the fraction field case.
/-- Proposition 15.50.12: a Dedekind domain whose fraction field has characteristic zero is a
`G`-ring. -/
instance isGRing_of_isDedekindDomain_of_fractionRing_charZero : IsGRing R := sorry

end

section

/- Proposition 15.50.12: the ring of integers `ℤ` is a `G`-ring, by the
Dedekind-domain characteristic-zero instance above. -/
#check (inferInstance : IsGRing ℤ)

end

section

variable (R : Type u) {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

-- Proof sketch: finite type algebras are essentially finite type, so this is the finite-type
-- specialization of Proposition `15.50.10`.
/-- Proposition 15.50.12: a finite type algebra over a `G`-ring is again a `G`-ring. -/
theorem isGRing_of_finiteType [IsGRing R] [Algebra.FiniteType R S] : IsGRing S := by
  letI : Algebra.EssFiniteType R S := inferInstance
  exact isGRing_of_essFiniteType R

end
