import Mathlib
import StacksProject_2024.Chap10.Proposition_10_162_16

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v

/-
Domain triage: this file is in the commutative algebra of Nagata and universally Japanese rings,
with the target construction the integral closure of a reduced essentially finite type algebra.

Sampled owner API in this domain:
- `NagataRing`, the source-facing owner from `Definition_10_162_1`;
- `UniversallyJapaneseRing`, the core owner abstraction already present upstream in the chapter;
- `UniversallyJapaneseRing.finiteType_algebra_isN2Ring`, the owner-side `N-2` API for finite type
  domains;
- `IsN2Ring.integralClosure_finite`, the canonical finite-normalization field for finite
  fraction-field extensions;
- the project instance `[NagataRing R] → [UniversallyJapaneseRing R]` from
  `Proposition_10_162_16`, which supplies the source-to-owner bridge for the theorem below.

Source/core/bridge triage for the declarations below:
- `integralClosure_finite_of_nagataRing_of_essFiniteType_of_isReduced` is `source-facing`, since
  Lemma 10.162.2 is stated for Nagata rings;
- `UniversallyJapaneseRing`, `IsN2Ring`, and `integralClosure` are the `core/canonical` owners;
- the owner-level bridge is the existing instance `[NagataRing R] → [UniversallyJapaneseRing R]`,
  reused directly inside the theorem rather than through a parallel local wrapper.

Primitive data: the rings `R`, `S`, the `R`-algebra structure on `S`, and the hypotheses
`Algebra.EssFiniteType R S` and `IsReduced S`.
Derived API: finiteness of `integralClosure R S`.
-/

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.EssFiniteType R S] [IsReduced S]

/-- Lemma 10.162.2: if `R` is a Nagata ring and `S` is a reduced `R`-algebra essentially of
finite type, then the integral closure of `R` in `S` is finite over `R`. -/
-- Proof sketch: write the reduced essentially-finite-type algebra `S` as a subring of the product
-- of the residue fields at its finitely many minimal primes; for each factor, use the Nagata
-- hypothesis on the corresponding quotient domain of `R` to obtain finiteness of the integral
-- closure, then combine these finitely many finite modules inside the product. The canonical
-- owner bridge `[NagataRing R] → [UniversallyJapaneseRing R]` from Proposition `10.162.16` is
-- reused directly in the proof.
theorem integralClosure_finite_of_nagataRing_of_essFiniteType_of_isReduced
    [NagataRing R] :
    Module.Finite R (integralClosure R S) := by
  haveI : UniversallyJapaneseRing.{u, v} R := inferInstance
  sorry

end
