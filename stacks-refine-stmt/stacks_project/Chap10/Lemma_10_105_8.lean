import Mathlib
import stacks_project.Chap10.Definition_10_105_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Ideal

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-
Domain-style sampling in the catenary API:
- topological owner: `CatenarySpace (PrimeSpectrum R)`
- ring owner: `IsCatenaryRing R`
- universal owner: `UniversallyCatenaryRing R`
- layer here: `bridge/view`, since this item characterizes the existing owners through quotients by
  minimal primes

Primitive data already belongs to the owner abstractions from `Lemma_10_105_2` and
`Definition_10_105_3`; this file should only expose the minimal-prime reduction theorems.
-/

-- Proof sketch: for the forward implication, pass catenarity to each irreducible component
-- `Spec (R ⧸ p)` cut out by a minimal prime. For the reverse implication, every chain of primes in
-- `R` lies over some minimal prime, reducing the catenary condition to the corresponding quotient.
/-- Lemma 10.105.8 (1): a Noetherian ring is catenary if and only if the quotient by every
minimal prime is catenary. -/
theorem isCatenaryRing_iff_forall_quotient_by_minimalPrime :
    IsCatenaryRing R ↔ ∀ p ∈ minimalPrimes R, IsCatenaryRing (R ⧸ p) := sorry

-- Proof sketch: use the same minimal-prime reduction after base change to finite type algebras
-- over `R`, applying the first clause to each such algebra and its quotients by minimal primes.
/-- Lemma 10.105.8 (2): a Noetherian ring is universally catenary if and only if the quotient by
every minimal prime is universally catenary. -/
theorem universallyCatenaryRing_iff_forall_quotient_by_minimalPrime :
    UniversallyCatenaryRing R ↔
      ∀ p ∈ minimalPrimes R, UniversallyCatenaryRing (R ⧸ p) := sorry

end
