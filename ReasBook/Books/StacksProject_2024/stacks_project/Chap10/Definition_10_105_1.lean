import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap10.Lemma_10_105_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open Order Set

section

variable {R : Type u} [CommRing R]

/- Domain-style sampling in the catenary API:
- topological owner: `CatenarySpace X`
- prime-spectrum/irreducible-closed bridge: `PrimeSpectrum.pointsEquivIrreducibleCloseds`
- ring-level owner: `IsCatenaryRing R`
- prime-spectrum owner equivalence: `isCatenaryRing_iff_catenarySpace_primeSpectrum`

Layer triage:
- `source-facing`: Definition 10.105.1 phrases catenarity through bounded prime chains and common
  lengths of maximal prime chains in intervals of `Spec R`
- `core/canonical`: the chapter owner is already `IsCatenaryRing R` from
  `Lemma_10_105_2`, together with its bridge to `CatenarySpace (PrimeSpectrum R)`
- `bridge/view`: `PrimeSpectrum.pointsEquivIrreducibleCloseds` transports the Chapter 5
  irreducible-closed catenary API to the prime-order formulation used in the source

Primitive data belongs to the owner abstraction `IsCatenaryRing R`; the interval-chain wording is
derived API and should stay as thin owner-derived companion theorems, not as a second public class
or a bundled replacement definition.
-/

/- Definition 10.105.1: the chapter owner for catenary commutative rings is
`IsCatenaryRing R`. -/
recall IsCatenaryRing

/- Companion recall: Lemma `10.105.2` identifies ring catenarity with catenarity of the prime
spectrum. -/
recall isCatenaryRing_iff_catenarySpace_primeSpectrum

namespace IsCatenaryRing

variable [IsCatenaryRing R]

/-- In a catenary ring, every interval `[p, q]` in `Spec R` has a uniform bound on the cardinality
of its finite prime chains. This is the source-facing bounded-chain clause of Definition 10.105.1,
derived from the Chapter 5 catenary owner on `Spec R`. -/
theorem primeChainsBounded (p q : PrimeSpectrum R) (hpq : p ≤ q) :
    ∃ n : ℕ, ∀ s : Set (Set.Icc p q), IsChain (· ≤ ·) s → s.Finite → s.encard ≤ n + 1 := by
  sorry

/-- In a catenary ring, any two maximal prime chains in a fixed interval `[p, q]` have the same
cardinality. This is the source-facing equal-length clause of Definition 10.105.1, derived from
the canonical owner `IsCatenaryRing R`. -/
theorem maximalPrimeChainsHaveSameLength
    (p q : PrimeSpectrum R) (hpq : p ≤ q)
    {s t : Set (Set.Icc p q)} (hs : IsMaxChain (· ≤ ·) s) (ht : IsMaxChain (· ≤ ·) t) :
    s.encard = t.encard := by
  sorry

end IsCatenaryRing

end
