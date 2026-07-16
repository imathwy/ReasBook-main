import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_125_1

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- 
Domain-style sampling:
- primary domain: local relative fiber dimension on `Spec(S)` and the corresponding bounded
  locus;
- sampled owner declarations of the same kind:
  `relativeDimensionAt`,
  `Module.flatOverBaseLocus`,
  `Module.mem_flatOverBaseLocus`,
  `Module.isOpen_flatOverBaseLocus_of_finitePresentation`;
- best owner abstraction: the bounded-dimension locus
  `{ q : PrimeSpectrum S | relativeDimensionAt R S q ≤ n }` should be a named owner on
  `PrimeSpectrum S`, while the source-facing theorem remains the equality-at-the-point
  neighborhood statement from the Stacks lemma and the locus-membership version is only companion
  API.

Source/core/bridge triage:
- `source-facing`: the equality-at-the-point neighborhood statement of Lemma `10.125.6`;
- `core/canonical`: `relativeDimensionAt` and the induced bounded-dimension locus owner;
- `bridge/view`: the membership lemma for the named locus and the strengthened
  locus-membership-neighborhood formulation.

Primitive data are only `n` and the prime `q`; the repeated inequality
`relativeDimensionAt R S q ≤ n` is derived API from the locus owner.
-/

/-- The locus in `Spec(S)` where the relative dimension of `S/R` is at most `n`. -/
def relativeDimensionAtLELocus (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (n : ℕ) : Set (PrimeSpectrum S) :=
  { q : PrimeSpectrum S | relativeDimensionAt R S q ≤ (n : WithBot ℕ∞) }

-- Proof sketch: unfold `relativeDimensionAtLELocus`.
/-- Membership in `relativeDimensionAtLELocus` means that the local fiber dimension is at most
`n`. -/
theorem mem_relativeDimensionAtLELocus (n : ℕ) (q : PrimeSpectrum S) :
    q ∈ relativeDimensionAtLELocus R S n ↔ relativeDimensionAt R S q ≤ (n : WithBot ℕ∞) := sorry

variable [Algebra.FiniteType R S]

/-- Lemma 10.125.6: let `R → S` be a finite type ring map, let `q : Spec(S)` be a prime, and
assume the relative dimension of `S/R` at `q` is exactly `n`. Then there exists an open
neighbourhood of `q` in `Spec(S)` contained in `relativeDimensionAtLELocus R S n`, i.e. on which
the relative fiber dimension is everywhere at most `n`. -/
theorem exists_openNhdsOf_relativeDimensionAt_eq
    (n : ℕ) (q : PrimeSpectrum S) (hq : relativeDimensionAt R S q = (n : WithBot ℕ∞)) :
    ∃ U : OpenNhdsOf q, ∀ q' ∈ U, q' ∈ relativeDimensionAtLELocus R S n := sorry

-- Proof sketch: if `q ∈ relativeDimensionAtLELocus R S n`, let `m := relativeDimensionAt R S q`.
-- The equality-case argument at the actual local dimension `m` gives an open neighborhood of `q`
-- contained in the `≤ m` locus; since `m ≤ n`, that neighborhood is also contained in the
-- `≤ n` locus.
/-- Companion strengthening: if `q` already lies in the bounded-dimension locus
`relativeDimensionAtLELocus R S n`, then there is an open neighbourhood of `q` contained in that
locus. -/
theorem exists_openNhdsOf_mem_relativeDimensionAtLELocus
    (n : ℕ) (q : PrimeSpectrum S) (hq : q ∈ relativeDimensionAtLELocus R S n) :
    ∃ U : OpenNhdsOf q, ∀ q' ∈ U, q' ∈ relativeDimensionAtLELocus R S n := by
  sorry

end
