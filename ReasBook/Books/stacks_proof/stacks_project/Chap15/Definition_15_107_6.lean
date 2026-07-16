import Mathlib.Data.Set.Card
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import stacks_proof.stacks_project.Chap10.Definition_10_155_3
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

/-
Domain-style sampling:
- primary domain: local commutative algebra of henselizations, strict henselizations, and minimal
  primes;
- sampled owner declarations:
  `IsHenselizationOf`,
  `IsStrictHenselizationOf`,
  `minimalPrimes`;
- best owner abstraction: the source-facing branch-count owners should take the base local ring
  and the chosen henselization/strict henselization explicitly, while the counted minimal-prime
  set remains the canonical derived object on the chosen target ring;
- primitive data: the base local ring together with the chosen henselization/strict-henselization
  owner instance;
- derived API: the minimal-prime count `(minimalPrimes _).encard` on the chosen target ring.

Source/core/bridge triage:
- `source-facing`: `branchNumber`, `geometricBranchNumber`;
- `core/canonical`: `IsHenselizationOf`, `IsStrictHenselizationOf`, `minimalPrimes`;
- `bridge/view`: direct unfolding of the source-facing definitions to `(minimalPrimes _).encard`.
-/

variable (A : Type u)
variable [CommRing A] [IsLocalRing A]

/-- Definition 15.107.6: for a chosen henselization `Ah` of the local ring `A`, the number of
branches of `A` is the extended natural number counting the minimal primes of `Ah`. -/
@[stacks 0C26]
abbrev branchNumber (Ah : Type u) [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah] : ℕ∞ :=
  (minimalPrimes Ah).encard

/-- Definition 15.107.6: for a chosen strict henselization `Ash` of the local ring `A`, the
number of geometric branches of `A` is the extended natural number counting the minimal primes of
`Ash`. -/
@[stacks 0C26]
abbrev geometricBranchNumber
    (Ash : Type u) [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash] : ℕ∞ :=
  (minimalPrimes Ash).encard
