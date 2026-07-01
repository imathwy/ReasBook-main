import Mathlib
import stacks_project.Chap15.Lemma_15_45_7
import stacks_project.Chap15.Lemma_15_109_2
import stacks_project.Chap15.Lemma_15_109_5

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u

section

variable {A Ah Ash Ahatsh : Type u}
variable [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]
variable [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]
variable [CommRing Ahatsh] [Algebra (AdicCompletion (maximalIdeal A) A) Ahatsh]
variable [IsStrictHenselizationOf (AdicCompletion (maximalIdeal A) A) Ahatsh]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A

/- Domain-style sampling:
- primary domain: one-dimensional Noetherian local rings, their henselizations, strict
  henselizations, and maximal-ideal completions;
- sampled owner declarations:
  `branchNumber`,
  `geometricBranchNumber`,
  `branchNumber_eq_completion_minimalPrimes_iff_radical_map_minimalPrime_isPrime`,
  `exists_minimalPrime_henselization_of_completion_minimalPrime_dim_one`,
  `geometricBranchNumber_le_completion`,
  `ringKrullDim_strictHenselization_eq`;
- best owner abstraction: the source-facing owners remain `branchNumber` and
  `geometricBranchNumber`, while the completion comparison and strict-henselization comparison are
  derived from the canonical Chapter 15 bridges already introduced in `15.109.1`, `15.109.2`,
  `15.109.5`, and `15.45.7`;
- primitive data: the one-dimensional Noetherian local ring `A`, a chosen henselization `Ah`, a
  chosen strict henselization `Ash`, and a chosen strict henselization `Ahatsh` of `ACompletion`;
- derived API: the minimal-prime count `(minimalPrimes ACompletion).encard`, the canonical
  completion comparison inequalities, and the one-dimensional quotient criterion on minimal
  primes of `ACompletion`.

Source/core/bridge triage:
- `source-facing`: the two branch-count equalities below;
- `core/canonical`: `branchNumber`, `geometricBranchNumber`, `minimalPrimes`, `ACompletion`,
  and the Krull-dimension owners;
- `bridge/view`: the completion comparison criteria from `15.109.1`, `15.109.2`, and `15.109.5`,
  together with `ringKrullDim_strictHenselization_eq`.
-/

-- Proof sketch: combine Lemmas `15.109.1`, `15.109.2`, and `15.109.5`. The dimension hypothesis on
-- `A` transfers to `ACompletion` by Lemma `15.43.1`, so every minimal prime of `ACompletion`
-- satisfies the one-dimensional quotient hypothesis needed to produce a minimal prime of `Ah`.
/-- For a one-dimensional Noetherian local ring, the number of branches equals the number of
minimal primes of the maximal-ideal completion. -/
theorem branchNumber_eq_completion_minimalPrimes_of_ringKrullDim_eq_one
    (hdim : ringKrullDim A = 1) :
    branchNumber A Ah = (minimalPrimes ACompletion).encard := sorry

-- Proof sketch: apply the ordinary branch-count statement to the strict henselization `Ash`,
-- use Lemma `15.45.7` to keep the Krull dimension equal to `1` after strict henselization, and
-- compare `Ash` with `Ahatsh` through the canonical strict-henselization completion bridge from
-- Lemma `15.109.1`. The compatible residue-field map used to build that bridge is internal and
-- should not appear in the public API here.
/-- Lemma 15.109.7: if `(A, 𝔪)` is a one-dimensional Noetherian local ring, then the number of
geometric branches of `A` equals the number of geometric branches of its maximal-ideal
completion. -/
theorem geometricBranchNumber_eq_completion_of_ringKrullDim_eq_one
    (hdim : ringKrullDim A = 1) :
    geometricBranchNumber A Ash =
      geometricBranchNumber ACompletion Ahatsh := sorry

end
