import Mathlib
import StacksProject_2024.Chap15.Lemma_15_109_1

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u

noncomputable section

section

variable {A Ah : Type u}
variable [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A

/-
Domain-style sampling:
- primary domain: Noetherian local commutative algebra of henselizations, maximal-ideal
  completions, and minimal primes;
- sampled owner declarations:
  `branchNumber`,
  `minimalPrimes`,
  `henselizationCompletionComparison`,
  `henselizationCompletion_surjOn_minimalPrimes`;
- best owner abstraction: the source-facing equality criterion should use the canonical owner
  subtype `minimalPrimes Ah` for the minimal primes of the chosen henselization, while the
  comparison map to the completion remains the owner-derived
  `henselizationCompletionComparison A Ah`;
- primitive data: the Noetherian local ring `A`, its chosen henselization `Ah`, and the canonical
  comparison map `Ah → ACompletion`;
- derived API: the branch count `branchNumber A Ah`, the minimal-prime count
  `(minimalPrimes ACompletion).encard`, and the primality of the radicals of extended minimal
  primes.

Source/core/bridge triage:
- `source-facing`: the equivalence below;
- `core/canonical`: `minimalPrimes`, `branchNumber`, `AdicCompletion`, `Ideal.map`,
  `Ideal.radical`;
- `bridge/view`: `henselizationCompletionComparison A Ah`.
-/
-- Proof sketch: by Lemma `15.109.1`, the minimal primes of `ACompletion` surject onto the minimal
-- primes of `Ah`, so equality of branch counts is equivalent to every fiber over a minimal prime
-- of `Ah` consisting of a single minimal prime of `ACompletion`. Since both rings are Noetherian
-- by Lemma `15.45.3` and Algebra, Lemma `10.31.6`, this uniqueness is equivalent to the radical
-- of the extended ideal `qACompletion` being prime for each minimal prime `q` of `Ah`.
/-- Lemma 15.109.2: for a Noetherian local ring `A` with chosen henselization `Ah`, the number of
branches of `A` equals the number of minimal primes of the completion
`ACompletion = AdicCompletion (maximalIdeal A) A` if and only if for every minimal prime `q` of
`Ah`, the radical `√(qACompletion)` is prime. -/
theorem branchNumber_eq_completion_minimalPrimes_iff_radical_map_minimalPrime_isPrime
    :
    branchNumber A Ah = (minimalPrimes ACompletion).encard ↔
      ∀ q : minimalPrimes Ah,
        (Ideal.radical (Ideal.map (henselizationCompletionComparison A Ah) q)).IsPrime :=
      sorry

end
