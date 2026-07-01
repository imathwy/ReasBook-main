import Mathlib
import stacks_project.Chap15.Lemma_15_109_1

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u

section

variable {A Ah : Type u}
variable [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A

/-
Domain-style sampling:
- primary domain: minimal-prime comparison between a Noetherian local ring's henselization and
  maximal-ideal completion;
- sampled owner declarations:
  `minimalPrimes`,
  `henselizationCompletionComparison`,
  `branchNumber_eq_completion_minimalPrimes_iff_radical_map_minimalPrime_isPrime`,
  `ringKrullDim_eq_ringKrullDim_maximalIdeal_adicCompletion`;
- best owner abstraction: the source-facing theorem is a `bridge/view` statement over the
  canonical comparison map `henselizationCompletionComparison A Ah`, while the minimal-prime data
  should use the owner subtype `minimalPrimes _` rather than a raw ideal together with a separate
  membership hypothesis;
- primitive data: a minimal prime `q : minimalPrimes ACompletion` whose quotient has Krull
  dimension `1`;
- derived API: existence of a minimal prime `qh : minimalPrimes Ah` whose extension to
  `ACompletion` has radical `q`.

Source/core/bridge triage:
- `source-facing`: the existence theorem below for a one-dimensional completed branch;
- `core/canonical`: `minimalPrimes`, `AdicCompletion`, `Ideal.map`, `Ideal.radical`, and the
  completion comparison owner `henselizationCompletionComparison`;
- `bridge/view`: passage from the chosen henselization to the completion along that canonical map.
-/

-- Proof sketch: reduce first to the henselian case using the standard identification of the
-- completions of `A` and `Ah`. Then apply Lemma `15.109.4` to the quotient of `ACompletion` by the
-- kernel of the localization map at `q`, use the one-dimensional minimal-prime hypothesis to
-- algebraize that quotient, and finally descend along the henselian local map to obtain a minimal
-- prime `qh` of `Ah` whose extension to the completion has radical `q`.
/-- Lemma 15.109.5: let `(A, 𝔪)` be a Noetherian local ring with chosen henselization `Ah`, let
`ACompletion = AdicCompletion (maximalIdeal A) A`, and let `q` be a minimal prime of
`ACompletion` such that `dim (ACompletion / q) = 1`. Then there exists a minimal prime `qh` of
`Ah` such that `q = √(qh ACompletion)`, where `qh ACompletion` is taken along the canonical
comparison map `Ah → ACompletion`. -/
theorem exists_minimalPrime_henselization_of_completion_minimalPrime_dim_one
    (q : minimalPrimes ACompletion) (hdim : ringKrullDim (ACompletion ⧸ q.1) = 1) :
    ∃ qh : minimalPrimes Ah,
      (q : Ideal ACompletion) =
        Ideal.radical (Ideal.map (henselizationCompletionComparison A Ah) qh) := sorry

end
