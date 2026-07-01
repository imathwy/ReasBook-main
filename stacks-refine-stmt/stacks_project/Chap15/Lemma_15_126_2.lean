import Mathlib.RingTheory.OrderOfVanishing

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

section

/- Domain triage:
* primary domain: one-dimensional local commutative algebra, comparing minimal-prime counts with
  principal-ideal quotient length;
* sampled owner API: `Ring.ord`, `minimalPrimes.finite_of_isNoetherianRing`,
  `Ring.KrullDimLE 1`, and the chapter-level principal-ideal length theorem
  `ord_pow_le_nsmul_ord`;
* source/core/bridge triage:
  `source-facing`: the Stacks bound on the number of minimal primes of a one-dimensional local
  ring cut by an element of the maximal ideal avoiding all minimal primes;
* `core/canonical`: the owner for `Module.length R (R ⧸ Ideal.span {x})` is `Ring.ord R x`;
* `bridge/view`: the textbook quotient length is already canonically owned by `Ring.ord`, so no
  parallel local length wrapper belongs in this file.

Primitive-vs-derived split:
* primitive data: the local Noetherian ring, the distinguished element `x : maximalIdeal R`, and
  the canonical membership-style minimal-prime avoidance predicate
  `∀ p ∈ minimalPrimes R, (x : R) ∉ p`;
* derived API: the quotient-length bound, expressed canonically through `Ring.ord`.
-/

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]

-- Proof sketch: pass to the reduced quotient to preserve the number of minimal primes while only
-- decreasing the quotient length. Embed the reduced ring into the product of its minimal-prime
-- quotients, show the cokernel has finite length and is killed by a power of `x`, and then compare
-- lengths after multiplication by `x^n`. Apply Lemma `15.126.1` to the one-dimensional reduced
-- quotients to conclude that each minimal prime contributes at least `1` to the total length.
/-- Lemma 15.126.2: let `(R, 𝔪)` be a Noetherian local ring of dimension `1`, and let
`x : maximalIdeal R` avoid every minimal prime of `R`. Then the number of minimal prime ideals of
`R`, written as `(minimalPrimes R).encard`, is at most the order of vanishing `Ring.ord R x`,
which is canonically `Module.length R (R ⧸ Ideal.span {x})`. The explicit equality
`ringKrullDim R = 1` from the source is replaced by the owner hypothesis `[Ring.KrullDimLE 1 R]`;
the maximal-ideal condition is absorbed into the input type `x : maximalIdeal R`. -/
theorem encard_minimalPrimes_le_ord
    (x : maximalIdeal R) (hmin : ∀ p ∈ minimalPrimes R, (x : R) ∉ p) :
    (minimalPrimes R).encard ≤ Ring.ord R x := sorry

end
