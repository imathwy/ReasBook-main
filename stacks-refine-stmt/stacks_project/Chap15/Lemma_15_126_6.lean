import Mathlib
import stacks_project.Chap15.Lemma_15_126_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalRing A]

/- Domain-style sampling for Lemma 15.126.6:
- primary domain: two-dimensional local commutative algebra, with height-one primes, principal
  divisors, and reduced principal quotients;
- sampled owner declarations:
  `exists_mem_heightOnePrimes_with_reduced_principal_quotient`,
  `IsNormalRing`,
  `IsLocalRing.notMem_maximalIdeal`,
  `principalIdeal`,
  `IsReduced`,
  `Ideal.height`;
- best owner abstraction: the source-facing input remains the single nonzero element
  `a ≠ 0`, while the canonical chapter owner driving the construction is the finite-family
  height-one-prime theorem `exists_mem_heightOnePrimes_with_reduced_principal_quotient`; the
  local-ring owner `IsLocalRing.notMem_maximalIdeal` shows that the extra source-side hypothesis
  `a ∈ maximalIdeal A` is redundant for the resulting divisibility conclusion;
- primitive data vs. derived API:
  primitive data is the element `a` together with `a ≠ 0`;
  derived API is the resulting nonzero element `c` with reduced principal quotient and a power of
  `c` divisible by `a`.

Source/core/bridge triage:
- `source-facing`: the divisibility statement for one nonzero element, with the source
  maximal-ideal formulation recovered as the nonunit case;
- `core/canonical`: `IsNormalRing`, `exists_mem_heightOnePrimes_with_reduced_principal_quotient`,
  `principalIdeal`, `IsReduced`, and the height-one-prime API on ideals;
- `bridge/view`: passing from the finite family of height-one primes appearing in the divisor of
  `a` to the single-element divisibility consequence. -/

-- Proof sketch: if `a ∉ maximalIdeal A`, then `a` is a unit by
-- `IsLocalRing.notMem_maximalIdeal`, so the conclusion is trivial with `c = 1` and `n = 0`.
-- Otherwise `a` lies in the maximal ideal, and Lemma `15.126.5` applied to the finite family of
-- height-one primes occurring in the divisor of `a` yields a common nonzero element `c` with
-- `A ⧸ (c)` reduced. For any exponent `n` at least as large as all coefficients in `div(a)`, the
-- divisor `-div(a) + div(c ^ n)` is effective, and Lemma `10.157.6` then identifies this
-- effectivity with the divisibility relation `a ∣ c ^ n`.
/-- Lemma 15.126.6: in a two-dimensional Noetherian normal local domain, every nonzero element
divides a power of some nonzero element `c` such that the principal quotient
`A ⧸ principalIdeal c` is reduced. -/
theorem exists_nonzero_reduced_principal_quotient_dvd_pow
    (hdim : ringKrullDim A = 2) (a : A) (ha0 : a ≠ 0) :
    ∃ c : A, c ≠ 0 ∧ IsReduced (A ⧸ principalIdeal c) ∧ ∃ n : ℕ, a ∣ c ^ n := sorry

end
