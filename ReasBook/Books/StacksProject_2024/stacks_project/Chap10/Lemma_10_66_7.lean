import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_66_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Domain triage: this item lies in commutative algebra of weakly associated primes of modules.
The owner abstraction in the chapter is the set-valued declaration `weaklyAssociatedPrimes R M`,
parallel to mathlib's `associatedPrimes R M`.

Sampled owner-style declarations in the same domain:
- `associatedPrimes R M`
- `biUnion_associatedPrimes_eq_zero_divisors`
- `associatedPrimes.subset_of_injective`
- `weaklyAssociatedPrimes.subset_of_injective`

This file is therefore `core/canonical` owner API: it identifies the union of the owner set with
the textbook zerodivisor set, and derives the regular-element reformulation from that owner
statement. Primitive data are only the ring, module, and owner set; there is no extra wrapper
structure to keep. -/

namespace weaklyAssociatedPrimes

/-- Lemma 10.66.7: the union of the weakly associated primes of the `R`-module `M` is exactly the
set of zerodivisors on `M`. This is the weakly associated analogue of the canonical mathlib theorem
`biUnion_associatedPrimes_eq_zero_divisors`. -/
-- Proof sketch: if `f ∈ 𝔮 ∈ WeakAss(M)`, choose `m : M` such that `𝔮` is minimal over
-- `Ann(m)`. Minimality gives some `g ∉ 𝔮` and `n > 0` with `f ^ n • (g • m) = 0`; taking `n`
-- minimal shows `f` kills a nonzero element of `M`, so `f` is a zerodivisor. Conversely, if `f`
-- kills a nonzero element, the submodule `N = {m | f • m = 0}` is nontrivial, so Lemma 10.66.5
-- gives a weakly associated prime of `N`, and Lemma 10.66.4 carries it to a weakly associated
-- prime of `M` containing `f`.
theorem biUnion_eq_zero_divisors :
    ⋃ 𝔮 ∈ weaklyAssociatedPrimes R M, 𝔮 =
      { f : R | ∃ m : M, m ≠ 0 ∧ f • m = 0 } := sorry

/-- Equivalent regular-element form of Lemma 10.66.7, parallel to
`biUnion_associatedPrimes_eq_compl_regular`. -/
theorem biUnion_eq_compl_regular :
    ⋃ 𝔮 ∈ weaklyAssociatedPrimes R M, 𝔮 =
      { f : R | IsSMulRegular M f }ᶜ :=
  biUnion_eq_zero_divisors.trans <| by
    simp_rw [Set.compl_setOf, isSMulRegular_iff_right_eq_zero_of_smul,
      not_forall, exists_prop, and_comm]

end weaklyAssociatedPrimes

end
