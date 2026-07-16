import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_66_1
import stacks_proof.stacks_project.Chap10.Lemma_10_66_4
import stacks_proof.stacks_project.Chap10.Lemma_10_66_5

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

/-- Helper for Lemma 10.66.7: an element lying in a weakly associated prime annihilates some
nonzero module element. -/
lemma exists_smul_eq_zero_of_mem_weaklyAssociatedPrime {𝔮 : Ideal R} {f : R}
    (h𝔮 : 𝔮 ∈ weaklyAssociatedPrimes R M) (hf : f ∈ 𝔮) :
    ∃ m : M, m ≠ 0 ∧ f • m = 0 := by
  rw [mem_weaklyAssociatedPrimes_iff] at h𝔮
  rcases h𝔮 with ⟨m, hm⟩
  -- Minimal-prime avoidance produces a coefficient outside `torsionOf m` whose product with `f`
  -- lies inside `torsionOf m`.
  obtain ⟨g, hg, hfg⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes hm hf
  refine ⟨g • m, ?_, ?_⟩
  · -- Since `g` avoids the torsion ideal, the scaled element `g • m` is nonzero.
    intro hgm
    have hg_mem : g ∈ Ideal.torsionOf R M m := by
      rw [Ideal.mem_torsionOf_iff]
      exact hgm
    exact hg hg_mem
  · -- Membership of `f * g` in the torsion ideal says exactly that `f` kills `g • m`.
    rw [Ideal.mem_torsionOf_iff] at hfg
    simpa [smul_smul, mul_comm] using hfg

/-- Helper for Lemma 10.66.7: every element of the kernel of multiplication by `f` is annihilated
by `f` inside that kernel module. -/
lemma mem_torsionOf_ker_lsmul {f : R}
    (n : LinearMap.ker (LinearMap.lsmul R M f)) :
    f ∈ Ideal.torsionOf R (LinearMap.ker (LinearMap.lsmul R M f)) n := by
  -- Rewrite the torsion condition in the kernel module to the defining kernel equation.
  rw [Ideal.mem_torsionOf_iff]
  apply Subtype.ext
  simpa [LinearMap.mem_ker, LinearMap.lsmul_apply] using n.2

/-- Helper for Lemma 10.66.7: a zerodivisor on `M` lies in some weakly associated prime of `M`. -/
lemma exists_weaklyAssociatedPrime_of_smul_eq_zero {f : R}
    (hf : ∃ m : M, m ≠ 0 ∧ f • m = 0) :
    ∃ 𝔮 : Ideal R, 𝔮 ∈ weaklyAssociatedPrimes R M ∧ f ∈ 𝔮 := by
  let N : Submodule R M := LinearMap.ker (LinearMap.lsmul R M f)
  rcases hf with ⟨m, hm_ne, hfm⟩
  have hm_mem : m ∈ N := by
    rw [LinearMap.mem_ker, LinearMap.lsmul_apply]
    exact hfm
  let n : N := ⟨m, hm_mem⟩
  have hn_ne : n ≠ 0 := by
    intro hn
    have hm_zero : m = 0 := by
      simpa [n] using congrArg Subtype.val hn
    exact hm_ne hm_zero
  have hN_not_subsingleton : ¬ Subsingleton N := by
    intro hN
    exact hn_ne (Subsingleton.elim n 0)
  have hN_nontrivial : Nontrivial N := not_subsingleton_iff_nontrivial.mp hN_not_subsingleton
  letI : Nontrivial N := hN_nontrivial
  -- The nontrivial kernel has a weakly associated prime by Lemma `10.66.5`.
  obtain ⟨𝔮, h𝔮N⟩ : (weaklyAssociatedPrimes R N).Nonempty := weaklyAssociatedPrimes.nonempty
  have h𝔮M : 𝔮 ∈ weaklyAssociatedPrimes R M := by
    -- Lemma `10.66.4` transports weak association along the injective subtype map.
    exact
      weaklyAssociatedPrimes.subset_of_injective
        (R := R) (M' := N) (M := M) (f := N.subtype) N.subtype_injective h𝔮N
  rw [mem_weaklyAssociatedPrimes_iff] at h𝔮N
  rcases h𝔮N with ⟨x, hx⟩
  have hf_torsion : f ∈ Ideal.torsionOf R N x :=
    mem_torsionOf_ker_lsmul (R := R) (M := M) x
  have hf_mem : f ∈ 𝔮 := hx.1.2 hf_torsion
  exact ⟨𝔮, h𝔮M, hf_mem⟩

/-- Lemma 10.66.7: the union of the weakly associated primes of the `R`-module `M` is exactly the
set of zerodivisors on `M`. This is the weakly associated analogue of the canonical mathlib theorem
`biUnion_associatedPrimes_eq_zero_divisors`. -/
-- Proof sketch: if `f ∈ 𝔮 ∈ WeakAss(M)`, choose `m : M` such that `𝔮` is minimal over
-- `Ann(m)`. Minimality gives some `g ∉ 𝔮` and `n > 0` with `f ^ n • (g • m) = 0`; taking `n`
-- minimal shows `f` kills a nonzero element of `M`, so `f` is a zerodivisor. Conversely, if `f`
-- kills a nonzero element, the submodule `N = {m | f • m = 0}` is nontrivial, so Lemma 10.66.5
-- gives a weakly associated prime of `N`, and Lemma 10.66.4 carries it to a weakly associated
-- prime of `M` containing `f`.
@[stacks 05C3]
theorem biUnion_eq_zero_divisors :
    ⋃ 𝔮 ∈ weaklyAssociatedPrimes R M, 𝔮 =
      { f : R | ∃ m : M, m ≠ 0 ∧ f • m = 0 } := by
  ext f
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨𝔮, h𝔮, hf⟩
    -- An element inside a weakly associated prime annihilates a nonzero vector.
    exact exists_smul_eq_zero_of_mem_weaklyAssociatedPrime h𝔮 hf
  · intro hf
    -- A zerodivisor yields a nontrivial kernel of multiplication, hence a weakly associated prime.
    rcases exists_weaklyAssociatedPrime_of_smul_eq_zero hf with ⟨𝔮, h𝔮, hf𝔮⟩
    exact ⟨𝔮, h𝔮, hf𝔮⟩

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
