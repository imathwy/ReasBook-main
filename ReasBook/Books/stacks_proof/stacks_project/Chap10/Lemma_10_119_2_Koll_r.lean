import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_63_1
import stacks_proof.stacks_project.Chap10.Definition_10_72_1
import stacks_proof.stacks_project.Chap10.Lemma_10_52_8
import stacks_proof.stacks_project.Chap10.Lemma_10_72_5
import stacks_proof.stacks_project.Chap10.Lemma_10_72_6
import stacks_proof.stacks_project.Chap10.Lemma_10_72_7
import stacks_proof.stacks_project.Chap10.Lemma_10_106_3
import stacks_proof.stacks_project.Chap10.Lemma_10_106_6
import stacks_proof.stacks_project.Chap10.Lemma_10_36_2
import stacks_proof.stacks_project.Chap10.Lemma_10_157_2
import stacks_proof.stacks_project.Chap10.Lemma_10_79_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing
open scoped Pointwise ENat

section

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- A finite `R`-algebra appearing in Kollár's fourth alternative: the canonical map `R → S` is
not an isomorphism, its kernel and cokernel are annihilated by a power of the maximal ideal of
`R`, the maximal ideal is not an associated prime of `S`, and `S` is nonzero. -/
def HasKollarExceptionalFiniteExtension : Prop :=
  ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S) (_ : Module.Finite R S) (_ : Nontrivial S),
    ¬ Function.Bijective (algebraMap R S) ∧
      (∃ n : ℕ,
        (maximalIdeal R) ^ n • (RingHom.ker (algebraMap R S) : Submodule R R) = ⊥ ∧
        (maximalIdeal R) ^ n • (⊤ : Submodule R S) ≤ (Algebra.linearMap R S).range) ∧
      maximalIdeal R ∉ associatedPrimes R S

-- Proof sketch: this is just the defining existential package for the fourth alternative; later
-- arguments can unfold it to access the finite `R`-algebra, the `𝔪`-power torsion conditions on
-- the kernel and cokernel, the non-associated-prime hypothesis, and the nontriviality of the
-- target ring.
/-- Unfolding `HasKollarExceptionalFiniteExtension R` into its finite `R`-algebra data and the
torsion conditions on the kernel and cokernel of the canonical map. -/
theorem hasKollarExceptionalFiniteExtension_iff :
    HasKollarExceptionalFiniteExtension R ↔
      ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S) (_ : Module.Finite R S)
        (_ : Nontrivial S),
        ¬ Function.Bijective (algebraMap R S) ∧
          (∃ n : ℕ,
            (maximalIdeal R) ^ n • (RingHom.ker (algebraMap R S) : Submodule R R) = ⊥ ∧
            (maximalIdeal R) ^ n • (⊤ : Submodule R S) ≤ (Algebra.linearMap R S).range) ∧
          maximalIdeal R ∉ associatedPrimes R S := by
  -- This theorem is only the owner-level unpacking of the defining existential package.
  rfl

namespace RingHom

variable {R}
variable {S : Type u} [CommRing S]

/-- A specific finite ring map `f : R →+* S` realizes Kollár's exceptional finite-extension
alternative when the canonical `R`-algebra structure induced by `f` makes `S` a nontrivial finite
`R`-algebra, the map is not bijective, its kernel and cokernel are annihilated by a power of the
maximal ideal, and that maximal ideal is not an associated prime of `S`. This is a
`bridge/view` proposition from an explicit map to the owner predicate
`HasKollarExceptionalFiniteExtension R`. -/
def IsKollarExceptionalFiniteExtension (f : R →+* S) : Prop :=
  let _ : Algebra R S := f.toAlgebra
  Nontrivial S ∧
    Module.Finite R S ∧
      ¬ Function.Bijective f ∧
        (∃ n : ℕ,
          (maximalIdeal R) ^ n • (RingHom.ker f : Submodule R R) = ⊥ ∧
            (maximalIdeal R) ^ n • (⊤ : Submodule R S) ≤ (Algebra.linearMap R S).range) ∧
          maximalIdeal R ∉ associatedPrimes R S

/-- A map-level witness of Kollár's exceptional finite-extension alternative yields the canonical
owner proposition `HasKollarExceptionalFiniteExtension R`. -/
theorem hasKollarExceptionalFiniteExtension (f : R →+* S)
    (hf : f.IsKollarExceptionalFiniteExtension) :
    HasKollarExceptionalFiniteExtension R := by
  let _ : Algebra R S := f.toAlgebra
  rcases hf with ⟨hS, hfinite, hbij, htorsion, hassoc⟩
  exact (hasKollarExceptionalFiniteExtension_iff (R := R)).2
    ⟨S, inferInstance, f.toAlgebra, hfinite, hS, hbij, htorsion, hassoc⟩

end RingHom

variable [IsNoetherianRing R]

/-- Helper for Lemma 10.119.2 (Kollár): the ideal of elements of `R` killed by some power of the
maximal ideal. This is the source's "largest ideal annihilated by a power of `𝔪`". -/
def maximalIdealPowTorsionIdeal : Ideal R where
  carrier := { r : R | ∃ n : ℕ, (maximalIdeal R) ^ n ≤ Ideal.torsionOf R R r }
  zero_mem' := by
    refine ⟨0, ?_⟩
    simpa [Ideal.torsionOf_zero]
  add_mem' := by
    rintro a b ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨max m n, ?_⟩
    intro r hr
    rw [Ideal.mem_torsionOf_iff]
    have hra : r ∈ Ideal.torsionOf R R a :=
      hm <| Ideal.pow_le_pow_right (I := maximalIdeal R) (Nat.le_max_left m n) hr
    have hrb : r ∈ Ideal.torsionOf R R b :=
      hn <| Ideal.pow_le_pow_right (I := maximalIdeal R) (Nat.le_max_right m n) hr
    rw [Ideal.mem_torsionOf_iff] at hra hrb
    have hra' : r * a = 0 := by simpa [smul_eq_mul] using hra
    have hrb' : r * b = 0 := by simpa [smul_eq_mul] using hrb
    simpa [smul_eq_mul, mul_add, hra', hrb']
  smul_mem' := by
    intro a b hb
    rcases hb with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    intro r hr
    rw [Ideal.mem_torsionOf_iff]
    have hrb : r ∈ Ideal.torsionOf R R b := hn hr
    rw [Ideal.mem_torsionOf_iff] at hrb
    have hrb' : r * b = 0 := by simpa [smul_eq_mul] using hrb
    calc
      r * (a * b) = a * (r * b) := by ring
      _ = 0 := by simp [hrb']

/-- Helper for Lemma 10.119.2 (Kollár): a finite generating set for the maximal-ideal-power
torsion ideal admits one exponent annihilating the whole ideal. -/
lemma exists_pow_smul_eq_bot_maximalIdealPowTorsionIdeal :
    ∃ n : ℕ, (maximalIdeal R) ^ n • maximalIdealPowTorsionIdeal R = ⊥ := by
  obtain ⟨n, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Ideal.fg_of_isNoetherianRing (maximalIdealPowTorsionIdeal R))
  choose e he using fun i : Fin n ↦
    (show ∃ k : ℕ, (maximalIdeal R) ^ k ≤ Ideal.torsionOf R R (g i) from
      (show g i ∈ maximalIdealPowTorsionIdeal R by
        rw [← hg]
        exact Submodule.subset_span (Set.mem_range_self i)))
  refine ⟨Finset.univ.sup e, le_antisymm ?_ bot_le⟩
  intro z hz
  -- Follow the source proof: expand a generic element of `𝔪^N J` into generators of `J` and
  -- use the uniform upper bound on the chosen annihilating exponents.
  rw [← hg] at hz
  rw [Submodule.mem_ideal_smul_span_iff_exists_sum] at hz
  rcases hz with ⟨a, ha, hsum⟩
  rw [Submodule.mem_bot]
  rw [← hsum, Finsupp.sum]
  refine Finset.sum_eq_zero ?_
  intro i hi
  have hai_torsion : a i ∈ Ideal.torsionOf R R (g i) := by
    exact (he i) <|
      Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_univ i)) (ha i)
  simpa [Ideal.mem_torsionOf_iff, smul_eq_mul] using hai_torsion

/-- Helper for Lemma 10.119.2 (Kollár): if the maximal-ideal-power torsion ideal is zero, then the
maximal ideal is not an associated prime of `R` itself. -/
lemma maximalIdeal_not_mem_associatedPrimes_self_of_maximalIdealPowTorsionIdeal_eq_bot
    (hJzero : maximalIdealPowTorsionIdeal R = ⊥) :
    maximalIdeal R ∉ associatedPrimes R R := by
  intro hassoc
  have hassoc' : maximalIdeal R ∈ associatedPrimesOfModule R R := by
    simpa [associatedPrimesOfModule_eq_associatedPrimes (R := R) (M := R)] using hassoc
  rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf] at hassoc'
  rcases hassoc' with ⟨hmaxPrime, y, hy⟩
  have hy_ne : y ≠ 0 := by
    intro hy_zero
    have htop : Ideal.torsionOf R R y = ⊤ := by
      simpa [hy_zero] using (Ideal.torsionOf_eq_top_iff (R := R) y).2 hy_zero
    exact hmaxPrime.ne_top (hy.trans htop)
  have hy_memJ : y ∈ maximalIdealPowTorsionIdeal R := by
    refine ⟨1, ?_⟩
    simpa [pow_one, hy]
  have hy_zero : y = 0 := by
    have : y ∈ (⊥ : Ideal R) := by
      simpa [hJzero] using hy_memJ
    simpa using this
  exact hy_ne hy_zero

/-- Helper for Lemma 10.119.2 (Kollár): after quotienting by the maximal-ideal-power torsion ideal,
the maximal ideal is no longer an associated prime. -/
lemma maximalIdeal_not_mem_associatedPrimes_quotient_maximalIdealPowTorsionIdeal :
    maximalIdeal R ∉ associatedPrimes R (R ⧸ maximalIdealPowTorsionIdeal R) := by
  let J : Ideal R := maximalIdealPowTorsionIdeal R
  intro hassoc
  have hassoc' : maximalIdeal R ∈ associatedPrimesOfModule R (R ⧸ J) := by
    simpa [J, associatedPrimesOfModule_eq_associatedPrimes (R := R) (M := R ⧸ J)] using hassoc
  rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf] at hassoc'
  rcases hassoc' with ⟨hmaxPrime, z, hz⟩
  have hz_ne : z ≠ 0 := by
    intro hz_zero
    have htop : Ideal.torsionOf R (R ⧸ J) z = ⊤ := by
      simpa [hz_zero] using (Ideal.torsionOf_eq_top_iff (R := R) z).2 hz_zero
    exact hmaxPrime.ne_top (hz.trans htop)
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hy_not_memJ : y ∉ J := by
    intro hy_memJ
    exact hz_ne ((Ideal.Quotient.eq_zero_iff_mem).2 hy_memJ)
  obtain ⟨n, hnJ⟩ := exists_pow_smul_eq_bot_maximalIdealPowTorsionIdeal (R := R)
  have hy_memJ : y ∈ J := by
    refine ⟨n + 1, ?_⟩
    intro r hr
    rw [Ideal.mem_torsionOf_iff]
    have hr' : r ∈ (maximalIdeal R) ^ n • (maximalIdeal R : Submodule R R) := by
      simpa [pow_succ, Ideal.smul_eq_mul, mul_comm] using hr
    -- The associated-prime witness in the quotient says `𝔪 • y ⊆ J`; one more power of `𝔪`
    -- kills `J` by the uniform-exponent lemma, so `𝔪^(n+1)` kills `y`.
    refine Submodule.smul_induction_on hr' ?_ ?_
    · intro a ha b hb
      have hb_torsion :
          b ∈ Ideal.torsionOf R (R ⧸ J) (Ideal.Quotient.mk J y) := by
        simpa [hz] using hb
      rw [Ideal.mem_torsionOf_iff] at hb_torsion
      have hby_memJ : b * y ∈ J := by
        exact (Ideal.Quotient.eq_zero_iff_mem).1 <| by
          simpa [smul_eq_mul] using hb_torsion
      have ha_zero_mem : a * (b * y) ∈ (⊥ : Submodule R R) := by
        have hmem_smul : a * (b * y) ∈ (maximalIdeal R) ^ n • J := by
          exact Submodule.smul_mem_smul ha hby_memJ
        have hnJ' : (maximalIdeal R) ^ n • J = ⊥ := by
          simpa [J] using hnJ
        rw [hnJ'] at hmem_smul
        exact hmem_smul
      have ha_zero : a * (b * y) = 0 := by
        simpa [Submodule.mem_bot] using ha_zero_mem
      simpa [smul_eq_mul, mul_assoc] using ha_zero
    · intro a b ha hb
      have ha' : a * y = 0 := by simpa [smul_eq_mul] using ha
      have hb' : b * y = 0 := by simpa [smul_eq_mul] using hb
      rw [add_smul, ha, hb, zero_add]
  exact hy_not_memJ hy_memJ

/-- Helper for Lemma 10.119.2 (Kollár): if the maximal-ideal-power torsion ideal is nonzero, then
quotienting by it already gives Kollár's exceptional finite extension. -/
lemma hasKollarExceptionalFiniteExtension_of_nonzero_maximalIdealPowTorsionIdeal
    (hnotArtinian : ¬ IsArtinianRing R)
    (hJnonzero : maximalIdealPowTorsionIdeal R ≠ ⊥) :
    HasKollarExceptionalFiniteExtension R := by
  let J : Ideal R := maximalIdealPowTorsionIdeal R
  have hJ_ne_top : J ≠ ⊤ := by
    intro hJ_top
    obtain ⟨n, hnJ⟩ := exists_pow_smul_eq_bot_maximalIdealPowTorsionIdeal (R := R)
    have hnil : IsNilpotent (maximalIdeal R) := by
      refine ⟨n, ?_⟩
      simpa [J, hJ_top] using hnJ
    exact hnotArtinian ((isArtinianRing_iff_isNilpotent_maximalIdeal R).2 hnil)
  letI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ_ne_top
  letI : Module.Finite R (R ⧸ J) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R J).toLinearMap Ideal.Quotient.mk_surjective
  have hnotbij : ¬ Function.Bijective (algebraMap R (R ⧸ J)) := by
    intro hbij
    have hker_bot : RingHom.ker (algebraMap R (R ⧸ J)) = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot (algebraMap R (R ⧸ J))).1 hbij.1
    exact hJnonzero <| by
      simpa [J, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker] using hker_bot
  obtain ⟨n, hnker⟩ := exists_pow_smul_eq_bot_maximalIdealPowTorsionIdeal (R := R)
  have hrange_top : (Algebra.linearMap R (R ⧸ J)).range = ⊤ := by
    apply LinearMap.range_eq_top.2
    simpa [Ideal.Quotient.algebraMap_eq] using
      (Ideal.Quotient.mk_surjective : Function.Surjective (Ideal.Quotient.mk J))
  have hcoker :
      (maximalIdeal R) ^ n • (⊤ : Submodule R (R ⧸ J)) ≤ (Algebra.linearMap R (R ⧸ J)).range := by
    simpa [hrange_top] using (le_top : (maximalIdeal R) ^ n • (⊤ : Submodule R (R ⧸ J)) ≤ ⊤)
  have hassoc : maximalIdeal R ∉ associatedPrimes R (R ⧸ J) := by
    simpa [J] using
      maximalIdeal_not_mem_associatedPrimes_quotient_maximalIdealPowTorsionIdeal (R := R)
  -- Package the source's quotient witness `R → R / J` directly into Kollár's fourth case.
  exact (hasKollarExceptionalFiniteExtension_iff (R := R)).2
    ⟨R ⧸ J, inferInstance, inferInstance, inferInstance, inferInstance, hnotbij,
      ⟨n, by simpa [J, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker] using hnker, hcoker⟩, hassoc⟩

/-- Helper for Lemma 10.119.2 (Kollár): an associated-prime witness for `R/xR`, expressed as
`QuotSMulTop x R`, lifts to an element `y : R` that is nonzero modulo `(x)` and whose product with
every element of the maximal ideal lies in `(x)`. -/
lemma exists_lift_outside_span_singleton_of_associated_quotSMulTop {x : R}
    (hassoc : maximalIdeal R ∈ associatedPrimes R (QuotSMulTop x R)) :
    ∃ y : R, y ∉ Ideal.span ({x} : Set R) ∧
      ∀ t ∈ maximalIdeal R, y * t ∈ Ideal.span ({x} : Set R) := by
  let e : QuotSMulTop x R ≃ₗ[R] R ⧸ Ideal.span ({x} : Set R) :=
    Submodule.quotEquivOfEq (x • (⊤ : Submodule R R)) (Ideal.span ({x} : Set R))
      (by simpa using (Submodule.ideal_span_singleton_smul x (⊤ : Submodule R R)).symm)
  have hassoc' : maximalIdeal R ∈ associatedPrimesOfModule R (QuotSMulTop x R) := by
    simpa [associatedPrimesOfModule_eq_associatedPrimes (R := R) (M := QuotSMulTop x R)] using
      hassoc
  have hassoc_quot :
      maximalIdeal R ∈ associatedPrimesOfModule R (R ⧸ Ideal.span ({x} : Set R)) := by
    rw [← LinearEquiv.associatedPrimesOfModule_eq (R := R) (M := QuotSMulTop x R)
      (M' := R ⧸ Ideal.span ({x} : Set R)) e]
    exact hassoc'
  rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf] at hassoc_quot
  rcases hassoc_quot with ⟨hmax, z, hz⟩
  have hz_ne : z ≠ 0 := by
    intro hz_zero
    have htop : Ideal.torsionOf R (R ⧸ Ideal.span ({x} : Set R)) z = ⊤ := by
      simpa [hz_zero] using (Ideal.torsionOf_eq_top_iff (R := R) z).2 hz_zero
    exact hmax.ne_top (hz.trans htop)
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨y, ?_, ?_⟩
  · -- The quotient class must stay nonzero, so the chosen lift does not lie in `(x)`.
    intro hy
    exact hz_ne ((Ideal.Quotient.eq_zero_iff_mem).2 hy)
  · -- Membership in the annihilator ideal says exactly that every `t ∈ 𝔪` kills the quotient
    -- class of `y`, which rewrites to `y * t ∈ (x)`.
    intro t ht
    have ht_torsion :
        t ∈ Ideal.torsionOf R (R ⧸ Ideal.span ({x} : Set R))
          (Ideal.Quotient.mk (Ideal.span ({x} : Set R)) y) := by
      simpa [hz] using ht
    rw [Ideal.mem_torsionOf_iff] at ht_torsion
    change Ideal.Quotient.mk (Ideal.span ({x} : Set R)) (t * y) = 0 at ht_torsion
    simpa [mul_comm] using (Ideal.Quotient.eq_zero_iff_mem).1 ht_torsion

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.119.2 (Kollár): from the source relation `y * 𝔪 ⊆ (x)`, either every
coefficient already lands back in `𝔪`, or one coefficient is a unit and yields the principal
branch. -/
lemma mul_maximalIdeal_into_span_singleton_dichotomy {x y : R}
    (hy_mul : ∀ t ∈ maximalIdeal R, y * t ∈ Ideal.span ({x} : Set R)) :
    (∀ t ∈ maximalIdeal R, ∃ s ∈ maximalIdeal R, y * t = x * s) ∨
      (∃ t ∈ maximalIdeal R, ∃ u : Units R, y * t = (u : R) * x) := by
  classical
  by_cases hcoeff : ∀ t ∈ maximalIdeal R, ∃ s ∈ maximalIdeal R, y * t = x * s
  · -- In the first source branch all coefficients stay inside `𝔪`.
    exact Or.inl hcoeff
  · -- Otherwise fix a counterexample `t`; its coefficient cannot lie in `𝔪`, hence is a unit.
    push Not at hcoeff
    rcases hcoeff with ⟨t, ht, hsbad⟩
    rcases Ideal.mem_span_singleton'.1 (hy_mul t ht) with ⟨s, hsx⟩
    have hyt : y * t = x * s := by
      simpa [mul_comm] using hsx.symm
    have hs_unit : IsUnit s := by
      by_contra hs_nonunit
      have hs_mem : s ∈ maximalIdeal R := by
        simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hs_nonunit
      exact hsbad s hs_mem hyt
    rcases hs_unit with ⟨u, rfl⟩
    exact Or.inr ⟨t, ht, u, by simpa [mul_comm] using hyt⟩

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.119.2 (Kollár): in the unit-coefficient branch of the source proof, the
maximal ideal is generated by the normalized witness `t`. -/
lemma maximalIdeal_isPrincipal_of_unit_multiple_branch {x y : R}
    (_hx : x ∈ maximalIdeal R) (hxreg : IsSMulRegular R x)
    (_hy : y ∉ Ideal.span ({x} : Set R))
    (hy_mul : ∀ t ∈ maximalIdeal R, y * t ∈ Ideal.span ({x} : Set R))
    (hunit : ∃ t ∈ maximalIdeal R, ∃ u : Units R, y * t = (u : R) * x) :
    (maximalIdeal R).IsPrincipal := by
  rcases hunit with ⟨t, ht, u, hu⟩
  let t' : R := ↑u⁻¹ * t
  have ht' : t' ∈ maximalIdeal R := by
    -- Normalizing by a unit keeps the witness inside the maximal ideal.
    simpa [t'] using Ideal.mul_mem_left (maximalIdeal R) ↑u⁻¹ ht
  have hnorm : y * t' = x := by
    -- Route correction: absorb the unit into `t` first, so the later cancellation arguments use
    -- the normalized source identity `y * t' = x`.
    calc
      y * t' = ↑u⁻¹ * (y * t) := by
        simp [t', mul_assoc, mul_comm]
      _ = ↑u⁻¹ * ((u : R) * x) := by rw [hu]
      _ = x := by simp
  have hyreg : IsSMulRegular R y := by
    -- Once `y * t' = x`, any zero-divisor relation for `y` would also annihilate the regular
    -- element `x`.
    refine IsSMulRegular.of_right_eq_zero_of_smul ?_
    intro a ha
    have hya : y * a = 0 := by
      simpa [smul_eq_mul] using ha
    have hx_zero : x * a = 0 := by
      calc
        x * a = (y * t') * a := by rw [hnorm]
        _ = t' * (y * a) := by ring
        _ = 0 := by simp [hya]
    exact hxreg.right_eq_zero_of_smul hx_zero
  refine ⟨t', le_antisymm ?_ ?_⟩
  · -- Every `t₀ ∈ 𝔪` is a multiple of `t'` by rewriting `y * t₀` through `x = y * t'` and then
    -- canceling the regular element `y`.
    intro t₀ ht₀
    rcases Ideal.mem_span_singleton'.1 (hy_mul t₀ ht₀) with ⟨s, hsx⟩
    have hyt₀ : y * t₀ = x * s := by
      simpa [mul_comm] using hsx.symm
    have hy_zero : y * (t₀ - s * t') = 0 := by
      calc
        y * (t₀ - s * t') = y * t₀ - y * (s * t') := by ring
        _ = x * s - y * (s * t') := by rw [hyt₀]
        _ = x * s - (y * t') * s := by ring
        _ = x * s - x * s := by rw [hnorm]
        _ = 0 := by simp
    have ht₀_eq : t₀ = s * t' := by
      exact sub_eq_zero.mp (hyreg.right_eq_zero_of_smul (by simpa [smul_eq_mul] using hy_zero))
    exact Ideal.mem_span_singleton'.2 ⟨s, ht₀_eq.symm⟩
  · -- The normalized witness itself lies in `𝔪`, so the principal ideal it generates is
    -- contained in the maximal ideal.
    refine Ideal.span_le.2 ?_
    intro z hz
    rcases Set.mem_singleton_iff.1 hz with rfl
    exact ht'

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Lemma 10.119.2 (Kollár): if `y / x` in the localization away from a regular
element `x` came from `R`, then `y` would already lie in the principal ideal `(x)`. -/
lemma localized_ratio_not_mem_range_of_not_mem_span_singleton {x y : R}
    (hxreg : IsSMulRegular R x) (hy : y ∉ Ideal.span ({x} : Set R)) :
    let z : Localization.Away x :=
      algebraMap R (Localization.Away x) y * IsLocalization.Away.invSelf x
    z ∉ Set.range (algebraMap R (Localization.Away x)) := by
  dsimp
  rintro ⟨r, hr⟩
  have hinj : Function.Injective (algebraMap R (Localization.Away x)) := by
    -- Regularity of `x` propagates to every denominator in the localization away from `x`.
    rw [IsLocalization.injective_iff_isRegular (M := Submonoid.powers x) (S := Localization.Away x)]
    intro c
    rcases c with ⟨c, ⟨n, rfl⟩⟩
    have hx_regular : IsRegular x :=
      (Commute.isRegular_iff (a := x) (fun b ↦ mul_comm x b)).mpr hxreg.isLeftRegular
    simpa using hx_regular.pow n
  have hr' : algebraMap R (Localization.Away x) (r * x) =
      algebraMap R (Localization.Away x) y := by
    -- Multiplying the identity `y / x = r` by `x` clears the denominator inside the localization.
    calc
      algebraMap R (Localization.Away x) (r * x) =
          algebraMap R (Localization.Away x) r * algebraMap R (Localization.Away x) x := by
            simp [map_mul]
      _ = (algebraMap R (Localization.Away x) y * IsLocalization.Away.invSelf x) *
            algebraMap R (Localization.Away x) x := by
            rw [hr]
      _ = algebraMap R (Localization.Away x) y *
            (IsLocalization.Away.invSelf x * algebraMap R (Localization.Away x) x) := by
            rw [mul_assoc]
      _ = algebraMap R (Localization.Away x) y * 1 := by
            rw [mul_comm (IsLocalization.Away.invSelf x), IsLocalization.Away.mul_invSelf]
      _ = algebraMap R (Localization.Away x) y := by
            simp
  have hyr : r * x = y := hinj hr'
  -- Therefore `y` lies in `(x)`, contradicting the chosen lift.
  exact hy <| Ideal.mem_span_singleton'.2 ⟨r, hyr⟩

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.119.2 (Kollár): if `y * 𝔪 ⊆ x𝔪`, then for the localized ratio
`z = y / x` every product `t * z` with `t ∈ 𝔪` already comes from an element of `𝔪`. -/
lemma localized_ratio_mul_eq_of_mul_maximalIdeal_into_mul_maximalIdeal {x y : R}
    (hdet : ∀ t ∈ maximalIdeal R, ∃ s ∈ maximalIdeal R, y * t = x * s) :
    let z : Localization.Away x :=
      algebraMap R (Localization.Away x) y * IsLocalization.Away.invSelf x
    ∀ t ∈ maximalIdeal R, ∃ s ∈ maximalIdeal R,
      algebraMap R (Localization.Away x) t * z = algebraMap R (Localization.Away x) s := by
  intro z t ht
  rcases hdet t ht with ⟨s, hs, hys⟩
  refine ⟨s, hs, ?_⟩
  -- Clear the denominator in `z = y / x` using the source relation `y * t = x * s`.
  dsimp [z]
  calc
    algebraMap R (Localization.Away x) t *
        (algebraMap R (Localization.Away x) y * IsLocalization.Away.invSelf x) =
      algebraMap R (Localization.Away x) (y * t) * IsLocalization.Away.invSelf x := by
        simp [map_mul, mul_left_comm, mul_comm]
    _ = algebraMap R (Localization.Away x) (x * s) * IsLocalization.Away.invSelf x := by
        rw [hys]
    _ = algebraMap R (Localization.Away x) s *
        (algebraMap R (Localization.Away x) x * IsLocalization.Away.invSelf x) := by
        simp [map_mul, mul_left_comm, mul_comm]
    _ = algebraMap R (Localization.Away x) s := by
        rw [IsLocalization.Away.mul_invSelf]
        simp

/-- Helper for Lemma 10.119.2 (Kollár): the determinantal relation `y * 𝔪 ⊆ x𝔪` yields a
finitely generated `R`-submodule of `R[1/x]` that contains `1` and is stable under multiplication
by the localized ratio `y / x`. -/
lemma exists_fg_submodule_of_one_mem_of_mul_mem_localized_ratio {x y : R}
    (hx : x ∈ maximalIdeal R)
    (hdet : ∀ t ∈ maximalIdeal R, ∃ s ∈ maximalIdeal R, y * t = x * s) :
    let z : Localization.Away x :=
      algebraMap R (Localization.Away x) y * IsLocalization.Away.invSelf x
    ∃ M : Submodule R (Localization.Away x),
      M.FG ∧ (1 : Localization.Away x) ∈ M ∧ ∀ m ∈ M, z * m ∈ M := by
  intro z
  let invx : Localization.Away x := IsLocalization.Away.invSelf x
  let ψ : maximalIdeal R →ₗ[R] Localization.Away x :=
    (Algebra.lsmul R R (Localization.Away x) invx).comp
      ((Algebra.linearMap R (Localization.Away x)).comp (maximalIdeal R).subtype)
  let M : Submodule R (Localization.Away x) := LinearMap.range ψ
  refine ⟨M, ?_, ?_, ?_⟩
  · letI : Module.Finite R (maximalIdeal R) :=
      Module.Finite.of_injective (maximalIdeal R).subtype (maximalIdeal R).injective_subtype
    -- The source module `𝔪` is finite over the Noetherian ring, so its image remains finite.
    have hfg : (Submodule.map ψ (⊤ : Submodule R (maximalIdeal R))).FG :=
      Submodule.FG.map ψ Module.Finite.fg_top
    have hrange : M = Submodule.map ψ (⊤ : Submodule R (maximalIdeal R)) := by
      simpa [M] using (LinearMap.range_eq_map ψ)
    rw [hrange]
    exact hfg
  · -- The element `x / x = 1` lies in the image of the generating map.
    refine ⟨⟨x, hx⟩, ?_⟩
    calc
      ψ ⟨x, hx⟩
          = invx *
              algebraMap R (Localization.Away x) x := by
                simp [ψ, mul_comm]
      _ = 1 := by
            change IsLocalization.Away.invSelf x * algebraMap R (Localization.Away x) x = 1
            rw [mul_comm, IsLocalization.Away.mul_invSelf]
  · intro m hm
    rcases hm with ⟨t, rfl⟩
    rcases
      (localized_ratio_mul_eq_of_mul_maximalIdeal_into_mul_maximalIdeal
        (R := R) (x := x) (y := y) hdet) t t.2 with
      ⟨s, hs, hsz⟩
    refine ⟨⟨s, hs⟩, ?_⟩
    -- Rewrite `z * (t / x)` as `(t * z) / x` and then use the determinantal relation.
    calc
      ψ ⟨s, hs⟩
          = algebraMap R (Localization.Away x) s * invx := by
              simp [ψ, mul_comm]
      _ = (algebraMap R (Localization.Away x) t * z) * invx := by
            rw [hsz]
      _ = z * ψ t := by
            simp [ψ, mul_assoc, mul_comm]

/-- Helper for Lemma 10.119.2 (Kollár): the determinantal relation `y * 𝔪 ⊆ x𝔪` makes the
localized ratio `y / x` integral over `R`. -/
lemma localized_ratio_isIntegral_of_mul_maximalIdeal_into_mul_maximalIdeal {x y : R}
    (hx : x ∈ maximalIdeal R) (_hxreg : IsSMulRegular R x)
    (hdet : ∀ t ∈ maximalIdeal R, ∃ s ∈ maximalIdeal R, y * t = x * s) :
    let z : Localization.Away x :=
      algebraMap R (Localization.Away x) y * IsLocalization.Away.invSelf x
    IsIntegral R z := by
  intro z
  -- Route correction: use the owner theorem from Lemma 10.36.2 on the finite stable submodule of
  -- fractions `t / x`, instead of transporting Cayley-Hamilton through localization.
  exact isIntegral_of_exists_fg_submodule_of_one_mem_of_mul_mem <|
    exists_fg_submodule_of_one_mem_of_mul_mem_localized_ratio
      (R := R) (x := x) (y := y) hx hdet

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Lemma 10.119.2 (Kollár): the image of a regular element stays regular on any
subalgebra of the localization away from that element. -/
lemma isSMulRegular_subalgebra_localizationAway {x : R}
    (_hxreg : IsSMulRegular R x) (S : Subalgebra R (Localization.Away x)) :
    IsSMulRegular S x := by
  have hloc : IsSMulRegular (Localization.Away x) x := by
    -- In the localization away from `x`, multiplication by `x` has inverse `1 / x`.
    refine IsSMulRegular.of_right_eq_zero_of_smul ?_
    intro a ha
    have ha' : algebraMap R (Localization.Away x) x * a = 0 := by
      simpa [Algebra.smul_def] using ha
    have hinv : IsLocalization.Away.invSelf x * algebraMap R (Localization.Away x) x = 1 := by
      simpa [mul_comm] using (IsLocalization.Away.mul_invSelf (S := Localization.Away x) x)
    calc
      a = 1 * a := by simp
      _ = (IsLocalization.Away.invSelf x * algebraMap R (Localization.Away x) x) * a := by
            rw [hinv]
      _ = IsLocalization.Away.invSelf x *
            (algebraMap R (Localization.Away x) x * a) := by
              ring
      _ = 0 := by simp [ha']
  -- Restrict the ambient regularity statement along the subalgebra inclusion.
  change IsSMulRegular (S.toSubmodule) x
  simpa using IsSMulRegular.submodule S.toSubmodule x hloc

/-- Helper for Lemma 10.119.2 (Kollár): a regular maximal-ideal element excludes the maximal ideal
from the associated primes of a finite module. -/
lemma maximalIdeal_not_mem_associatedPrimes_of_mem_maximalIdeal_of_isSMulRegular
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {x : R} (hx : x ∈ maximalIdeal R) (hxreg : IsSMulRegular M x) :
    maximalIdeal R ∉ associatedPrimes R M := by
  intro hp
  -- Regularity says `x` avoids the union of all associated primes, hence also `𝔪`.
  have hx_not_mem_union : x ∉ ⋃ q ∈ associatedPrimes R M, (q : Set R) := by
    simpa [Set.mem_compl_iff, biUnion_associatedPrimes_eq_compl_regular R M] using hxreg
  exact hx_not_mem_union <|
    Set.mem_iUnion.2 ⟨maximalIdeal R, Set.mem_iUnion.2 ⟨hp, hx⟩⟩

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.119.2 (Kollár): after adjoining the localized ratio `y / x`, multiplication
by the maximal ideal sends every element of `R[y / x]` back into the image of `R`, and even into
the image of the maximal ideal. -/
lemma adjoin_localized_ratio_mul_mem_maximalIdeal_image {x y : R}
    (hdet : ∀ t ∈ maximalIdeal R, ∃ s ∈ maximalIdeal R, y * t = x * s) :
    let z : Localization.Away x :=
      algebraMap R (Localization.Away x) y * IsLocalization.Away.invSelf x
    let S : Subalgebra R (Localization.Away x) := Algebra.adjoin R ({z} : Set (Localization.Away x))
    ∀ w : S, ∀ t ∈ maximalIdeal R, ∃ s ∈ maximalIdeal R,
      algebraMap R S t * w = algebraMap R S s := by
  intro z S w t ht
  let Q : Localization.Away x → Prop := fun a =>
    ∀ u ∈ maximalIdeal R, ∃ s ∈ maximalIdeal R,
      algebraMap R (Localization.Away x) u * a = algebraMap R (Localization.Away x) s
  have hQ : ∀ ⦃a : Localization.Away x⦄, a ∈ S → Q a := by
    intro a ha
    -- Extend the source generator relation from `z` to the whole simple adjoin `R[z]`.
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ ha
    · intro a ha_mem
      rcases Set.mem_singleton_iff.1 ha_mem with rfl
      simpa [Q] using
        (localized_ratio_mul_eq_of_mul_maximalIdeal_into_mul_maximalIdeal
          (R := R) (x := x) (y := y) hdet)
    · intro r u hu
      refine ⟨u * r, Ideal.mul_mem_right r _ hu, ?_⟩
      simp [map_mul, mul_comm]
    · intro a b ha hb hQa hQb u hu
      rcases hQa u hu with ⟨sa, hsa, hsa_eq⟩
      rcases hQb u hu with ⟨sb, hsb, hsb_eq⟩
      refine ⟨sa + sb, Ideal.add_mem _ hsa hsb, ?_⟩
      calc
        algebraMap R (Localization.Away x) u * (a + b) =
          algebraMap R (Localization.Away x) u * a +
            algebraMap R (Localization.Away x) u * b := by
              ring
        _ = algebraMap R (Localization.Away x) sa +
            algebraMap R (Localization.Away x) sb := by
              rw [hsa_eq, hsb_eq]
        _ = algebraMap R (Localization.Away x) (sa + sb) := by
              simp
    · intro a b ha hb hQa hQb u hu
      rcases hQa u hu with ⟨sa, hsa, hsa_eq⟩
      rcases hQb sa hsa with ⟨sb, hsb, hsb_eq⟩
      refine ⟨sb, hsb, ?_⟩
      calc
        algebraMap R (Localization.Away x) u * (a * b) =
          (algebraMap R (Localization.Away x) u * a) * b := by
            ring
        _ = algebraMap R (Localization.Away x) sa * b := by rw [hsa_eq]
        _ = algebraMap R (Localization.Away x) sb := hsb_eq
  rcases hQ (a := w.1) w.2 t ht with ⟨s, hs, hs_eq⟩
  refine ⟨s, hs, ?_⟩
  -- Move the ambient equality back to the adjoin subtype.
  apply Subtype.ext
  simpa using hs_eq

/-- Helper for Lemma 10.119.2 (Kollár): the determinantal branch `y * 𝔪 ⊆ x𝔪` produces
Kollár's exceptional finite extension by adjoining the localized ratio `y / x`. -/
lemma hasKollarExceptionalFiniteExtension_of_localized_ratio_determinantal_case {x y : R}
    (hx : x ∈ maximalIdeal R) (hxreg : IsSMulRegular R x)
    (hy : y ∉ Ideal.span ({x} : Set R))
    (hdet : ∀ t ∈ maximalIdeal R, ∃ s ∈ maximalIdeal R, y * t = x * s) :
    HasKollarExceptionalFiniteExtension R := by
  let z : Localization.Away x :=
    algebraMap R (Localization.Away x) y * IsLocalization.Away.invSelf x
  let S : Subalgebra R (Localization.Away x) := Algebra.adjoin R ({z} : Set (Localization.Away x))
  have hz_integral : IsIntegral R z := by
    -- First prove the source ratio `y / x` is integral by the finite-submodule determinantal trick.
    simpa [z] using
      localized_ratio_isIntegral_of_mul_maximalIdeal_into_mul_maximalIdeal
        (R := R) (x := x) (y := y) hx hxreg hdet
  have hfiniteS : Module.Finite R S := by
    -- Adjoining one integral element produces a finite `R`-algebra.
    dsimp [S]
    exact Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_singleton z) <| by
      intro w hw
      rcases Set.mem_singleton_iff.1 hw with rfl
      exact hz_integral
  let η : R →+* S := algebraMap R S
  have hz_mem_S : z ∈ S := by
    -- The adjoined ratio is, by construction, an element of `R[z]`.
    dsimp [S]
    exact Algebra.subset_adjoin (R := R) (a := z) (by simp)
  have hz_not_range :
      z ∉ Set.range (algebraMap R (Localization.Away x)) := by
    -- The source lift `y` was chosen outside `(x)`, so the ratio cannot already come from `R`.
    simpa [z] using
      localized_ratio_not_mem_range_of_not_mem_span_singleton
        (R := R) (x := x) (y := y) hxreg hy
  have hnot_surj : ¬ Function.Surjective η := by
    intro hsurj
    rcases hsurj ⟨z, hz_mem_S⟩ with ⟨r, hr⟩
    exact hz_not_range ⟨r, congrArg Subtype.val hr⟩
  have hS_not_subsingleton : ¬ Subsingleton S := by
    intro hsub
    letI : Subsingleton S := hsub
    exact hnot_surj fun s => ⟨0, Subsingleton.elim _ _⟩
  letI : Nontrivial S := not_subsingleton_iff_nontrivial.mp hS_not_subsingleton
  letI : Module.Finite R S := hfiniteS
  have hnotbij : ¬ Function.Bijective η := by
    intro hbij
    exact hnot_surj hbij.2
  have hloc_inj : Function.Injective (algebraMap R (Localization.Away x)) := by
    -- Regularity of `x` propagates to every denominator in the localization away from `x`.
    rw [IsLocalization.injective_iff_isRegular (M := Submonoid.powers x) (S := Localization.Away x)]
    intro c
    rcases c with ⟨c, ⟨n, rfl⟩⟩
    have hx_regular : IsRegular x :=
      (Commute.isRegular_iff (a := x) (fun b ↦ mul_comm x b)).mpr hxreg.isLeftRegular
    simpa using hx_regular.pow n
  have hηinj : Function.Injective η := by
    intro a b hab
    apply hloc_inj
    exact congrArg Subtype.val hab
  have hker :
      (maximalIdeal R) ^ 1 • (RingHom.ker η : Submodule R R) = ⊥ := by
    have hker_bot : RingHom.ker η = ⊥ := by
      exact (RingHom.injective_iff_ker_eq_bot η).1 hηinj
    simpa [pow_one, hker_bot]
  have hcoker :
      (maximalIdeal R) ^ 1 • (⊤ : Submodule R S) ≤ (Algebra.linearMap R S).range := by
    intro w hw
    rw [pow_one] at hw
    -- The source relation sends every generator `t * w` with `t ∈ 𝔪` back into the image of `R`,
    -- and then `Submodule.smul_induction_on` closes the whole `𝔪S` containment.
    refine Submodule.smul_induction_on hw ?_ ?_
    · intro t ht s hs
      rcases
        (adjoin_localized_ratio_mul_mem_maximalIdeal_image
          (R := R) (x := x) (y := y) hdet (w := s) t ht) with
        ⟨r, hr, hr_eq⟩
      exact ⟨r, by simpa [Algebra.smul_def] using hr_eq.symm⟩
    · intro a b ha hb
      exact Submodule.add_mem _ ha hb
  have hxregS : IsSMulRegular S x :=
    isSMulRegular_subalgebra_localizationAway (R := R) (x := x) hxreg S
  have hassoc : maximalIdeal R ∉ associatedPrimes R S := by
    intro hp
    exact
      maximalIdeal_not_mem_associatedPrimes_of_mem_maximalIdeal_of_isSMulRegular
        (R := R) (M := S) hx hxregS hp
  -- Package the adjoin `R[z]` as the exceptional finite extension from the source proof.
  exact (hasKollarExceptionalFiniteExtension_iff (R := R)).2
    ⟨S, inferInstance, inferInstance, hfiniteS, inferInstance, hnotbij, ⟨1, hker, hcoker⟩, hassoc⟩

/-- Helper for Lemma 10.119.2 (Kollár): outside the Artinian case, a principal maximal ideal
forces the ring to be regular local of dimension `1`. -/
lemma regular_dim_one_of_principal_maximalIdeal_and_not_artinian
    (hprincipal : (maximalIdeal R).IsPrincipal) (hnotArtinian : ¬ IsArtinianRing R) :
    IsRegularLocalRing R ∧ ringKrullDim R = 1 := by
  have hnontrivial : Nontrivial R := by
    -- The zero ring is Artinian, so the non-Artinian hypothesis rules it out immediately.
    by_contra hsub
    letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp hsub
    exact hnotArtinian inferInstance
  have hspan_le : (maximalIdeal R).spanFinrank ≤ 1 := by
    -- A principal maximal ideal is generated by one element, hence has span finrank at most `1`.
    obtain ⟨x, hx⟩ := Submodule.IsPrincipal.principal (maximalIdeal R)
    rw [hx]
    calc
      (Ideal.span ({x} : Set R)).spanFinrank ≤ ({x} : Set R).ncard := by
        exact Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite {x})
      _ = 1 := by
        simp
  have hdim_le : ringKrullDim R ≤ 1 := by
    -- Krull's height theorem bounds the local dimension by the number of generators of `𝔪`.
    exact le_trans (ringKrullDim_le_spanFinrank_maximalIdeal (R := R)) (by exact_mod_cast hspan_le)
  obtain ⟨n, hn_le, hdim⟩ := ringKrullDim_eq_nat_of_le (R := R) hdim_le
  have hn_ne_zero : n ≠ 0 := by
    -- Dimension `0` would make the Noetherian local ring Artinian, contrary to hypothesis.
    intro hn_zero
    have hdim_zero : ringKrullDim R = 0 := by
      simpa [hn_zero] using hdim
    have hdim_le_zero : Ring.KrullDimLE 0 R :=
      ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hdim_zero
    exact hnotArtinian <|
      (isArtinianRing_iff_isNoetherianRing_krullDimLE_zero).2 ⟨inferInstance, hdim_le_zero⟩
  have hn_one : n = 1 := by
    omega
  have hregular : IsRegularLocalRing R := by
    -- With `dim R = 1`, the one-generator bound is exactly the regular-local criterion.
    refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le (R := R) ?_
    calc
      ↑(maximalIdeal R).spanFinrank ≤ (1 : WithBot ℕ∞) := by
        exact_mod_cast hspan_le
      _ = ringKrullDim R := by
        simpa [hn_one] using hdim.symm
  exact ⟨hregular, by simpa [hn_one] using hdim⟩

/-- Helper for Lemma 10.119.2 (Kollár): a nontrivial finite module annihilated by a power of the
maximal ideal has depth `0`. -/
lemma moduleDepth_eq_zero_of_pow_maximalIdeal_smul_top_eq_bot
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    {n : ℕ} (hn : (maximalIdeal R) ^ n • (⊤ : Submodule R M) = ⊥) :
    moduleDepth R M = 0 := by
  by_contra hdepth
  -- Positive depth gives a regular element in `𝔪`, exactly as in the source proof.
  obtain ⟨x, hx, hxreg⟩ :=
    exists_mem_maximalIdeal_isSMulRegular_of_moduleDepth_ne_zero (R := R) (M := M) hdepth
  have hpowreg : IsSMulRegular M (x ^ n) := hxreg.pow n
  have hpow_eq_zero : ((x ^ n) • · : M → M) = ((0 : R) • ·) := by
    funext m
    -- Since `x^n ∈ 𝔪^n`, the `𝔪^n`-torsion hypothesis forces `x^n • m = 0`.
    have hmem : x ^ n • m ∈ (maximalIdeal R) ^ n • (⊤ : Submodule R M) := by
      exact Submodule.smul_mem_smul (Ideal.pow_mem_pow hx n) (by simp)
    simpa [hn] using hmem
  have hzero_reg : IsSMulRegular M (0 : R) := by
    simpa [IsSMulRegular, hpow_eq_zero] using hpowreg
  exact (IsSMulRegular.not_zero (M := M)) hzero_reg

/-- Helper for Lemma 10.119.2 (Kollár): a submodule of `R` killed by a power of the maximal ideal
cannot have positive depth unless it is zero. -/
lemma submodule_eq_bot_of_pow_maximalIdeal_smul_eq_bot_of_moduleDepth_ne_zero
    (N : Submodule R R) {n : ℕ} (hn : (maximalIdeal R) ^ n • N = ⊥)
    (hdepth : moduleDepth R N ≠ 0) :
    N = ⊥ := by
  by_contra hN
  letI : Nontrivial N := Submodule.nontrivial_iff_ne_bot.mpr hN
  have hdepth_zero : moduleDepth R N = 0 := by
    -- Rewrite the ambient annihilation statement onto the top submodule of `N`.
    have hn' : (maximalIdeal R) ^ n • (⊤ : Submodule R N) = ⊥ := by
      apply le_antisymm ?_ bot_le
      intro x hx
      have hx' : (x : R) ∈ (maximalIdeal R) ^ n • N :=
        (Submodule.mem_smul_top_iff (I := (maximalIdeal R) ^ n) (N := N) (x := x)).1 hx
      have hx0' : (x : R) = 0 := by
        have hx0 : (x : R) ∈ (⊥ : Submodule R R) := by
          rw [← hn]
          exact hx'
        simpa [Submodule.mem_bot] using hx0
      exact Subtype.ext hx0'
    exact moduleDepth_eq_zero_of_pow_maximalIdeal_smul_top_eq_bot (R := R) (M := N) hn'
  exact hdepth hdepth_zero

/-- Helper for Lemma 10.119.2 (Kollár): a finite module killed by a power of the maximal ideal is
trivial as soon as its depth is nonzero. -/
lemma subsingleton_of_pow_maximalIdeal_smul_top_eq_bot_of_moduleDepth_ne_zero
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {n : ℕ} (hn : (maximalIdeal R) ^ n • (⊤ : Submodule R M) = ⊥)
    (hdepth : moduleDepth R M ≠ 0) :
    Subsingleton M := by
  by_contra hM
  letI : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM
  exact hdepth (moduleDepth_eq_zero_of_pow_maximalIdeal_smul_top_eq_bot
    (R := R) (M := M) hn)

/-- Helper for Lemma 10.119.2 (Kollár): if the maximal ideal is an associated prime of a finite
module over the local ring, then the module has depth `0`. -/
lemma moduleDepth_eq_zero_of_maximalIdeal_mem_associatedPrimes_of_finite
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (hassoc : maximalIdeal R ∈ associatedPrimes R M) :
    moduleDepth R M = 0 := by
  -- Translate the associated-prime witness into an element annihilated by `𝔪`.
  rw [moduleDepth_eq_zero_iff_no_maximalIdeal_regular (R := R) (M := M)]
  intro hregular
  have hassoc' : maximalIdeal R ∈ associatedPrimesOfModule R M := by
    simpa [associatedPrimesOfModule_eq_associatedPrimes (R := R) (M := M)] using hassoc
  rw [mem_associatedPrimesOfModule_iff, Ideal.isAssociatedToModule_iff_exists_torsionOf] at hassoc'
  rcases hassoc' with ⟨hmaxPrime, m, hm⟩
  have hm_ne : m ≠ 0 := by
    intro hm_zero
    have htop : Ideal.torsionOf R M m = ⊤ := by
      simpa [hm_zero] using (Ideal.torsionOf_eq_top_iff (R := R) m).2 hm_zero
    exact hmaxPrime.ne_top (hm.trans htop)
  rcases hregular with ⟨x, hx, hxreg⟩
  have hx_torsion : x ∈ Ideal.torsionOf R M m := by
    simpa [hm] using hx
  rw [Ideal.mem_torsionOf_iff] at hx_torsion
  exact hm_ne (hxreg.right_eq_zero_of_smul hx_torsion)

/-- Helper for Lemma 10.119.2 (Kollár): positive depth excludes the maximal ideal from the
associated primes of a finite module. -/
lemma maximalIdeal_not_mem_associatedPrimes_of_moduleDepth_ne_zero
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (hdepth : moduleDepth R M ≠ 0) :
    maximalIdeal R ∉ associatedPrimes R M := by
  -- The previous lemma converts an associated-prime occurrence of `𝔪` back into depth `0`.
  intro hassoc
  exact hdepth
    (moduleDepth_eq_zero_of_maximalIdeal_mem_associatedPrimes_of_finite
      (R := R) (M := M) hassoc)

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Lemma 10.119.2 (Kollár): a linear equivalence preserves the regular-sequence
lengths cut out by a fixed ideal. -/
private theorem regularSequenceLengths_eq_of_linearEquiv {M N : Type u} [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (I : Ideal R) (e : M ≃ₗ[R] N) :
    Ideal.regularSequenceLengths I M = Ideal.regularSequenceLengths I N := by
  -- Transport each regular sequence across the equivalence and then reverse the argument.
  ext d
  constructor
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).1 hreg, hI, rfl⟩
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).2 hreg, hI, rfl⟩

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Lemma 10.119.2 (Kollár): finite modules related by a linear equivalence have the
same ideal depth. -/
private theorem idealDepth_eq_of_linearEquiv {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Finite R N] (I : Ideal R)
    (e : M ≃ₗ[R] N) :
    Ideal.depth I M = Ideal.depth I N := by
  -- Compare the `IM = M` branch on both sides, and otherwise use the same regular-sequence data.
  have htop : I • (⊤ : Submodule R M) = ⊤ ↔ I • (⊤ : Submodule R N) = ⊤ := by
    constructor
    · intro h
      have hmap := congrArg (Submodule.map e.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.surjective] using hmap
    · intro h
      have hmap := congrArg (Submodule.map e.symm.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.symm.surjective] using hmap
  by_cases hM : I • (⊤ : Submodule R M) = ⊤
  · rw [Ideal.depth_eq_top_of_smul_top I M hM, Ideal.depth_eq_top_of_smul_top I N (htop.mp hM)]
  · rw [Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top I M hM,
      Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top I N (mt htop.mpr hM),
      regularSequenceLengths_eq_of_linearEquiv (R := R) (M := M) (N := N) I e]

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.119.2 (Kollár): linear equivalences preserve module depth over the local
base ring. -/
private theorem moduleDepth_eq_of_linearEquiv {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Finite R N]
    (e : M ≃ₗ[R] N) :
    moduleDepth R M = moduleDepth R N := by
  -- Specialize ideal-depth invariance to the maximal ideal.
  simpa [moduleDepth] using
    idealDepth_eq_of_linearEquiv (R := R) (M := M) (N := N) (maximalIdeal R) e

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Lemma 10.119.2 (Kollár): the canonical row `0 → N → M → M / N → 0` as a short
complex of `R`-modules. -/
private abbrev submodule_quotient_shortComplex {M : Type u} [AddCommGroup M] [Module R M]
    (N : Submodule R M) :
    CategoryTheory.ShortComplex (ModuleCat R) :=
  CategoryTheory.ShortComplex.moduleCatMk N.subtype N.mkQ
    (LinearMap.exact_subtype_mkQ N).linearMap_comp_eq_zero

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Lemma 10.119.2 (Kollár): the canonical quotient row is short exact. -/
private theorem submodule_quotient_shortExact {M : Type u} [AddCommGroup M] [Module R M]
    (N : Submodule R M) :
    (submodule_quotient_shortComplex (R := R) N).ShortExact := by
  -- Exactness is the standard kernel-range computation for `N ↪ M → M / N`.
  refine CategoryTheory.ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    simpa [submodule_quotient_shortComplex] using LinearMap.exact_subtype_mkQ N
  · exact (ModuleCat.mono_iff_injective _).2 N.subtype_injective
  · exact (ModuleCat.epi_iff_surjective _).2 N.mkQ_surjective

namespace Submodule

/-- Helper for Lemma 10.119.2 (Kollár): the quotient row `0 → N → M → M / N → 0` gives the
standard lower bound on the depth of `M / N`. -/
lemma moduleDepth_quotient_ge_min_of_submodule_row {M : Type u} [AddCommGroup M] [Module R M]
    [Module.Finite R M] (N : Submodule R M) :
    moduleDepth R (M ⧸ N) ≥ min (moduleDepth R M) (moduleDepth R N - 1) := by
  letI : Module.Finite R N :=
    Module.Finite.of_injective N.subtype N.injective_subtype
  letI : Module.Finite R (M ⧸ N) :=
    Module.Finite.of_surjective N.mkQ N.mkQ_surjective
  letI : Module.Finite R ((submodule_quotient_shortComplex (R := R) N).X₁) := by
    change Module.Finite R N
    infer_instance
  letI : Module.Finite R ((submodule_quotient_shortComplex (R := R) N).X₃) := by
    change Module.Finite R (M ⧸ N)
    infer_instance
  -- Apply the chapter's short-exact depth inequality to the canonical quotient row.
  simpa [submodule_quotient_shortComplex] using
    CategoryTheory.ShortComplex.ShortExact.moduleDepth_right_ge_min
      (R := R) (S := submodule_quotient_shortComplex (R := R) N)
      (submodule_quotient_shortExact (R := R) N)

end Submodule

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.119.2 (Kollár): if a power of the maximal ideal sends `N` into the range
of `f`, then the same power kills the quotient `N / range(f)`. -/
lemma pow_smul_top_eq_bot_of_pow_smul_top_le_range_mkQ
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {f : M →ₗ[R] N} {n : ℕ}
    (h : (maximalIdeal R) ^ n • (⊤ : Submodule R N) ≤ LinearMap.range f) :
    (maximalIdeal R) ^ n • (⊤ : Submodule R (N ⧸ LinearMap.range f)) = ⊥ := by
  apply le_antisymm ?_ bot_le
  -- Map the containment through `mkQ`; the image of the range is zero in the quotient.
  have hmap :
      Submodule.map (Submodule.mkQ (LinearMap.range f))
          ((maximalIdeal R) ^ n • (⊤ : Submodule R N)) ≤
        (⊥ : Submodule R (N ⧸ LinearMap.range f)) := by
    calc
      Submodule.map (Submodule.mkQ (LinearMap.range f))
          ((maximalIdeal R) ^ n • (⊤ : Submodule R N)) ≤
          Submodule.map (Submodule.mkQ (LinearMap.range f)) (LinearMap.range f) :=
        Submodule.map_mono h
      _ = ⊥ := by
        simpa using (Submodule.mkQ_map_self (p := LinearMap.range f))
  simpa [Submodule.map_smul''] using hmap

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Lemma 10.119.2 (Kollár): localizing a linear map is injective exactly when the
localized kernel module is trivial. -/
private lemma localized_map_injective_iff_subsingleton_kernel
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N) (S : Submonoid R) :
    Function.Injective (LocalizedModule.map S φ) ↔
      Subsingleton (LocalizedModule S (LinearMap.ker φ)) := by
  let κ : LinearMap.ker φ →ₗ[R] LinearMap.ker (LocalizedModule.map S φ) :=
    LinearMap.toKerIsLocalized
      (p := S)
      (f := LocalizedModule.mkLinearMap S M)
      (f' := LocalizedModule.mkLinearMap S N)
      φ
  let _ : IsLocalizedModule S κ :=
    LinearMap.toKerLocalized_isLocalizedModule
      (S := Localization S)
      (p := S)
      (f := LocalizedModule.mkLinearMap S M)
      (f' := LocalizedModule.mkLinearMap S N)
      φ
  -- Compare the localized kernel module with the actual kernel after localizing the map.
  constructor
  · intro hφ
    have hker :
        LinearMap.ker (LocalizedModule.map S φ) = ⊥ :=
      LinearMap.ker_eq_bot.2 hφ
    have hsub :
        Subsingleton (LinearMap.ker (LocalizedModule.map S φ)) :=
      Submodule.subsingleton_iff_eq_bot.2 hker
    exact ((IsLocalizedModule.iso S κ).toEquiv.subsingleton_congr).2 hsub
  · intro hker
    have hsub :
        Subsingleton (LinearMap.ker (LocalizedModule.map S φ)) :=
      ((IsLocalizedModule.iso S κ).toEquiv.subsingleton_congr).1 hker
    exact LinearMap.ker_eq_bot.1 (Submodule.subsingleton_iff_eq_bot.1 hsub)

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Lemma 10.119.2 (Kollár): if the localized cokernel is trivial, then the localized
map is surjective. -/
private lemma localized_map_surjective_of_subsingleton_cokernel
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N) (S : Submonoid R)
    (hsub : Subsingleton (LocalizedModule S (N ⧸ LinearMap.range φ))) :
    Function.Surjective (LocalizedModule.map S φ) := by
  -- Reuse the chapter-local cokernel criterion instead of reproving the localization step here.
  exact (localized_map_surjective_iff_subsingleton_cokernel φ S).mpr hsub

/-- Helper for Lemma 10.119.2 (Kollár): once `x ∈ 𝔪` is regular and `𝔪` is not associated to
`R / xR`, the source proof returns to the depth-`≥ 2` branch. -/
lemma depth_ge_two_of_regular_element_and_maximalIdeal_not_mem_associatedPrimes_quotSMulTop
    {x : R} (hx : x ∈ maximalIdeal R) (hxreg : IsSMulRegular R x)
    (hassoc : maximalIdeal R ∉ associatedPrimes R (QuotSMulTop x R)) :
    (2 : WithTop ℕ) ≤ moduleDepth R R := by
  have hdepth_ne_zero : moduleDepth R R ≠ 0 := by
    intro hzero
    have hno :=
      (moduleDepth_eq_zero_iff_no_maximalIdeal_regular (R := R) (M := R)).1 hzero
    exact hno ⟨x, hx, hxreg⟩
  have hquot_ne_zero : moduleDepth R (QuotSMulTop x R) ≠ 0 := by
    intro hzero
    exact hassoc <|
      Module.maximalIdeal_mem_associatedPrimes_of_moduleDepth_eq_zero
        (A := R) (N := QuotSMulTop x R) hzero
  have hone_depth : (1 : ℕ∞) ≤ moduleDepth R R :=
    ENat.one_le_iff_ne_zero.2 hdepth_ne_zero
  have hone_quot : (1 : ℕ∞) ≤ moduleDepth R (QuotSMulTop x R) :=
    ENat.one_le_iff_ne_zero.2 hquot_ne_zero
  have htwo_enat : (2 : ℕ∞) ≤ moduleDepth R R := by
    -- Compare `depth(R / xR) = depth(R) - 1` from Lemma 10.72.7 and add `1` back on both sides.
    calc
      (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ moduleDepth R (QuotSMulTop x R) + 1 := by
        simpa [add_comm] using add_le_add_right hone_quot 1
      _ = (moduleDepth R R - 1) + 1 := by
        rw [IsSMulRegular.moduleDepth_quotSMulTop_eq_sub_one (R := R) (M := R) hxreg hx]
      _ = moduleDepth R R := tsub_add_cancel_of_le hone_depth
  simpa using htwo_enat

/-- Helper for Lemma 10.119.2 (Kollár): once the canonical map `R → S` is injective, depth at
least `2` on `R` forces positive depth on the quotient `S / range(R → S)`. -/
lemma moduleDepth_quotient_range_algebraLinearMap_ne_zero_of_depth_ge_two
    {S : Type u} [CommRing S] [Algebra R S] [Module.Finite R S]
    (hinj : Function.Injective (algebraMap R S))
    (hdepth : (2 : WithTop ℕ) ≤ moduleDepth R R)
    (hassoc : maximalIdeal R ∉ associatedPrimes R S) :
    moduleDepth R (S ⧸ LinearMap.range (Algebra.linearMap R S)) ≠ 0 := by
  let η : R →ₗ[R] S := Algebra.linearMap R S
  letI : Module.Finite R (LinearMap.range η) :=
    Module.Finite.of_injective (LinearMap.range η).subtype (LinearMap.range η).injective_subtype
  letI : Module.Finite R (S ⧸ LinearMap.range η) :=
    Module.Finite.of_surjective (LinearMap.range η).mkQ (Submodule.mkQ_surjective _)
  have hdepthS_ne_zero : moduleDepth R S ≠ 0 := by
    -- The exceptional witness already rules out `𝔪` as an associated prime of `S`.
    intro hzero
    exact hassoc <|
      Module.maximalIdeal_mem_associatedPrimes_of_moduleDepth_eq_zero
        (A := R) (N := S) hzero
  have hdepthRange :
      moduleDepth R (LinearMap.range η) = moduleDepth R R := by
    -- Replace `R` by the concrete image of `η` via the injective range equivalence.
    simpa [η] using
      (moduleDepth_eq_of_linearEquiv (R := R)
        (M := R) (N := LinearMap.range η)
        (LinearEquiv.ofInjective η (by simpa [η] using hinj))).symm
  have hdepthQ :
      min (moduleDepth R S) (moduleDepth R (LinearMap.range η) - 1) ≤
        moduleDepth R (S ⧸ LinearMap.range η) := by
    -- Use the canonical quotient row `0 → range(η) → S → S / range(η) → 0`.
    simpa [η] using
      (Submodule.moduleDepth_quotient_ge_min_of_submodule_row
        (R := R) (M := S) (N := LinearMap.range η))
  have honeS : (1 : ℕ∞) ≤ moduleDepth R S :=
    ENat.one_le_iff_ne_zero.2 hdepthS_ne_zero
  have htwoRange : (2 : ℕ∞) ≤ moduleDepth R (LinearMap.range η) := by
    simpa [hdepthRange] using hdepth
  have honeRangeSub :
      (1 : ℕ∞) ≤ moduleDepth R (LinearMap.range η) - 1 := by
    -- Depth at least `2` prevents the predecessor from vanishing.
    have hne :
        moduleDepth R (LinearMap.range η) - 1 ≠ 0 := by
      intro hzero
      have hle : moduleDepth R (LinearMap.range η) ≤ 1 :=
        (tsub_eq_zero_iff_le).1 hzero
      have : (2 : ℕ∞) ≤ (1 : ℕ∞) := le_trans htwoRange hle
      norm_num at this
    exact ENat.one_le_iff_ne_zero.2 hne
  have honeMin :
      (1 : ℕ∞) ≤ min (moduleDepth R S) (moduleDepth R (LinearMap.range η) - 1) := by
    exact le_min honeS honeRangeSub
  exact ENat.one_le_iff_ne_zero.1 (le_trans honeMin hdepthQ)

/-- Helper for Lemma 10.119.2 (Kollár): depth at least `2` excludes Kollár's exceptional finite
extension alternative. -/
lemma not_hasKollarExceptionalFiniteExtension_of_depth_ge_two
    (hdepth : (2 : WithTop ℕ) ≤ moduleDepth R R) :
    ¬ HasKollarExceptionalFiniteExtension R := by
  -- Route correction: work with the canonical quotient row
  -- `0 → range(R → S) → S → S / range(R → S) → 0`, so the cokernel torsion statement can be
  -- transported once through `mkQ` instead of being re-expanded through a raw custom exact row.
  intro hExceptional
  rcases (hasKollarExceptionalFiniteExtension_iff (R := R)).1 hExceptional with
    ⟨S, _, _, _, _, hnotbij, ⟨n, hker, htop⟩, hassoc⟩
  let η : R →ₗ[R] S := Algebra.linearMap R S
  let K : Submodule R R := (RingHom.ker (algebraMap R S) : Submodule R R)
  have hdepthR_ne_zero : moduleDepth R R ≠ 0 := by
    intro hzero
    have hbad : ¬ ((2 : WithTop ℕ) ≤ 0) := by
      norm_num
    have hzeroDepth : (2 : WithTop ℕ) ≤ 0 := by
      have hdepth' := hdepth
      rwa [hzero] at hdepth'
    exact hbad hzeroDepth
  obtain ⟨x, hx, hxreg⟩ :=
    exists_mem_maximalIdeal_isSMulRegular_of_moduleDepth_ne_zero
      (R := R) (M := R) hdepthR_ne_zero
  have hKbot : K = ⊥ := by
    by_cases hK : K = ⊥
    · exact hK
    · letI : Nontrivial K := Submodule.nontrivial_iff_ne_bot.mpr hK
      letI : Module.Finite R K := Module.Finite.of_injective K.subtype K.injective_subtype
      have hdepthK_ne_zero : moduleDepth R K ≠ 0 := by
        -- The same maximal-ideal regular element stays regular on the kernel submodule.
        intro hzero
        have hno :=
          (moduleDepth_eq_zero_iff_no_maximalIdeal_regular (R := R) (M := K)).1 hzero
        exact hno ⟨x, hx, IsSMulRegular.submodule K x hxreg⟩
      exact
        submodule_eq_bot_of_pow_maximalIdeal_smul_eq_bot_of_moduleDepth_ne_zero
          (R := R) K (by simpa [K] using hker) hdepthK_ne_zero
  have hker_bot : RingHom.ker (algebraMap R S) = ⊥ := by
    simpa [K] using hKbot
  have hinj : Function.Injective (algebraMap R S) := by
    exact (RingHom.injective_iff_ker_eq_bot (algebraMap R S)).2 hker_bot
  letI : Module.Finite R (S ⧸ LinearMap.range η) :=
    Module.Finite.of_surjective (LinearMap.range η).mkQ (Submodule.mkQ_surjective _)
  have hquot_depth_ne_zero :
      moduleDepth R (S ⧸ LinearMap.range η) ≠ 0 :=
    moduleDepth_quotient_range_algebraLinearMap_ne_zero_of_depth_ge_two
      (R := R) (S := S) hinj hdepth hassoc
  have hquot_torsion :
      (maximalIdeal R) ^ n • (⊤ : Submodule R (S ⧸ LinearMap.range η)) = ⊥ :=
    pow_smul_top_eq_bot_of_pow_smul_top_le_range_mkQ
      (R := R) (f := η) (n := n) (by simpa [η] using htop)
  have hquot_subsingleton : Subsingleton (S ⧸ LinearMap.range η) :=
    subsingleton_of_pow_maximalIdeal_smul_top_eq_bot_of_moduleDepth_ne_zero
      (R := R) (M := S ⧸ LinearMap.range η) hquot_torsion hquot_depth_ne_zero
  have hsurjη : Function.Surjective η := by
    -- Vanishing of the quotient means the image is all of `S`.
    exact LinearMap.range_eq_top.1 ((Submodule.Quotient.subsingleton_iff).1 hquot_subsingleton)
  have hsurj : Function.Surjective (algebraMap R S) := by
    simpa [η] using hsurjη
  exact hnotbij ⟨hinj, hsurj⟩

/-- Helper for Lemma 10.119.2 (Kollár): over a one-dimensional local ring, a finite module with
positive depth is automatically maximal Cohen-Macaulay. -/
lemma maximalCohenMacaulay_of_moduleDepth_ne_zero_of_ringKrullDim_eq_one
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (hdepth : moduleDepth R M ≠ 0) (hdim : ringKrullDim R = 1) :
    Module.MaximalCohenMacaulay R M := by
  have hle :
      ((moduleDepth R M : ℕ∞) : WithBot ℕ∞) ≤ 1 := by
    -- Positive depth still cannot exceed the ambient support dimension, hence not the ring
    -- dimension `1`.
    calc
      ((moduleDepth R M : ℕ∞) : WithBot ℕ∞) ≤ Module.supportDim R M := depth_le_supportDim
      _ ≤ ringKrullDim R := Module.supportDim_le_ringKrullDim (R := R) (M := M)
      _ = 1 := hdim
  have hge :
      (1 : WithBot ℕ∞) ≤ ((moduleDepth R M : ℕ∞) : WithBot ℕ∞) := by
    -- Nonzero depth means the first regular element already exists.
    exact_mod_cast ENat.one_le_iff_ne_zero.2 hdepth
  refine
    { toFinite := inferInstance
      depth_eq_ringKrullDim := ?_ }
  -- The two inequalities force the depth to be exactly the one-dimensional Krull dimension.
  calc
    ((moduleDepth R M : ℕ∞) : WithBot ℕ∞) = 1 := le_antisymm hle hge
    _ = ringKrullDim R := by simpa [hdim]

/-- Helper for Lemma 10.119.2 (Kollár): in the regular-dimension-one branch, the exceptional
target module is free because its depth is already positive. -/
lemma free_of_nonzero_depth_of_regular_dim_one
    [IsRegularLocalRing R] {S : Type u} [CommRing S] [Algebra R S] [Module.Finite R S]
    [Nontrivial S]
    (hdim : ringKrullDim R = 1)
    (hassoc : maximalIdeal R ∉ associatedPrimes R S) :
    Module.Free R S := by
  have hdepth_ne_zero : moduleDepth R S ≠ 0 := by
    -- The hypothesis on associated primes is precisely the positive-depth input from the source
    -- proof.
    intro hzero
    exact hassoc <|
      Module.maximalIdeal_mem_associatedPrimes_of_moduleDepth_eq_zero
        (A := R) (N := S) hzero
  have hMCM : Module.MaximalCohenMacaulay R S :=
    maximalCohenMacaulay_of_moduleDepth_ne_zero_of_ringKrullDim_eq_one
      (R := R) hdepth_ne_zero hdim
  -- Lemma 10.106.6 now applies verbatim.
  exact free_of_maximalCohenMacaulay_of_isRegularLocalRing (R := R) (M := S) hMCM

/-- Helper for Lemma 10.119.2 (Kollár): in the regular-dimension-one branch, the kernel of an
exceptional finite-extension witness must vanish. -/
lemma injective_algebraMap_of_kernel_pow_torsion_of_regular_dim_one
    [IsRegularLocalRing R] {S : Type u} [CommRing S] [Algebra R S] [Module.Finite R S]
    {n : ℕ}
    (hdim : ringKrullDim R = 1)
    (hker : (maximalIdeal R) ^ n • (RingHom.ker (algebraMap R S) : Submodule R R) = ⊥) :
    Function.Injective (algebraMap R S) := by
  let K : Submodule R R := (RingHom.ker (algebraMap R S) : Submodule R R)
  have hdepthR_ne_zero : moduleDepth R R ≠ 0 := by
    -- A one-dimensional regular local ring has self-depth exactly `1`.
    have hCM : Module.CohenMacaulay R R := inferInstance
    have hdepth_eq :
        ((moduleDepth R R : ℕ∞) : WithBot ℕ∞) = 1 := by
      simpa [Module.supportDim_self_eq_ringKrullDim, hdim] using hCM.supportDim_eq_moduleDepth.symm
    intro hzero
    have : ((0 : ℕ∞) : WithBot ℕ∞) = 1 := by
      simpa [hzero] using hdepth_eq
    norm_num at this
  have hKbot : K = ⊥ := by
    by_cases hK : K = ⊥
    · exact hK
    · letI : Nontrivial K := Submodule.nontrivial_iff_ne_bot.mpr hK
      letI : Module.Finite R K := Module.Finite.of_injective K.subtype K.injective_subtype
      have hdepthK_ne_zero : moduleDepth R K ≠ 0 := by
        -- The regular element witnessing positive depth on `R` restricts to the kernel.
        intro hzero
        have hno :=
          (moduleDepth_eq_zero_iff_no_maximalIdeal_regular (R := R) (M := K)).1 hzero
        obtain ⟨x, hx, hxreg⟩ :=
          exists_mem_maximalIdeal_isSMulRegular_of_moduleDepth_ne_zero
            (R := R) (M := R) hdepthR_ne_zero
        exact hno ⟨x, hx, IsSMulRegular.submodule K x hxreg⟩
      exact
        submodule_eq_bot_of_pow_maximalIdeal_smul_eq_bot_of_moduleDepth_ne_zero
          (R := R) K (by simpa [K] using hker) hdepthK_ne_zero
  -- Translate the kernel computation back to injectivity of the ring map.
  exact (RingHom.injective_iff_ker_eq_bot (algebraMap R S)).2 <| by
    simpa [K] using hKbot

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.119.2 (Kollár): a one-dimensional regular local ring has positive
self-depth. -/
lemma moduleDepth_self_ne_zero_of_regular_dim_one [IsRegularLocalRing R]
    (hdim : ringKrullDim R = 1) :
    moduleDepth R R ≠ 0 := by
  -- Cohen-Macaulay self-depth agrees with the one-dimensional Krull dimension.
  have hCM : Module.CohenMacaulay R R := inferInstance
  have hdepth_eq :
      ((moduleDepth R R : ℕ∞) : WithBot ℕ∞) = 1 := by
    simpa [Module.supportDim_self_eq_ringKrullDim, hdim] using hCM.supportDim_eq_moduleDepth.symm
  intro hzero
  have : ((0 : ℕ∞) : WithBot ℕ∞) = 1 := by
    simpa [hzero] using hdepth_eq
  norm_num at this

/-- Helper for Lemma 10.119.2 (Kollár): in the regular-dimension-one branch, the maximal ideal is
not an associated prime of the self-module `R`. -/
lemma maximalIdeal_not_mem_associatedPrimes_self_of_regular_dim_one [IsRegularLocalRing R]
    (hdim : ringKrullDim R = 1) :
    maximalIdeal R ∉ associatedPrimes R R := by
  have hnontrivial : Nontrivial R := by
    by_contra hR
    letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
    simpa [ringKrullDim_eq_bot_of_subsingleton] using hdim
  -- Positive self-depth rules out `𝔪` as an associated prime.
  exact maximalIdeal_not_mem_associatedPrimes_of_moduleDepth_ne_zero
    (R := R) (M := R) (moduleDepth_self_ne_zero_of_regular_dim_one (R := R) hdim)

/-- Helper for Lemma 10.119.2 (Kollár): in the regular-dimension-one branch, localizing away
from a regular element in the maximal ideal forces any exceptional finite-extension witness to have
rank `1`, hence to be an isomorphism. -/
lemma not_hasKollarExceptionalFiniteExtension_of_regular_dim_one [IsRegularLocalRing R]
    (hdim : ringKrullDim R = 1) :
    ¬ HasKollarExceptionalFiniteExtension R := by
  -- Route correction: follow the source proof at the generic point. First make the finite target
  -- free, then localize at `(0)` where the cokernel vanishes, and finally transport the resulting
  -- rank-one computation back to the closed point to force global rank `1`.
  intro hExceptional
  rcases (hasKollarExceptionalFiniteExtension_iff (R := R)).1 hExceptional with
    ⟨S, hSComm, hSAlg, hSFinite, hSNontrivial, hnotbij, ⟨n, hker, htop⟩, hassoc⟩
  letI : CommRing S := hSComm
  letI : Algebra R S := hSAlg
  letI : Module.Finite R S := hSFinite
  letI : Nontrivial S := hSNontrivial
  letI : IsDomain R := inferInstance
  let η : R →ₗ[R] S := Algebra.linearMap R S
  have hinj : Function.Injective (algebraMap R S) :=
    injective_algebraMap_of_kernel_pow_torsion_of_regular_dim_one
      (R := R) (S := S) hdim hker
  letI : Module.Free R S :=
    free_of_nonzero_depth_of_regular_dim_one (R := R) (S := S) hdim hassoc
  letI : Module.Flat R S := inferInstance
  let Q : Type u := S ⧸ LinearMap.range η
  letI : AddCommGroup Q := inferInstance
  letI : Module R Q := inferInstance
  letI : Module.Finite R Q :=
    Module.Finite.of_surjective (LinearMap.range η).mkQ (Submodule.mkQ_surjective _)
  have hquot_torsion :
      (maximalIdeal R) ^ n • (⊤ : Submodule R Q) = ⊥ :=
    pow_smul_top_eq_bot_of_pow_smul_top_le_range_mkQ
      (R := R) (f := η) (n := n) (by simpa [η] using htop)
  have hdepthR_ne_zero : moduleDepth R R ≠ 0 :=
    moduleDepth_self_ne_zero_of_regular_dim_one (R := R) hdim
  obtain ⟨x, hx, hxreg⟩ :=
    exists_mem_maximalIdeal_isSMulRegular_of_moduleDepth_ne_zero
      (R := R) (M := R) hdepthR_ne_zero
  have hx_ne : x ≠ 0 := by
    intro hx_zero
    subst hx_zero
    exact IsSMulRegular.not_zero (M := R) hxreg
  let p0 : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  have hQloc_sub :
      Subsingleton (LocalizedModule.AtPrime (⊥ : Ideal R) Q) := by
    rw [LocalizedModule.subsingleton_iff]
    intro q
    refine ⟨x ^ n, ?_, ?_⟩
    · simpa [Ideal.primeCompl_bot] using pow_ne_zero n hx_ne
    · have hmem : x ^ n • q ∈ (maximalIdeal R) ^ n • (⊤ : Submodule R Q) := by
        exact Submodule.smul_mem_smul (Ideal.pow_mem_pow hx n) (by simp)
      simpa [hquot_torsion] using hmem
  have hηloc_surj :
      Function.Surjective (LocalizedModule.map (⊥ : Ideal R).primeCompl η) :=
    localized_map_surjective_of_subsingleton_cokernel
      (R := R) (M := R) (N := S) (φ := η) (S := (⊥ : Ideal R).primeCompl) hQloc_sub
  have hker_sub : Subsingleton (LinearMap.ker η) := by
    exact Submodule.subsingleton_iff_eq_bot.2 (LinearMap.ker_eq_bot.2 <| by simpa [η] using hinj)
  letI : Subsingleton (LinearMap.ker η) := hker_sub
  have hηloc_inj :
      Function.Injective (LocalizedModule.map (⊥ : Ideal R).primeCompl η) :=
    (localized_map_injective_iff_subsingleton_kernel
      (φ := η) (S := (⊥ : Ideal R).primeCompl)).2 inferInstance
  let eLoc : LocalizedModule.AtPrime (⊥ : Ideal R) R ≃ₗ[Localization.AtPrime (⊥ : Ideal R)]
      LocalizedModule.AtPrime (⊥ : Ideal R) S :=
    LinearEquiv.ofBijective (LocalizedModule.map (⊥ : Ideal R).primeCompl η)
      ⟨hηloc_inj, hηloc_surj⟩
  have hfinrank_generic :
      Module.finrank (Localization.AtPrime (⊥ : Ideal R))
        (LocalizedModule.AtPrime (⊥ : Ideal R) S) = 1 := by
    have hfinrank_source :
        Module.finrank (Localization.AtPrime (⊥ : Ideal R))
          (LocalizedModule.AtPrime (⊥ : Ideal R) R) = 1 := by
      simpa using
        (Module.finrank_of_isLocalizedModule_of_free
          (R := R) (M := R) (Rₛ := Localization.AtPrime (⊥ : Ideal R))
          ((⊥ : Ideal R).primeCompl) (LocalizedModule.mkLinearMap ((⊥ : Ideal R).primeCompl) R))
    calc
      Module.finrank (Localization.AtPrime (⊥ : Ideal R))
          (LocalizedModule.AtPrime (⊥ : Ideal R) S) =
          Module.finrank (Localization.AtPrime (⊥ : Ideal R))
            (LocalizedModule.AtPrime (⊥ : Ideal R) R) := by
              simpa using eLoc.finrank_eq.symm
      _ = 1 := hfinrank_source
  have hfinrank_one : Module.finrank R S = 1 := by
    calc
      Module.finrank R S =
          Module.finrank (Localization.AtPrime (⊥ : Ideal R))
            (LocalizedModule.AtPrime (⊥ : Ideal R) S) := by
              symm
              simpa using
                (Module.finrank_of_isLocalizedModule_of_free
                  (R := R) (M := S) (Rₛ := Localization.AtPrime (⊥ : Ideal R))
                  ((⊥ : Ideal R).primeCompl)
                  (LocalizedModule.mkLinearMap ((⊥ : Ideal R).primeCompl) S))
      _ = 1 := hfinrank_generic
  have hbij : Function.Bijective (algebraMap R S) :=
    Module.Free.bijective_algebraMap_of_finrank_eq_one hfinrank_one
  exact hnotbij hbij

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.119.2 (Kollár): in an Artinian local ring, every prime ideal is the
maximal ideal. -/
lemma prime_eq_maximalIdeal_of_isArtinianRing {p : Ideal R}
    (hArt : IsArtinianRing R) (hp : p.IsPrime) :
    p = maximalIdeal R := by
  have hpmax : p.IsMaximal := (IsArtinianRing.isPrime_iff_isMaximal p).mp hp
  have hple : p ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal hp.ne_top
  -- Localness collapses the unique maximal ideal of the Artinian ring onto any prime ideal.
  exact hpmax.eq_of_le (IsLocalRing.maximalIdeal.isMaximal R).ne_top hple

/-- Helper for Lemma 10.119.2 (Kollár): the Artinian alternative excludes Kollár's exceptional
finite-extension alternative because every associated prime of a nonzero finite module is then the
maximal ideal. -/
lemma not_hasKollarExceptionalFiniteExtension_of_isArtinianRing
    (hArt : IsArtinianRing R) :
    ¬ HasKollarExceptionalFiniteExtension R := by
  intro hExceptional
  rcases (hasKollarExceptionalFiniteExtension_iff (R := R)).1 hExceptional with
    ⟨S, hSComm, hSAlg, hSFinite, hSNontrivial, _, _, hassoc⟩
  letI : CommRing S := hSComm
  letI : Algebra R S := hSAlg
  letI : Module.Finite R S := hSFinite
  letI : Nontrivial S := hSNontrivial
  obtain ⟨p, hp_assoc⟩ := associatedPrimes.nonempty R S
  have hp_eq : p = maximalIdeal R :=
    prime_eq_maximalIdeal_of_isArtinianRing (R := R) hArt hp_assoc.1
  -- The witness module `S` must have an associated prime, and in the Artinian local case that
  -- associated prime can only be `𝔪`, contradicting the exceptional-extension hypothesis.
  exact hassoc (hp_eq ▸ hp_assoc)

-- Proof sketch: the textbook argument first proves that one of the four alternatives must occur
-- by killing the maximal `𝔪`-power-torsion ideal, finding a nonzerodivisor in `𝔪`, and then
-- splitting into the depth-at-least-two, regular-dimension-one, and exceptional-finite-extension
-- cases via the determinantal trick. It then shows these alternatives are pairwise incompatible,
-- with the nontrivial exclusions against the fourth case handled by the freeness result for
-- maximal Cohen-Macaulay modules over a one-dimensional regular local ring and by the depth
-- inequalities in short exact sequences.
/-- Lemma 10.119.2 (Kollár): for a local Noetherian ring `R`, exactly one of the following holds:
`R` is Artinian, `R` is a regular local ring of dimension `1`, the depth of `R` is at least `2`,
or there exists a finite ring map `R → S` which is not an isomorphism, whose kernel and cokernel
are annihilated by a power of the maximal ideal, such that the maximal ideal of `R` is not an
associated prime of `S` and `S` is nonzero. -/
@[stacks 0BHZ]
theorem kollar_exactly_one_of_artinian_regular_dim_one_depth_ge_two_or_exceptional_finite_extension :
    Xor' (IsArtinianRing R)
      (Xor' (IsRegularLocalRing R ∧ ringKrullDim R = 1)
        (Xor' ((2 : WithTop ℕ) ≤ moduleDepth R R)
          (HasKollarExceptionalFiniteExtension R))) :=
by
  by_cases hArt : IsArtinianRing R
  · have hregFalse : ¬ (IsRegularLocalRing R ∧ ringKrullDim R = 1) := by
      -- An Artinian local ring has Krull dimension `0`, so it cannot be in the dimension-one
      -- regular branch.
      rintro ⟨_, hdim⟩
      have hnontrivial : Nontrivial R := by
        by_contra hR
        letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
        simpa [ringKrullDim_eq_bot_of_subsingleton] using hdim
      have hzero : ringKrullDim R = 0 := by
        exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp
          ((isArtinianRing_iff_krullDimLE_zero).mp hArt)
      have : (0 : WithBot ℕ∞) = 1 := by simpa [hzero] using hdim
      norm_num at this
    have hdepthFalse : ¬ ((2 : WithTop ℕ) ≤ moduleDepth R R) := by
      -- Depth cannot exceed the support dimension, and in the Artinian case that dimension is `0`.
      intro hdepth
      have hdepth' : (2 : ℕ∞) ≤ moduleDepth R R := by
        simpa using hdepth
      have hzero : ringKrullDim R = 0 := by
        exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp
          ((isArtinianRing_iff_krullDimLE_zero).mp hArt)
      have hle :
          ((moduleDepth R R : ℕ∞) : WithBot ℕ∞) ≤ 0 := by
        calc
          ((moduleDepth R R : ℕ∞) : WithBot ℕ∞) ≤ Module.supportDim R R := depth_le_supportDim
          _ ≤ ringKrullDim R := Module.supportDim_le_ringKrullDim (R := R) (M := R)
          _ = 0 := hzero
      have hdepth_le_zero : moduleDepth R R ≤ 0 := by
        exact_mod_cast hle
      have : (2 : ℕ∞) ≤ 0 := le_trans hdepth' hdepth_le_zero
      norm_num at this
    have hExceptionalFalse : ¬ HasKollarExceptionalFiniteExtension R :=
      not_hasKollarExceptionalFiniteExtension_of_isArtinianRing (R := R) hArt
    -- With the Artinian clause true, all three alternatives to the right are already excluded.
    simp [Xor', hArt, hregFalse, hdepthFalse, hExceptionalFalse]
  · by_cases hreg : IsRegularLocalRing R ∧ ringKrullDim R = 1
    · have hdepthFalse : ¬ ((2 : WithTop ℕ) ≤ moduleDepth R R) := by
        -- In the regular one-dimensional branch, Cohen-Macaulay self-depth is exactly `1`.
        letI : IsRegularLocalRing R := hreg.1
        intro hdepth
        have hdepth' : (2 : ℕ∞) ≤ moduleDepth R R := by
          simpa using hdepth
        have hCM : Module.CohenMacaulay R R := inferInstance
        have hdepth_eq_bot :
            ((moduleDepth R R : ℕ∞) : WithBot ℕ∞) = 1 := by
          simpa [Module.supportDim_self_eq_ringKrullDim, hreg.2] using
            hCM.supportDim_eq_moduleDepth.symm
        have hdepth_eq : moduleDepth R R = 1 := by
          exact_mod_cast hdepth_eq_bot
        have : (2 : ℕ∞) ≤ 1 := by
          simpa [hdepth_eq] using hdepth'
        norm_num at this
      letI : IsRegularLocalRing R := hreg.1
      have hExceptionalFalse : ¬ HasKollarExceptionalFiniteExtension R :=
        not_hasKollarExceptionalFiniteExtension_of_regular_dim_one (R := R) hreg.2
      -- The previous helper closes the source's last incompatibility between cases `(2)` and `(4)`.
      simp [Xor', hArt, hreg, hdepthFalse, hExceptionalFalse]
    · by_cases hdepth : (2 : WithTop ℕ) ≤ moduleDepth R R
      · have hExceptionalFalse : ¬ HasKollarExceptionalFiniteExtension R :=
          not_hasKollarExceptionalFiniteExtension_of_depth_ge_two (R := R) hdepth
        -- Positive depth `≥ 2` is already incompatible with the exceptional alternative.
        simp [Xor', hArt, hreg, hdepth, hExceptionalFalse]
      · -- Route correction: first execute the source's torsion-ideal step. If the maximal
        -- `𝔪`-power-torsion ideal is nonzero, quotienting by it already yields case `(4)`.
        let J : Ideal R := maximalIdealPowTorsionIdeal R
        by_cases hJ : J = ⊥
        · have hmax_not_assoc : maximalIdeal R ∉ associatedPrimes R R :=
            maximalIdeal_not_mem_associatedPrimes_self_of_maximalIdealPowTorsionIdeal_eq_bot
              (R := R) (by simpa [J] using hJ)
          have hdepth_ne_zero : moduleDepth R R ≠ 0 := by
            intro hzero
            exact hmax_not_assoc <|
              Module.maximalIdeal_mem_associatedPrimes_of_moduleDepth_eq_zero
                (A := R) (N := R) hzero
          obtain ⟨x, hx, hxreg⟩ :=
            exists_mem_maximalIdeal_isSMulRegular_of_moduleDepth_ne_zero
              (R := R) (M := R) hdepth_ne_zero
          by_cases hx_assoc : maximalIdeal R ∈ associatedPrimes R (QuotSMulTop x R)
          · obtain ⟨y, hy_not_span, hy_mul⟩ :=
              exists_lift_outside_span_singleton_of_associated_quotSMulTop
                (R := R) hx_assoc
            rcases mul_maximalIdeal_into_span_singleton_dichotomy (R := R) (x := x) (y := y) hy_mul
              with hdet | hunit
            · have hExceptional :
                  HasKollarExceptionalFiniteExtension R :=
                hasKollarExceptionalFiniteExtension_of_localized_ratio_determinantal_case
                  (R := R) hx hxreg hy_not_span hdet
              simp [Xor', hArt, hreg, hdepth, hExceptional]
            · have hprincipal :
                (maximalIdeal R).IsPrincipal :=
                  maximalIdeal_isPrincipal_of_unit_multiple_branch
                    (R := R) hx hxreg hy_not_span hy_mul hunit
              have hregular :
                  IsRegularLocalRing R ∧ ringKrullDim R = 1 :=
                regular_dim_one_of_principal_maximalIdeal_and_not_artinian
                  (R := R) hprincipal hArt
              exact False.elim (hreg hregular)
          · exact False.elim <|
              hdepth <|
                depth_ge_two_of_regular_element_and_maximalIdeal_not_mem_associatedPrimes_quotSMulTop
                  (R := R) hx hxreg hx_assoc
        · have hExceptional :
            HasKollarExceptionalFiniteExtension R :=
              hasKollarExceptionalFiniteExtension_of_nonzero_maximalIdealPowTorsionIdeal
                (R := R) hArt (by simpa [J] using hJ)
          simp [Xor', hArt, hreg, hdepth, hExceptional]

end
