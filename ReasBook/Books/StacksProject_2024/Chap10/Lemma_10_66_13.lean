import Mathlib
import StacksProject_2024.Chap10.Lemma_10_66_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
variable [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-
Domain triage:
* `source-facing`: the textbook item identifies the image of `WeakAss_S(M)` in `Spec R` under a
  finite ring map.
* `core/canonical`: the owner abstraction in this chapter is the set-valued declaration
  `weaklyAssociatedPrimes R M`.
* `bridge/view`: the only primitive module-theoretic datum needed pointwise is the annihilator
  ideal `Ideal.torsionOf _ _ m`; the set-level equality should be expressed directly in terms of
  the owner set rather than by a parallel wrapper declaration.
-/

namespace weaklyAssociatedPrimes

omit [Module.Finite R S] in
private theorem comap_torsionOf_eq (m : M) :
    Ideal.comap (algebraMap R S) (Ideal.torsionOf S M m) = Ideal.torsionOf R M m := by
  ext r
  rw [Ideal.mem_comap, Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff]
  simp [algebraMap_smul]

/-- Helper for Lemma 10.66.13: in an integral extension, minimal primes contract to
minimal primes. -/
private theorem comap_mem_minimalPrimes_of_isIntegral_zero
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] {𝔮 : Ideal B} (h𝔮 : 𝔮 ∈ minimalPrimes B) :
    Ideal.comap (algebraMap A B) 𝔮 ∈ minimalPrimes A := by
  -- TODO: localize at `𝔭 := Ideal.comap (algebraMap A B) 𝔮` and `𝔮`, use lying over in the
  -- induced local integral map `A_𝔭 → B_𝔮` to produce a prime below `𝔮`, then use minimality of
  -- `𝔮` over `0` to force equality and conclude that every prime below `𝔭` is equal to `𝔭`.
  sorry

/-- Helper for Lemma 10.66.13: reduce contraction of minimal primes over arbitrary ideals to the
zero-ideal case in the quotient rings. -/
private theorem comap_mem_minimalPrimes_of_isIntegral [Algebra.IsIntegral R S]
    {I : Ideal S} {𝔮 : Ideal S} (h𝔮 : 𝔮 ∈ I.minimalPrimes) :
    Ideal.comap (algebraMap R S) 𝔮 ∈ (Ideal.comap (algebraMap R S) I).minimalPrimes := by
  let Icomap : Ideal R := Ideal.comap (algebraMap R S) I
  rw [Ideal.minimalPrimes_eq_comap] at h𝔮
  rcases h𝔮 with ⟨𝔮bar, h𝔮bar, h𝔮bar_eq⟩
  letI : Algebra (R ⧸ Icomap) (S ⧸ I) := inferInstance
  have h𝔭bar :
      Ideal.comap (algebraMap (R ⧸ Icomap) (S ⧸ I)) 𝔮bar ∈ minimalPrimes (R ⧸ Icomap) :=
    comap_mem_minimalPrimes_of_isIntegral_zero
      (A := R ⧸ Icomap) (B := S ⧸ I) h𝔮bar
  rw [Ideal.minimalPrimes_eq_comap]
  refine ⟨Ideal.comap (algebraMap (R ⧸ Icomap) (S ⧸ I)) 𝔮bar, h𝔭bar, ?_⟩
  -- Compose the quotient contractions to recover the original contracted prime of `𝔮`.
  calc
    Ideal.comap (Ideal.Quotient.mk Icomap)
        (Ideal.comap (algebraMap (R ⧸ Icomap) (S ⧸ I)) 𝔮bar)
      = Ideal.comap (algebraMap R (S ⧸ I)) 𝔮bar := by
          rw [Ideal.comap_comap]
          rfl
    _ = Ideal.comap (algebraMap R S) (Ideal.comap (Ideal.Quotient.mk I) 𝔮bar) := by
          rw [Ideal.comap_comap]
          rfl
    _ = Ideal.comap (algebraMap R S) 𝔮 := by
          simpa [h𝔮bar_eq]

/-- Helper for Lemma 10.66.13: once minimal primes contract correctly under an integral map, a
weakly associated prime of `M` over `S` contracts to a weakly associated prime over `R`. -/
private theorem comap_mem_weaklyAssociatedPrimes_of_mem
    {𝔮 : Ideal S} (h𝔮 : 𝔮 ∈ weaklyAssociatedPrimes S M) :
    Ideal.comap (algebraMap R S) 𝔮 ∈ weaklyAssociatedPrimes R M := by
  rcases h𝔮 with ⟨m, hm⟩
  -- Contract the minimal-prime witness for the `S`-annihilator of `m`.
  have hminimal :
      Ideal.comap (algebraMap R S) 𝔮 ∈
        (Ideal.comap (algebraMap R S) (Ideal.torsionOf S M m)).minimalPrimes :=
    comap_mem_minimalPrimes_of_isIntegral (R := R) (S := S) hm
  -- The contracted annihilator is exactly the annihilator of the same element over `R`.
  refine ⟨m, ?_⟩
  simpa [comap_torsionOf_eq (R := R) (S := S) (M := M) m] using hminimal

/-- Lemma 10.66.13: let `f : Spec S → Spec R` be induced by `algebraMap R S`. If `R → S` is a
finite ring map, then the image of the weakly associated primes of `M` over `S` under `f` is
exactly the weakly associated primes of `M` over `R`. -/
-- Proof sketch: the inclusion `weaklyAssociatedPrimes R M ⊆ Ideal.comap (algebraMap R S) ''
-- weaklyAssociatedPrimes S M` is the restriction-of-scalars inclusion proved earlier. For the
-- reverse inclusion, start with `𝔮 ∈ weaklyAssociatedPrimes S M`, choose an element of `M` whose
-- annihilator has `𝔮` as a minimal prime, and use finiteness of `R → S`, prime avoidance, and the
-- semilocal structure of `S` over the contraction `𝔭` to produce an element whose annihilator over
-- `R` has `𝔭` as a minimal prime.
theorem restrictScalars_eq_image_comap_of_finite :
    Ideal.comap (algebraMap R S) '' weaklyAssociatedPrimes S M =
      weaklyAssociatedPrimes R M := by
  -- The earlier item already proves the inclusion from `R` to the image from `S`.
  refine Set.Subset.antisymm ?_ subset_comap_image
  rintro 𝔭 ⟨𝔮, h𝔮, rfl⟩
  -- For the reverse inclusion, contract a weakly associated prime witness along the finite map.
  exact comap_mem_weaklyAssociatedPrimes_of_mem (R := R) (S := S) (M := M) h𝔮

end weaklyAssociatedPrimes

end
