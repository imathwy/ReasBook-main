import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_40_4
import StacksProject_2024.stacks_project.Chap10.Definition_10_66_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (S : Submonoid R)

local notation "Rₛ" => Localization S
local notation "Mₛ" => LocalizedModule S M

/-
Domain triage: this file lies in commutative algebra of weakly associated primes under
localization. The owner abstraction is the project declaration `weaklyAssociatedPrimes R M`; the
current item contributes derived owner API describing how that set transforms under
`R → Localization S`. Primitive data are only the ring, module, and multiplicative subset. The
range/disjointness comparison is an auxiliary bridge; the public surface should stay at the owner
set level rather than introducing a parallel wrapper around localization data.
-/

private theorem torsionOf_linearEquiv_eq
    {A : Type*} {N : Type*} {N' : Type*} [CommRing A]
    [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']
    (e : N ≃ₗ[A] N') (x : N) :
    Ideal.torsionOf A N' (e x) = Ideal.torsionOf A N x := by
  ext a
  rw [Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff]
  constructor
  · intro ha
    apply e.injective
    simpa using ha
  · intro ha
    simpa using congrArg e ha

private theorem torsionOf_smul_eq
    {A : Type*} {N : Type*} [CommRing A] [AddCommGroup N] [Module A N]
    {u : A} (hu : IsUnit u) (x : N) :
    Ideal.torsionOf A N (u • x) = Ideal.torsionOf A N x := by
  ext a
  rw [Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff]
  simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using
    (hu.smul_eq_zero : u • (a • x) = 0 ↔ a • x = 0)

private theorem comap_torsionOf_eq_torsionOf (m : Mₛ) :
    Ideal.comap (algebraMap R Rₛ) (Ideal.torsionOf Rₛ Mₛ m) = Ideal.torsionOf R Mₛ m := by
  ext r
  rw [Ideal.mem_comap, Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff]
  simp [algebraMap_smul]

private theorem map_torsionOf_eq_torsionOf (m : M) :
    Ideal.map (algebraMap R Rₛ) (Ideal.torsionOf R M m) =
      Ideal.torsionOf Rₛ Mₛ (LocalizedModule.mk m (1 : S)) := by
  calc
    Ideal.map (algebraMap R Rₛ) (Ideal.torsionOf R M m) =
        Ideal.torsionOf Rₛ (Rₛ ⊗[R] M) ((1 : Rₛ) ⊗ₜ[R] m) := by
          simpa using Ideal.map_torsionOf_eq_torsionOf_baseChange_of_flat m
    _ =
        Ideal.torsionOf Rₛ Mₛ
          (((LocalizedModule.equivTensorProduct S M).symm) ((1 : Rₛ) ⊗ₜ[R] m)) := by
            simpa using
              torsionOf_linearEquiv_eq
                ((LocalizedModule.equivTensorProduct S M).symm)
                ((1 : Rₛ) ⊗ₜ[R] m) |>.symm
    _ = Ideal.torsionOf Rₛ Mₛ (LocalizedModule.mk m (1 : S)) := by
          simp

private lemma mem_range_comap_iff_disjoint_of_isPrime {𝔭 : Ideal R} (h𝔭 : 𝔭.IsPrime) :
    𝔭 ∈ Set.range (Ideal.comap (algebraMap R Rₛ)) ↔
      Disjoint (S : Set R) (𝔭 : Set R) := by
  constructor
  · rintro ⟨J, rfl⟩
    rw [IsLocalization.disjoint_comap_iff S Rₛ]
    intro hJ
    simpa [hJ] using h𝔭.ne_top
  · intro h𝔭S
    exact ⟨Ideal.map (algebraMap R Rₛ) 𝔭,
      IsLocalization.comap_map_of_isPrime_disjoint S Rₛ h𝔭 h𝔭S⟩

namespace weaklyAssociatedPrimes

/-- Lemma 10.66.15 (1): via the canonical injection
`Spec(Rₛ) → Spec(R)`, the weakly associated primes of the localized module `Mₛ` computed over
`R` agree with those computed over `Rₛ`. -/
-- Proof sketch: for `m : LocalizedModule S M`, compare the annihilator ideal of `m` over `R`
-- with its annihilator over `Rₛ`; the latter is the localization of the former. Minimal primes
-- of these annihilators correspond under `Ideal.comap (algebraMap R Rₛ)` by the standard order
-- isomorphism for prime ideals in a localization.
lemma localizedModule_eq_image_comap :
    Ideal.comap (algebraMap R Rₛ) '' weaklyAssociatedPrimes Rₛ Mₛ =
      weaklyAssociatedPrimes R Mₛ := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro 𝔭 ⟨𝔮, h𝔮, rfl⟩
    rcases h𝔮 with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have hminimal :
        Ideal.comap (algebraMap R Rₛ) 𝔮 ∈
          (Ideal.comap (algebraMap R Rₛ) (Ideal.torsionOf Rₛ Mₛ m)).minimalPrimes := by
      rw [IsLocalization.minimalPrimes_comap S Rₛ (Ideal.torsionOf Rₛ Mₛ m)]
      exact ⟨𝔮, hm, rfl⟩
    simpa [comap_torsionOf_eq_torsionOf S m] using hminimal
  · rintro 𝔭 h𝔭
    rcases h𝔭 with ⟨m, hm⟩
    have hminimal :
        𝔭 ∈
          (Ideal.comap (algebraMap R Rₛ) (Ideal.torsionOf Rₛ Mₛ m)).minimalPrimes := by
      simpa [comap_torsionOf_eq_torsionOf S m] using hm
    obtain ⟨𝔮, h𝔮, hcomap⟩ :=
      Ideal.exists_minimalPrimes_comap_eq (algebraMap R Rₛ) 𝔭 hminimal
    exact ⟨𝔮, ⟨m, h𝔮⟩, hcomap⟩

/-- Lemma 10.66.15 (2): viewed inside `Spec R` via the canonical map
`Spec(Rₛ) → Spec(R)`, the weakly associated primes of `Mₛ` are exactly the weakly associated
primes of `M` lying in the image of that map. -/
-- Proof sketch: for prime ideals of `R`, belonging to the image of
-- `Ideal.comap (algebraMap R Rₛ)` is equivalent to being disjoint from `S`. Then apply the
-- localization criterion for weakly associated primes from Lemma 10.66.2.
lemma inter_localization_range_eq :
    weaklyAssociatedPrimes R M ∩ Set.range (Ideal.comap (algebraMap R Rₛ)) =
      weaklyAssociatedPrimes R Mₛ := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro 𝔭 ⟨h𝔭, hrange⟩
    have hprime : 𝔭.IsPrime := h𝔭.isPrime
    have hdisj : Disjoint (S : Set R) (𝔭 : Set R) :=
      (mem_range_comap_iff_disjoint_of_isPrime S hprime).1 hrange
    rcases h𝔭 with ⟨m, hm⟩
    let 𝔮 : Ideal Rₛ := Ideal.map (algebraMap R Rₛ) 𝔭
    have hcomap : Ideal.comap (algebraMap R Rₛ) 𝔮 = 𝔭 :=
      by
        simp [𝔮, IsLocalization.comap_map_of_isPrime_disjoint S Rₛ hprime hdisj]
    have h𝔮 :
        𝔮 ∈ weaklyAssociatedPrimes Rₛ Mₛ := by
      refine ⟨LocalizedModule.mk m (1 : S), ?_⟩
      have hminimal :
          𝔮 ∈
            (Ideal.map (algebraMap R Rₛ) (Ideal.torsionOf R M m)).minimalPrimes := by
        rw [IsLocalization.minimalPrimes_map S Rₛ (Ideal.torsionOf R M m)]
        change Ideal.comap (algebraMap R Rₛ) 𝔮 ∈ (Ideal.torsionOf R M m).minimalPrimes
        simpa [hcomap] using hm
      simpa [map_torsionOf_eq_torsionOf S m, 𝔮] using hminimal
    have hlocal : Ideal.comap (algebraMap R Rₛ) 𝔮 ∈ weaklyAssociatedPrimes R Mₛ := by
      rw [← localizedModule_eq_image_comap S]
      exact ⟨𝔮, h𝔮, rfl⟩
    simpa [hcomap] using hlocal
  · intro 𝔭 h𝔭
    rw [← localizedModule_eq_image_comap S] at h𝔭
    rcases h𝔭 with ⟨𝔮, h𝔮, rfl⟩
    rcases h𝔮 with ⟨x, hx⟩
    have hx' :
        Ideal.comap (algebraMap R Rₛ) 𝔮 ∈
          (Ideal.comap (algebraMap R Rₛ) (Ideal.torsionOf Rₛ Mₛ x)).minimalPrimes := by
      rw [IsLocalization.minimalPrimes_comap S Rₛ (Ideal.torsionOf Rₛ Mₛ x)]
      exact ⟨𝔮, hx, rfl⟩
    obtain ⟨⟨m, s⟩, rfl⟩ :=
      IsLocalizedModule.mk'_surjective S (LocalizedModule.mkLinearMap S M) x
    have hunit : IsUnit (Localization.mk (1 : R) s : Rₛ) := by
      simpa [Localization.mk_eq_mk'] using
        (show IsUnit (IsLocalization.mk' Rₛ (1 : R) s) from isUnit_of_invertible _)
    have htorsion :
        Ideal.torsionOf Rₛ Mₛ (LocalizedModule.mk m s) =
          Ideal.torsionOf Rₛ Mₛ (LocalizedModule.mk m (1 : S)) := by
      calc
        Ideal.torsionOf Rₛ Mₛ (LocalizedModule.mk m s) =
            Ideal.torsionOf Rₛ Mₛ
              ((Localization.mk (1 : R) s : Rₛ) • LocalizedModule.mk m (1 : S)) := by
                congr 1
                simpa using (LocalizedModule.mk_smul_mk (1 : R) m s (1 : S)).symm
        _ = Ideal.torsionOf Rₛ Mₛ (LocalizedModule.mk m (1 : S)) :=
          torsionOf_smul_eq hunit (LocalizedModule.mk m (1 : S))
    have h𝔮_mk :
        𝔮 ∈ (Ideal.torsionOf Rₛ Mₛ (LocalizedModule.mk m s)).minimalPrimes := by
      simpa [IsLocalizedModule.mk_eq_mk'] using hx
    have h𝔮_one :
        𝔮 ∈ (Ideal.torsionOf Rₛ Mₛ (LocalizedModule.mk m (1 : S))).minimalPrimes := by
      simpa [htorsion] using h𝔮_mk
    have h𝔮_map :
        𝔮 ∈
          (Ideal.map (algebraMap R Rₛ) (Ideal.torsionOf R M m)).minimalPrimes := by
      simpa [map_torsionOf_eq_torsionOf S m] using h𝔮_one
    have h𝔮_pre :
        𝔮 ∈
          Ideal.comap (algebraMap R Rₛ) ⁻¹'
            (Ideal.torsionOf R M m).minimalPrimes := by
      rw [IsLocalization.minimalPrimes_map S Rₛ (Ideal.torsionOf R M m)] at h𝔮_map
      exact h𝔮_map
    have hmem :
        Ideal.comap (algebraMap R Rₛ) 𝔮 ∈ (Ideal.torsionOf R M m).minimalPrimes := by
      simpa [Set.mem_preimage] using h𝔮_pre
    exact ⟨⟨m, hmem⟩, ⟨𝔮, rfl⟩⟩

/-- Reformulation of Lemma 10.66.15 (2) using the disjointness criterion for primes in the image
of `Spec(Rₛ) → Spec(R)`. -/
lemma inter_eq_localizedModule :
    weaklyAssociatedPrimes R M ∩ {𝔭 : Ideal R | Disjoint (S : Set R) (𝔭 : Set R)} =
      weaklyAssociatedPrimes R Mₛ := by
  calc
    weaklyAssociatedPrimes R M ∩ {𝔭 : Ideal R | Disjoint (S : Set R) (𝔭 : Set R)} =
        weaklyAssociatedPrimes R M ∩ Set.range (Ideal.comap (algebraMap R Rₛ)) := by
          ext 𝔭
          constructor
          · rintro ⟨h𝔭, hdisj⟩
            exact ⟨h𝔭, (mem_range_comap_iff_disjoint_of_isPrime S h𝔭.isPrime).2 hdisj⟩
          · rintro ⟨h𝔭, himage⟩
            exact ⟨h𝔭, (mem_range_comap_iff_disjoint_of_isPrime S h𝔭.isPrime).1 himage⟩
    _ = weaklyAssociatedPrimes R Mₛ := inter_localization_range_eq S

end weaklyAssociatedPrimes

end
