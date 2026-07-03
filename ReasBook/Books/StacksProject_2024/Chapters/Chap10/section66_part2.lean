import Mathlib
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_66_15 (from Chap10) -/
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

/-! ### Lemma_10_66_16 (from Chap10) -/
universe u v

section

open weaklyAssociatedPrimes

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (S : Submonoid R)

local notation "Mₛ" => LocalizedModule S M

/- Domain triage:
* `core/canonical`: the owner abstraction is the set-valued declaration
  `weaklyAssociatedPrimes R M`.
* `bridge/view`: Lemma 10.66.15 provides the localization comparison
  `weaklyAssociatedPrimes.inter_eq_localizedModule`.
* This file is derived owner API: the regularity hypothesis forces every weakly associated prime
  of `M` to be disjoint from `S`, so the bridge theorem specializes to equality. -/

/-- Lemma 10.66.16: if every element of the multiplicative subset `S` acts on `M` by a
nonzerodivisor, then the weakly associated primes of `M` coincide with those of the localized
module `LocalizedModule S M`, viewed as an `R`-module. -/
-- Proof sketch: the hypothesis implies that the localization map `M → LocalizedModule S M` is
-- injective, so Lemma 10.66.4 gives `WeakAss(M) ⊆ WeakAss(S⁻¹M)`. Conversely, if `n / s` in the
-- localization has annihilator with minimal prime `𝔭`, then the same ideal annihilates `n : M`,
-- so `𝔭` is already weakly associated to `M`.
theorem weaklyAssociatedPrimes_eq_localizedModule
    (hS : ∀ s : S, IsSMulRegular M s) :
    weaklyAssociatedPrimes R M = weaklyAssociatedPrimes R Mₛ := by
  have hdisjoint :
      weaklyAssociatedPrimes R M ⊆ {𝔭 : Ideal R | Disjoint (S : Set R) (𝔭 : Set R)} := by
    intro 𝔭 h𝔭
    change Disjoint (S : Set R) (𝔭 : Set R)
    rw [Set.disjoint_left]
    intro s hsS hs𝔭
    have hs_not_mem : (s : R) ∉ ⋃ 𝔮 ∈ weaklyAssociatedPrimes R M, 𝔮 := by
      rw [weaklyAssociatedPrimes.biUnion_eq_compl_regular, Set.mem_compl_iff, Set.mem_setOf_eq]
      exact not_not_intro <| hS ⟨s, hsS⟩
    exact hs_not_mem <| Set.mem_iUnion.2 ⟨𝔭, Set.mem_iUnion.2 ⟨h𝔭, hs𝔭⟩⟩
  have hlocal :
      weaklyAssociatedPrimes R M ∩ {𝔭 : Ideal R | Disjoint (S : Set R) (𝔭 : Set R)} =
        weaklyAssociatedPrimes R Mₛ :=
    inter_eq_localizedModule S
  simpa [Set.inter_eq_left.2 hdisjoint] using hlocal

end

/-! ### Lemma_10_66_17 (from Chap10) -/
universe u v

open LocalizedModule

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Lemma 10.66.17: the canonical map from `M` to the product of the localizations `M_𝔭`,
indexed by the weakly associated primes `𝔭` of `M`, is injective. -/
-- Proof sketch: if `x : M` maps to zero in every localization at a weakly associated prime of
-- `M`, consider the cyclic submodule generated by `x`. Any weakly associated prime of that cyclic
-- module is also weakly associated to `M` by Lemma `10.66.4`, but localizing at such a prime would
-- keep the cyclic module nonzero, contradicting that `x` localizes to zero there. Hence the cyclic
-- module has no weakly associated primes, so Lemma `10.66.5` forces it to vanish and therefore
-- `x = 0`.
theorem weaklyAssociatedPrimes_localizationMap_injective :
    Function.Injective
      ⇑(LinearMap.pi fun p : weaklyAssociatedPrimes R M ↦ mkLinearMap p.1.primeCompl M) := by
  intro x y hxy
  apply sub_eq_zero.mp
  let z := x - y
  have hzero : weaklyAssociatedPrimes R (R ∙ z) = ∅ := by
    ext p
    constructor
    · intro hp
      have hwp : Ideal.IsWeaklyAssociatedToModule R (R ∙ z) p := hp
      haveI : p.IsPrime := hwp.isPrime
      have hpM : p ∈ weaklyAssociatedPrimes R M :=
        weaklyAssociatedPrimes.subset_of_injective
          (Submodule.subtype_injective (R ∙ z)) hwp
      have hp_support : (⟨p, inferInstance⟩ : PrimeSpectrum R) ∈ Module.support R (R ∙ z) := by
        simpa [z] using hwp.mem_support
      have hp_ne_zero : mkLinearMap p.primeCompl M z ≠ 0 := by
        simpa [z] using
          (mem_support_span_singleton_iff_localized_ne_zero
            ⟨p, inferInstance⟩ z).1 hp_support
      have hp_eq_zero : mkLinearMap p.primeCompl M z = 0 := by
        have hp_xy :
            mkLinearMap p.primeCompl M x =
              mkLinearMap p.primeCompl M y :=
          congrArg (fun f ↦ f ⟨p, hpM⟩) hxy
        simpa [z, LinearMap.map_sub] using
          sub_eq_zero.mpr hp_xy
      exact hp_ne_zero hp_eq_zero
    · simp
  have hsub :
      Subsingleton (R ∙ z) := by
    simpa using
      ((subsingleton_iff_weaklyAssociatedPrimes_eq_empty :
        Subsingleton (R ∙ z) ↔ weaklyAssociatedPrimes R (R ∙ z) = ∅)).2 hzero
  exact Submodule.span_singleton_eq_bot.mp (Submodule.subsingleton_iff_eq_bot.mp hsub)

end

/-! ### Lemma_10_66_18 (from Chap10) -/
open scoped nonZeroDivisors

universe u v w

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {N : Type w} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
variable [Module.Flat R N]

local notation "R⁰" => nonZeroDivisors R
local notation "T" => Algebra.algebraMapSubmonoid S R⁰
local notation "Sₖ" => Localization T
local notation "Nₖ" => LocalizedModule T N

/-
Domain triage:
- primary domain: weakly associated primes under fraction-ring base change;
- `core/canonical` owner: localize the `S`-module `N` at the image `T` of `R⁰`, namely
  `Nₖ = LocalizedModule T N`;
- `bridge/view`: the textbook tensor model `(S ⊗[R] FractionRing R) ⊗[S] N`.

This item is best stated at the owner layer `Nₖ`, because Lemmas `10.66.15` and `10.66.16`
already provide the canonical localization API for `weaklyAssociatedPrimes`. The tensor-product
presentation is only a derived realization of the same base change, and in the domain case this is
exactly the usual fraction-ring base change.
-/

/-- Lemma 10.66.18, owner form: if `R → S` is a ring map, `N` is an `S`-module that is flat over
`R`, and `T` is the image in `S` of the nonzerodivisors of `R`, then the weakly
associated primes of `N` over `S` coincide with those of the canonical localization owner
`Nₖ = LocalizedModule T N`, still computed over `S`. -/
-- Proof sketch: every element of `R⁰` acts regularly on `N` by flatness over the domain `R`, so
-- every element of its image `T` in `S` acts regularly as well. Lemma 10.66.16 then identifies
-- `WeakAss_S(N)` with `WeakAss_S(Nₖ)`.
theorem weaklyAssociatedPrimes_eq_fractionRingBaseChange_as_SModule :
    weaklyAssociatedPrimes S N = weaklyAssociatedPrimes S Nₖ := by
  refine weaklyAssociatedPrimes_eq_localizedModule T ?_
  intro t
  rcases t.2 with ⟨r, hr, hs⟩
  have ht : IsSMulRegular N (algebraMap R S r) :=
    (isSMulRegular_algebraMap_iff S).2
      (Module.Flat.isSMulRegular_of_nonZeroDivisors hr)
  simpa [hs] using ht

/-- Lemma 10.66.18: the weakly associated primes of `N` over `S` are exactly the contractions of
the weakly associated primes of the canonical base change `Nₖ` along the
localization map `S → Sₖ`. -/
-- Proof sketch: first replace `N` by the canonical owner `Nₖ` using the previous theorem. Then
-- apply Lemma 10.66.15 (1) to the localization of `N` at `T`.
theorem weaklyAssociatedPrimes_baseChange_to_fractionRing_eq_image_comap :
    weaklyAssociatedPrimes S N =
      Ideal.comap (algebraMap S Sₖ) '' weaklyAssociatedPrimes Sₖ Nₖ := by
  calc
    weaklyAssociatedPrimes S N = weaklyAssociatedPrimes S Nₖ :=
      weaklyAssociatedPrimes_eq_fractionRingBaseChange_as_SModule
    _ = Ideal.comap (algebraMap S Sₖ) '' weaklyAssociatedPrimes Sₖ Nₖ :=
      (weaklyAssociatedPrimes.localizedModule_eq_image_comap T).symm

end
