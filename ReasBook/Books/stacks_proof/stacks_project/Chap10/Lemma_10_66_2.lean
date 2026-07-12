import StacksProject_2024.Chap10.Definition_10_66_1
import StacksProject_2024.Chap10.Lemma_10_40_4
import StacksProject_2024.Chap10.Lemma_10_66_6
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing Submodule
open scoped TensorProduct

universe u v

section

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
variable (𝔭 : Ideal R) [𝔭.IsPrime]

local notation "Rₚ" => Localization.AtPrime 𝔭
local notation "Mₚ" => LocalizedModule.AtPrime 𝔭 M

/- Domain triage: this file is `source-facing` for weakly associated primes under localization.
The owner abstraction is mathlib's `IsAssociatedPrime`, and the project predicate
`Ideal.IsWeaklyAssociatedToModule` is the source-facing view. Primitive data: none. Derived API:
the three public equivalences in Lemma `10.66.2`. The local annihilator-radical reformulation is
kept internal and derived directly from the owner definition. -/

private theorem torsionOf_eq_bot_colon_singleton
    {A : Type*} {N : Type*} [CommRing A] [AddCommGroup N] [Module A N] (x : N) :
    Ideal.torsionOf A N x = colon (⊥ : Submodule A N) ({x} : Set N) := by
  calc
    Ideal.torsionOf A N x = (Submodule.span A ({x} : Set N)).annihilator := by
      simpa [Ideal.torsionOf] using (Submodule.annihilator_span_singleton x).symm
    _ = colon (⊥ : Submodule A N) ({x} : Set N) := by
      rw [Submodule.bot_colon']

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

private theorem map_torsionOf_atPrime_eq_torsionOf (m : M) :
    Ideal.map (algebraMap R Rₚ) (Ideal.torsionOf R M m) =
      Ideal.torsionOf Rₚ Mₚ (LocalizedModule.mk m (1 : 𝔭.primeCompl)) := by
  calc
    Ideal.map (algebraMap R Rₚ) (Ideal.torsionOf R M m) =
        Ideal.torsionOf Rₚ (Rₚ ⊗[R] M) ((1 : Rₚ) ⊗ₜ[R] m) := by
          simpa using Ideal.map_torsionOf_eq_torsionOf_baseChange_of_flat m
    _ =
        Ideal.torsionOf Rₚ Mₚ
          (((LocalizedModule.equivTensorProduct 𝔭.primeCompl M).symm)
            ((1 : Rₚ) ⊗ₜ[R] m)) := by
          simpa using
            torsionOf_linearEquiv_eq
              ((LocalizedModule.equivTensorProduct 𝔭.primeCompl M).symm)
              ((1 : Rₚ) ⊗ₜ[R] m) |>.symm
    _ = Ideal.torsionOf Rₚ Mₚ (LocalizedModule.mk m (1 : 𝔭.primeCompl)) := by
          simp

private theorem weaklyAssociatedToModule_maximalIdeal_atPrime_iff_isAssociatedPrime :
    Ideal.IsWeaklyAssociatedToModule Rₚ Mₚ (maximalIdeal Rₚ) ↔
      IsAssociatedPrime (maximalIdeal Rₚ) Mₚ := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨show (maximalIdeal Rₚ).IsPrime by infer_instance, x, ?_⟩
    have hminimal :
        (Ideal.torsionOf Rₚ Mₚ x).minimalPrimes = {maximalIdeal Rₚ} := by
      ext q
      constructor
      · intro hq
        have hq_le : q ≤ maximalIdeal Rₚ := IsLocalRing.le_maximalIdeal hq.1.1.ne_top
        exact Set.mem_singleton_iff.mpr <| le_antisymm hq_le (hx.2 hq.1 hq_le)
      · rintro rfl
        exact hx
    have hrad :
        (Ideal.torsionOf Rₚ Mₚ x).radical = maximalIdeal Rₚ := by
      rw [← Ideal.sInf_minimalPrimes, hminimal, sInf_singleton]
    calc
      maximalIdeal Rₚ = (Ideal.torsionOf Rₚ Mₚ x).radical := hrad.symm
      _ = (colon (⊥ : Submodule Rₚ Mₚ) ({x} : Set Mₚ)).radical := by
        rw [torsionOf_eq_bot_colon_singleton]
  · intro h
    exact h.isWeaklyAssociatedToModule

private theorem weaklyAssociatedToModule_iff_isAssociatedPrime_maximalIdeal_atPrime :
    Ideal.IsWeaklyAssociatedToModule R M 𝔭 ↔
      IsAssociatedPrime (maximalIdeal Rₚ) Mₚ := by
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨show (maximalIdeal Rₚ).IsPrime by infer_instance,
      LocalizedModule.mk m (1 : 𝔭.primeCompl), ?_⟩
    have hrad :
        (Ideal.torsionOf Rₚ Mₚ (LocalizedModule.mk m (1 : 𝔭.primeCompl))).radical =
          maximalIdeal Rₚ := by
      rw [← map_torsionOf_atPrime_eq_torsionOf]
      simpa [Localization.AtPrime.map_eq_maximalIdeal] using
        IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes Rₚ 𝔭
          (Ideal.torsionOf R M m) hm
    calc
      maximalIdeal Rₚ =
          (Ideal.torsionOf Rₚ Mₚ (LocalizedModule.mk m (1 : 𝔭.primeCompl))).radical :=
        hrad.symm
      _ = (colon (⊥ : Submodule Rₚ Mₚ)
            ({LocalizedModule.mk m (1 : 𝔭.primeCompl)} : Set Mₚ)).radical := by
          rw [torsionOf_eq_bot_colon_singleton]
  · intro h
    rcases h.2 with ⟨x, hx⟩
    obtain ⟨⟨m, s⟩, rfl⟩ :=
      IsLocalizedModule.mk'_surjective 𝔭.primeCompl
        (LocalizedModule.mkLinearMap 𝔭.primeCompl M) x
    have hunit : IsUnit (Localization.mk (1 : R) s : Rₚ) := by
      simpa [Localization.mk_eq_mk'] using
        (show IsUnit (IsLocalization.mk' Rₚ (1 : R) s) from isUnit_of_invertible _)
    have htorsion :
        Ideal.torsionOf Rₚ Mₚ (LocalizedModule.mk m s) =
          Ideal.torsionOf Rₚ Mₚ (LocalizedModule.mk m (1 : 𝔭.primeCompl)) := by
      calc
        Ideal.torsionOf Rₚ Mₚ (LocalizedModule.mk m s) =
            Ideal.torsionOf Rₚ Mₚ
              ((Localization.mk (1 : R) s : Rₚ) •
                LocalizedModule.mk m (1 : 𝔭.primeCompl)) := by
                  congr 1
                  simpa using
                    (LocalizedModule.mk_smul_mk (1 : R) m s (1 : 𝔭.primeCompl)).symm
        _ = Ideal.torsionOf Rₚ Mₚ (LocalizedModule.mk m (1 : 𝔭.primeCompl)) :=
          torsionOf_smul_eq hunit (LocalizedModule.mk m (1 : 𝔭.primeCompl))
    have hx' :
        maximalIdeal Rₚ =
          (Ideal.torsionOf Rₚ Mₚ (LocalizedModule.mk m s)).radical := by
      calc
        maximalIdeal Rₚ =
            (colon (⊥ : Submodule Rₚ Mₚ)
              ({Function.uncurry
                  (IsLocalizedModule.mk' (LocalizedModule.mkLinearMap 𝔭.primeCompl M))
                  (m, s)} : Set Mₚ)).radical := hx
        _ = (colon (⊥ : Submodule Rₚ Mₚ) ({LocalizedModule.mk m s} : Set Mₚ)).radical := by
              simp [IsLocalizedModule.mk_eq_mk']
        _ = (Ideal.torsionOf Rₚ Mₚ (LocalizedModule.mk m s)).radical := by
              rw [← torsionOf_eq_bot_colon_singleton]
    have hlocal :
        maximalIdeal Rₚ ∈
          (Ideal.torsionOf Rₚ Mₚ (LocalizedModule.mk m (1 : 𝔭.primeCompl))).minimalPrimes := by
      haveI :
          (Ideal.torsionOf Rₚ Mₚ (LocalizedModule.mk m s)).radical.IsPrime := by
        simpa [hx'] using (show (maximalIdeal Rₚ).IsPrime by infer_instance)
      rw [← htorsion, hx', ← Ideal.radical_minimalPrimes, Ideal.minimalPrimes_eq_subsingleton_self]
      simp
    have hmap :
        maximalIdeal Rₚ ∈
          (Ideal.map (algebraMap R Rₚ) (Ideal.torsionOf R M m)).minimalPrimes := by
      simpa [map_torsionOf_atPrime_eq_torsionOf] using hlocal
    rw [IsLocalization.minimalPrimes_map 𝔭.primeCompl Rₚ (Ideal.torsionOf R M m)] at hmap
    exact ⟨m, by simpa [Localization.AtPrime.comap_maximalIdeal] using hmap⟩

/-- Lemma 10.66.2, clauses `(1) ↔ (2)`: weak association descends and ascends along localization at
`𝔭`. -/
@[stacks 0566]
theorem isWeaklyAssociatedToModule_iff_isWeaklyAssociatedToModule_maximalIdeal_atPrime :
    Ideal.IsWeaklyAssociatedToModule R M 𝔭 ↔
      Ideal.IsWeaklyAssociatedToModule Rₚ Mₚ (maximalIdeal Rₚ) := by
  exact
    (weaklyAssociatedToModule_iff_isAssociatedPrime_maximalIdeal_atPrime 𝔭).trans
      (weaklyAssociatedToModule_maximalIdeal_atPrime_iff_isAssociatedPrime 𝔭).symm

/-- Lemma 10.66.2, clauses `(1) ↔ (3)`: a prime `𝔭` is weakly associated to `M` exactly when the
maximal ideal of `R_𝔭` is an associated prime of `M_𝔭`. -/
@[stacks 0566]
theorem isWeaklyAssociatedToModule_iff_isAssociatedPrime_maximalIdeal_atPrime :
    Ideal.IsWeaklyAssociatedToModule R M 𝔭 ↔
      IsAssociatedPrime (maximalIdeal Rₚ) Mₚ := by
  exact weaklyAssociatedToModule_iff_isAssociatedPrime_maximalIdeal_atPrime 𝔭

/-- Lemma 10.66.2, clauses `(2) ↔ (3)`: over the local ring `R_𝔭`, weak association of the
maximal ideal is equivalent to the canonical predicate `IsAssociatedPrime`. -/
@[stacks 0566]
theorem isWeaklyAssociatedToModule_maximalIdeal_atPrime_iff_isAssociatedPrime :
    Ideal.IsWeaklyAssociatedToModule Rₚ Mₚ (maximalIdeal Rₚ) ↔
      IsAssociatedPrime (maximalIdeal Rₚ) Mₚ := by
  exact weaklyAssociatedToModule_maximalIdeal_atPrime_iff_isAssociatedPrime 𝔭

end
