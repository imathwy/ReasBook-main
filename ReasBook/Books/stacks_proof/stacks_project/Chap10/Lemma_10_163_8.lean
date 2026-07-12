import Mathlib
import StacksProject_2024.Chap10.Definition_10_37_11
import StacksProject_2024.Chap10.Lemma_10_25_1
import StacksProject_2024.Chap10.Lemma_10_72_5
import StacksProject_2024.Chap10.Lemma_10_119_2_Koll_r
import StacksProject_2024.Chap10.Lemma_10_119_7
import StacksProject_2024.Chap10.Lemma_10_157_2
import StacksProject_2024.Chap10.Lemma_10_157_4_Serre_s_criterion_for_normality
import StacksProject_2024.Chap10.Lemma_10_163_4
import StacksProject_2024.Chap10.Lemma_10_163_5

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S] [IsNormalRing R]

/-- Helper for Lemma 10.163.8: localizing the self-module agrees with the localized ring itself. -/
private noncomputable abbrev localized_self_linearEquiv_entry
    {A : Type*} [CommRing A] (p : Ideal A) [p.IsPrime] :
    LocalizedModule.AtPrime p A ≃ₗ[Localization.AtPrime p] Localization.AtPrime p :=
  (LocalizedModule.equivTensorProduct p.primeCompl A).trans
    (Algebra.TensorProduct.rid A (Localization.AtPrime p) (Localization.AtPrime p)).toLinearEquiv

/-- Helper for Lemma 10.163.8: a normal Noetherian ring is regular in codimension at most `1`. -/
private lemma normal_ring_serreConditionR_one
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsNormalRing A] :
    SerreConditionR A 1 := by
  refine
    { toIsNoetherian := inferInstance
      isRegularLocalRing_localizationAtPrime := ?_ }
  intro p hp
  let B := Localization.AtPrime p.asIdeal
  letI : IsDomain B := isDomain_localizationAtPrime p
  by_cases hp0 : p.asIdeal.primeHeight = 0
  · -- Proof comment: a height-zero prime localization of a normal ring is a field, hence regular.
    have hdim0 : ringKrullDim B = 0 := by
      calc
        ringKrullDim B = p.asIdeal.height := by
          simpa [B] using
            (IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal B)
        _ = p.asIdeal.primeHeight := by
          rw [Ideal.height_eq_primeHeight]
        _ = 0 := by
          simpa using congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hp0
    letI : Ring.KrullDimLE 0 B := ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hdim0
    let hField : IsField B := Ring.KrullDimLE.isField_of_isDomain
    have hmax : maximalIdeal B = ⊥ :=
      (IsLocalRing.isField_iff_maximalIdeal_eq (R := B)).1 hField
    have hspan0 : (maximalIdeal B).spanFinrank = 0 := by
      simpa [hmax] using (Submodule.spanFinrank_bot : (⊥ : Ideal B).spanFinrank = 0)
    have hspan_le : (maximalIdeal B).spanFinrank ≤ ringKrullDim B := by
      simpa [hspan0, hdim0]
    exact IsRegularLocalRing.of_spanFinrank_maximalIdeal_le (R := B) hspan_le
  · -- Proof comment: in codimension one, the normal local domain is a DVR and hence regular.
    have hp1 : p.asIdeal.primeHeight = 1 := by
      exact le_antisymm hp (ENat.one_le_iff_ne_zero.2 hp0)
    have hdim1 : ringKrullDim B = 1 := by
      calc
        ringKrullDim B = p.asIdeal.height := by
          simpa [B] using
            (IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal B)
        _ = p.asIdeal.primeHeight := by
          rw [Ideal.height_eq_primeHeight]
        _ = 1 := by
          simpa using congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hp1
    letI : IsIntegrallyClosed B := isIntegrallyClosed_localizationAtPrime p
    have hNormalDimOne :
        ∃ (_ : IsLocalRing B) (_ : IsNoetherianRing B) (_ : IsDomain B)
          (_ : IsIntegrallyClosed B), ringKrullDim B = 1 := by
      exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, hdim1⟩
    have hRegDim : IsRegularLocalRing B ∧ ringKrullDim B = 1 := by
      exact ((discreteValuationRing_tfae (A := B)).out 4 2).mp hNormalDimOne
    exact hRegDim.1

/-- Helper for Lemma 10.163.8: a positive-dimensional normal local domain avoids Kollár's
exceptional finite-extension case. -/
private lemma normal_local_domain_no_exceptional_finite_extension
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    [IsIntegrallyClosed A] (hdim : ringKrullDim A ≠ 0) :
    ¬ HasKollarExceptionalFiniteExtension A := by
  intro hExceptional
  rcases (hasKollarExceptionalFiniteExtension_iff (R := A)).1 hExceptional with
    ⟨T, _, _, _, hT_nontrivial, hnotbij, ⟨n, hkerPow, hcokerPow⟩, hmax_not_assoc⟩
  let η : A →+* T := algebraMap A T
  have hnot_field : ¬ IsField A := by
    intro hfield
    letI : Field A := hfield.toField
    exact hdim (ringKrullDim_eq_zero_of_field A)
  have hmax_ne_bot : maximalIdeal A ≠ ⊥ := by
    intro hbot
    exact hnot_field ((IsLocalRing.isField_iff_maximalIdeal_eq).2 hbot)
  have hforall :
      ∀ q ∈ associatedPrimes A T, ¬ maximalIdeal A ≤ q := by
    intro q hq hmq
    have hq_le : q ≤ maximalIdeal A := IsLocalRing.le_maximalIdeal hq.1.ne_top
    have hq_eq : q = maximalIdeal A := le_antisymm hq_le hmq
    exact hmax_not_assoc (hq_eq ▸ hq)
  obtain ⟨x, hx, hxreg⟩ :=
    (exists_mem_isSMulRegular_iff_forall_not_le_associatedPrimes
      (R := A) (M := T) (I := maximalIdeal A)).2 hforall
  have hx_ne_zero : x ≠ 0 := by
    intro hx0
    have : (1 : T) = 0 := by
      exact hxreg.right_eq_zero_of_smul <| by simpa [hx0]
    exact one_ne_zero this
  have hηinj : Function.Injective η := by
    -- Proof comment: the kernel is annihilated by a nonzero element of the domain, so it vanishes.
    refine (RingHom.injective_iff_ker_eq_bot η).2 ?_
    ext a
    constructor
    · intro ha
      have hxa_mem :
          x ^ n • a ∈ (maximalIdeal A) ^ n • (RingHom.ker η : Submodule A A) := by
        exact Submodule.smul_mem_smul (Ideal.pow_mem_pow hx n) ha
      have hxa_zero : x ^ n * a = 0 := by
        have : x ^ n • a ∈ ((maximalIdeal A) ^ n • (RingHom.ker η : Submodule A A)) := hxa_mem
        rw [hkerPow] at this
        simpa [Submodule.mem_bot, smul_eq_mul] using this
      have ha_zero : a = 0 := by
        rcases mul_eq_zero.mp hxa_zero with hxpow_zero | ha_zero
        · exact False.elim ((pow_ne_zero n hx_ne_zero) hxpow_zero)
        · exact ha_zero
      simpa [Submodule.mem_bot, ha_zero]
    · intro ha
      have ha_zero : a = 0 := by
        simpa [Submodule.mem_bot] using ha
      simpa [RingHom.mem_ker, ha_zero]
  have hxreg_image : IsSMulRegular T (algebraMap A T x) := by
    -- Proof comment: regular scalar multiplication by `x` transports to regular multiplication by its image.
    refine IsSMulRegular.of_right_eq_zero_of_smul ?_
    intro t ht
    exact hxreg.right_eq_zero_of_smul <| by simpa [Algebra.smul_def] using ht
  have hAwayInj :
      Function.Injective (Localization.awayMap η x) := by
    rw [Localization.awayMap_injective_iff]
    intro a ha
    have ha_mem : a ∈ RingHom.ker η := by
      simpa [η] using ha
    have hxa_mem :
        x ^ n • a ∈ (maximalIdeal A) ^ n • (RingHom.ker η : Submodule A A) := by
      exact Submodule.smul_mem_smul (Ideal.pow_mem_pow hx n) ha_mem
    refine ⟨n, ?_⟩
    have : x ^ n • a ∈ ((maximalIdeal A) ^ n • (RingHom.ker η : Submodule A A)) := hxa_mem
    rw [hkerPow] at this
    simpa [Submodule.mem_bot, smul_eq_mul] using this
  have hAwaySurj :
      Function.Surjective (Localization.awayMap η x) := by
    rw [Localization.awayMap_surjective_iff]
    intro t
    -- Proof comment: the cokernel torsion condition writes a power of `x` times `t` inside the image.
    have hxt_mem :
        x ^ n • t ∈ (maximalIdeal A) ^ n • (⊤ : Submodule A T) := by
      exact Submodule.smul_mem_smul (Ideal.pow_mem_pow hx n) (by simp)
    have hxt_range : x ^ n • t ∈ (Algebra.linearMap A T).range := hcokerPow hxt_mem
    rcases hxt_range with ⟨a, ha⟩
    refine ⟨a, n, ?_⟩
    simpa [η, Algebra.smul_def, map_pow] using ha
  let e : Localization.Away x ≃ₐ[A] Localization.Away (η x) :=
    AlgEquiv.ofBijective (Localization.awayMapₐ (Algebra.ofId A T) x) <|
      by
        simpa [Localization.awayMapₐ] using ⟨hAwayInj, hAwaySurj⟩
  have hpow :
      Submonoid.powers x ≤ nonZeroDivisors A := by
    intro y hy
    rcases (show ∃ m : ℕ, x ^ m = y by simpa [Submonoid.mem_powers_iff] using hy) with ⟨m, rfl⟩
    rw [mem_nonZeroDivisors_iff_right]
    intro a ha
    rcases mul_eq_zero.mp ha with ha_zero | hxpow_zero
    · exact ha_zero
    · exact False.elim ((pow_ne_zero m hx_ne_zero) hxpow_zero)
  letI : Algebra (Localization.Away x) (FractionRing A) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe
      (Localization.Away x) (FractionRing A) (Submonoid.powers x) (nonZeroDivisors A) hpow
  letI : IsScalarTower A (Localization.Away x) (FractionRing A) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le
      (Localization.Away x) (FractionRing A) (Submonoid.powers x) (nonZeroDivisors A) hpow
  letI : IsFractionRing (Localization.Away x) (FractionRing A) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Submonoid.powers x) (Localization.Away x) (FractionRing A)
  let ψ : T →ₐ[A] FractionRing A :=
    (IsScalarTower.toAlgHom A (Localization.Away x) (FractionRing A)).comp <|
      e.symm.toAlgHom.comp
        (IsScalarTower.toAlgHom A T (Localization.Away (η x)))
  have hTLocInj :
      Function.Injective (algebraMap T (Localization.Away (η x))) := by
    refine IsLocalization.injective
      (M := Submonoid.powers (η x)) (S := Localization.Away (η x)) ?_
    intro y hy
    rcases
      (show ∃ m : ℕ, (η x) ^ m = y by simpa [Submonoid.mem_powers_iff] using hy) with ⟨m, rfl⟩
    rw [mem_nonZeroDivisors_iff_right]
    intro t ht
    exact (hxreg_image.pow m) <| by simpa [mul_comm] using ht
  have hFracInj :
      Function.Injective (algebraMap (Localization.Away x) (FractionRing A)) := by
    simpa using (IsFractionRing.injective (Localization.Away x) (FractionRing A))
  have hψinj : Function.Injective ψ := by
    exact hFracInj.comp (e.symm.injective.comp hTLocInj)
  have hηsurj : Function.Surjective η := by
    intro t
    -- Proof comment: every integral element in the fraction field comes from the integrally closed base.
    have ht_integral : IsIntegral A t := Algebra.IsIntegral.isIntegral t
    have hψt_integral : IsIntegral A (ψ t) := IsIntegral.map ψ ht_integral
    obtain ⟨a, ha⟩ :=
      IsIntegrallyClosed.algebraMap_eq_of_integral (K := FractionRing A) hψt_integral
    refine ⟨a, hψinj ?_⟩
    calc
      ψ (η a) = algebraMap A (FractionRing A) a := by simpa [η] using (AlgHom.commutes ψ a)
      _ = ψ t := ha
  exact hnotbij ⟨hηinj, hηsurj⟩

/-- Helper for Lemma 10.163.8: a normal Noetherian local domain satisfies the `(S₂)` depth bound. -/
private lemma normal_local_domain_depth_ge_min_two
    (A : Type*) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    [IsIntegrallyClosed A] :
    WithBot.some (moduleDepth A A : ℕ∞) ≥
      min (2 : WithBot ℕ∞) (ringKrullDim A) := by
  -- Proof comment: split by dimension and use the source trichotomy in the remaining case.
  by_cases hdim0 : ringKrullDim A = 0
  · simpa [hdim0]
  · by_cases hdim1 : ringKrullDim A = 1
    · have hNormalDimOne :
          ∃ (_ : IsLocalRing A) (_ : IsNoetherianRing A) (_ : IsDomain A)
            (_ : IsIntegrallyClosed A), ringKrullDim A = 1 := by
        exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, hdim1⟩
      have hRegDim : IsRegularLocalRing A ∧ ringKrullDim A = 1 := by
        exact ((discreteValuationRing_tfae (A := A)).out 4 2).mp hNormalDimOne
      letI : IsRegularLocalRing A := hRegDim.1
      have hCM : Module.CohenMacaulay A A := inferInstance
      have hdepth_eq :
          WithBot.some (moduleDepth A A : ℕ∞) = 1 := by
        simpa [Module.supportDim_self_eq_ringKrullDim, hRegDim.2] using
          hCM.supportDim_eq_moduleDepth.symm
      simpa [hdim1, hdepth_eq]
    · have hArtFalse : ¬ IsArtinianRing A := by
        intro hArt
        exact hdim0 <|
          ringKrullDimZero_iff_ringKrullDim_eq_zero.mp
            ((isArtinianRing_iff_krullDimLE_zero).mp hArt)
      have hRegFalse : ¬ (IsRegularLocalRing A ∧ ringKrullDim A = 1) := by
        rintro ⟨_, hdimA⟩
        exact hdim1 hdimA
      have hExceptionalFalse : ¬ HasKollarExceptionalFiniteExtension A :=
        normal_local_domain_no_exceptional_finite_extension (A := A) hdim0
      have hxor :=
        kollar_exactly_one_of_artinian_regular_dim_one_depth_ge_two_or_exceptional_finite_extension
          (R := A)
      have hdepth : (2 : WithTop ℕ) ≤ moduleDepth A A := by
        simpa [Xor', hArtFalse, hRegFalse, hExceptionalFalse] using hxor
      have hdepth_enat : (2 : ℕ∞) ≤ moduleDepth A A := by
        simpa using hdepth
      have hdepth_bot : (2 : WithBot ℕ∞) ≤ WithBot.some (moduleDepth A A : ℕ∞) := by
        simpa [WithBot.some_eq_coe] using (WithBot.coe_le_coe.2 hdepth_enat)
      exact le_trans (min_le_left _ _) hdepth_bot

/-- Helper for Lemma 10.163.8: a normal Noetherian ring satisfies Serre's condition `(S₂)`. -/
private lemma normal_ring_serreConditionS_two
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsNormalRing A] :
    SerreConditionS A 2 := by
  refine
    { toIsNoetherian := inferInstance
      toSerreConditionS := ?_ }
  refine
    { toFinite := inferInstance
      moduleDepth_localizationAtPrime_ge_min_supportDim := ?_ }
  intro p
  let B := Localization.AtPrime p.asIdeal
  letI : IsDomain B := isDomain_localizationAtPrime p
  letI : IsIntegrallyClosed B := isIntegrallyClosed_localizationAtPrime p
  let e := localized_self_linearEquiv_entry (A := A) p.asIdeal
  have hsupport :
      Module.supportDim B (LocalizedModule.AtPrime p.asIdeal A) = ringKrullDim B := by
    simpa [B, Module.supportDim_self_eq_ringKrullDim] using Module.supportDim_eq_of_equiv e
  have hdepth :
      moduleDepth B (LocalizedModule.AtPrime p.asIdeal A) = moduleDepth B B := by
    simpa [B] using moduleDepth_eq_of_equiv e
  -- Proof comment: replace the localized self-module by the localized ring and use the local normal-domain estimate.
  rw [hsupport, hdepth]
  exact normal_local_domain_depth_ge_min_two B

/-- Helper for Lemma 10.163.8: a reduced Noetherian local ring of positive dimension does not have
its maximal ideal among the associated primes of the self-module. -/
private lemma reduced_local_ring_maximalIdeal_not_associated_of_positive_krullDim
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsReduced A]
    (hdim : ringKrullDim A ≠ 0) :
    maximalIdeal A ∉ associatedPrimes A A := by
  intro hmax
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hmax
  rcases hmax with ⟨_, x, hx⟩
  have hnot_field : ¬ IsField A := by
    intro hfield
    letI : Field A := hfield.toField
    exact hdim (ringKrullDim_eq_zero_of_field A)
  have hmax_ne_bot : maximalIdeal A ≠ ⊥ := by
    intro hbot
    exact hnot_field ((IsLocalRing.isField_iff_maximalIdeal_eq).2 hbot)
  have hx_not_unit : ¬ IsUnit x := by
    intro hx_unit
    have hbot : maximalIdeal A = ⊥ := by
      rw [hx]
      ext a
      constructor
      · intro ha
        have ha_zero : a * x = 0 := by
          simpa [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul] using ha
        rcases hx_unit with ⟨u, rfl⟩
        apply_fun fun y => y * ↑u⁻¹ at ha_zero
        simpa [mul_assoc] using ha_zero
      · intro ha
        rw [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul]
        have ha_zero : a = 0 := by
          simpa using ha
        simp [ha_zero]
    exact hmax_ne_bot hbot
  have hx_mem : x ∈ maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hx_not_unit
  have hx_sq_zero : x * x = 0 := by
    have hx_colon : x ∈ Submodule.colon (⊥ : Submodule A A) ({x} : Set A) := by
      simpa [hx] using hx_mem
    simpa [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul] using hx_colon
  have hx_zero : x = 0 := by
    exact IsNilpotent.eq_zero ⟨2, by simpa [pow_two] using hx_sq_zero⟩
  have htop : maximalIdeal A = ⊤ := by
    rw [hx, hx_zero]
    ext a
    simp [Submodule.mem_colon_singleton, smul_eq_mul]
  exact (IsLocalRing.maximalIdeal.isMaximal A).1.1 htop

/-- Helper for Lemma 10.163.8: a zero-dimensional regular local ring is a field. -/
private lemma regularLocalRing_isField_of_krullDim_eq_zero
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsRegularLocalRing A]
    (hdim : ringKrullDim A = 0) :
    IsField A := by
  have hspan : (maximalIdeal A).spanFinrank = ringKrullDim A :=
    (isRegularLocalRing_iff A).1 inferInstance
  have hspan_zero : (maximalIdeal A).spanFinrank = 0 := by
    simpa [hdim] using hspan
  have hfg : (maximalIdeal A).FG := IsNoetherian.noetherian (maximalIdeal A)
  have hbot : maximalIdeal A = ⊥ :=
    (Submodule.spanFinrank_eq_zero_iff_eq_bot hfg).1 hspan_zero
  exact (IsLocalRing.isField_iff_maximalIdeal_eq).2 hbot

/-- Helper for Lemma 10.163.8: under `(S₁)`, a positive-height localization has nonzero depth. -/
private lemma localized_depth_ne_zero_of_serreConditionS_one
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (hS : SerreConditionS A 1) (p : PrimeSpectrum A)
    (hp0 : p.asIdeal.primeHeight ≠ 0) :
    moduleDepth (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) ≠ 0 := by
  let B := Localization.AtPrime p.asIdeal
  have hdim_ne_zero : ringKrullDim B ≠ 0 := by
    intro hdim
    have hheight : p.asIdeal.height = 0 := by
      simpa [B, hdim] using
        (IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal B).symm
    rw [Ideal.height_eq_primeHeight] at hheight
    exact hp0 hheight
  have hdim_ne_bot : ringKrullDim B ≠ ⊥ := ringKrullDim_ne_bot
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hdim_ne_bot
  have hd_ne_zero : d ≠ 0 := by
    intro hd_zero
    exact hdim_ne_zero <| by simpa [hd_zero] using hd.symm
  have hdim_ge_one : (1 : WithBot ℕ∞) ≤ ringKrullDim B := by
    have hd_ge_one : (1 : ℕ∞) ≤ d := ENat.one_le_iff_ne_zero.2 hd_ne_zero
    simpa [hd] using (WithBot.coe_le_coe.2 hd_ge_one)
  by_contra hdepth
  have hmin_le_zero : min (1 : WithBot ℕ∞) (ringKrullDim B) ≤ 0 := by
    simpa [B, hdepth] using
      (SerreConditionS.moduleDepth_localizationAtPrime_ge_min (R := A) hS p)
  have hmin_ge_one : (1 : WithBot ℕ∞) ≤ min (1 : WithBot ℕ∞) (ringKrullDim B) := by
    exact le_min le_rfl hdim_ge_one
  have : (1 : WithBot ℕ∞) ≤ 0 := le_trans hmin_ge_one hmin_le_zero
  exact not_le_of_gt (by simp : (0 : WithBot ℕ∞) < 1) this

/-- Helper for Lemma 10.163.8: a regular element gives an injective map to the away-localization. -/
private lemma localizationAway_injective_of_regular_element
    {A : Type*} [CommRing A] {t : A} (ht : IsSMulRegular A t) :
    Function.Injective (algebraMap A (Localization.Away t)) := by
  refine IsLocalization.injective (M := Submonoid.powers t) (S := Localization.Away t) ?_
  intro y hy
  rcases (show ∃ n : ℕ, t ^ n = y by simpa [Submonoid.mem_powers_iff] using hy) with ⟨n, rfl⟩
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  exact (ht.pow n) <| by simpa [mul_comm] using hx

/-- Helper for Lemma 10.163.8: maximal ideals upstairs contract strictly below the closed point. -/
private lemma away_maximal_contraction_lt_closed_point
    {A : Type*} [CommRing A] [IsLocalRing A] {t : A}
    (ht_mem : t ∈ maximalIdeal A) (m : Ideal (Localization.Away t)) [m.IsMaximal] :
    Ideal.comap (algebraMap A (Localization.Away t)) m < maximalIdeal A := by
  let qA : Ideal A := Ideal.comap (algebraMap A (Localization.Away t)) m
  haveI : qA.IsPrime := Ideal.comap_isPrime (algebraMap A (Localization.Away t)) m
  have hle : qA ≤ maximalIdeal A := IsLocalRing.le_maximalIdeal_of_isPrime qA
  refine lt_of_le_of_ne hle ?_
  intro hqA
  have ht_qA : t ∈ qA := by
    simpa [qA, hqA] using ht_mem
  have ht_m : algebraMap A (Localization.Away t) t ∈ m := by
    simpa [qA] using ht_qA
  exact
    Ideal.IsMaximal.ne_top (inferInstance : m.IsMaximal) <|
      Ideal.eq_top_of_isUnit_mem _ ht_m (IsLocalization.Away.algebraMap_isUnit t)

/-- Helper for Lemma 10.163.8: localizing `A[1/t]` at a prime matches the localization at the
contracted prime. -/
private noncomputable abbrev away_localization_compare_to_contracted_prime
    {A : Type*} [CommRing A] {t : A} (m : Ideal (Localization.Away t)) [m.IsPrime] :
    Localization.AtPrime (Ideal.comap (algebraMap A (Localization.Away t)) m) ≃ₐ[A]
      Localization.AtPrime m :=
  IsLocalization.localizationLocalizationAtPrimeIsoLocalization (M := Submonoid.powers t) m

/-- Helper for Lemma 10.163.8: localizing a prime localization again matches localizing at the
underlying prime. -/
private noncomputable abbrev atPrime_localization_compare_to_under
    {A : Type*} [CommRing A] (p : PrimeSpectrum A)
    (qA : Ideal (Localization.AtPrime p.asIdeal)) [qA.IsPrime] :
    Localization.AtPrime (Ideal.comap (algebraMap A (Localization.AtPrime p.asIdeal)) qA) ≃ₐ[A]
      Localization.AtPrime qA :=
  IsLocalization.localizationLocalizationAtPrimeIsoLocalization (M := p.asIdeal.primeCompl) qA

/-- Helper for Lemma 10.163.8: maximal ideals of `A[1/t]` lie over strictly smaller primes. -/
private lemma away_maximal_under_primeHeight_lt_entry
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (p : PrimeSpectrum A) {t : Localization.AtPrime p.asIdeal}
    (ht_mem : t ∈ maximalIdeal (Localization.AtPrime p.asIdeal))
    (m : Ideal (Localization.Away t)) [m.IsMaximal] :
    let qA : Ideal (Localization.AtPrime p.asIdeal) :=
      Ideal.comap (algebraMap (Localization.AtPrime p.asIdeal) (Localization.Away t)) m
    let qR : Ideal A := qA.under A
    qR.primeHeight < p.asIdeal.primeHeight := by
  let B := Localization.AtPrime p.asIdeal
  let qA : Ideal B := Ideal.comap (algebraMap B (Localization.Away t)) m
  haveI : qA.IsPrime := Ideal.comap_isPrime (algebraMap B (Localization.Away t)) m
  have hltA : qA < maximalIdeal B :=
    away_maximal_contraction_lt_closed_point (A := B) ht_mem m
  have hheightA : qA.primeHeight < (maximalIdeal B).primeHeight :=
    Ideal.primeHeight_strict_mono hltA
  have hunder : (qA.under A).primeHeight = qA.primeHeight := by
    simpa [B, Ideal.under_def] using
      (IsLocalization.primeHeight_comap p.asIdeal.primeCompl (A := B) qA)
  have hmax : (maximalIdeal B).primeHeight = p.asIdeal.primeHeight := by
    exact WithBot.coe_inj.mp <| by
      calc
        ((maximalIdeal B).primeHeight : WithBot ℕ∞) = ringKrullDim B := by
          simpa [B] using (IsLocalRing.maximalIdeal_primeHeight_eq_ringKrullDim (R := B))
        _ = p.asIdeal.height := IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal B
        _ = (p.asIdeal.primeHeight : WithBot ℕ∞) := by rw [Ideal.height_eq_primeHeight]
  change (qA.under A).primeHeight < p.asIdeal.primeHeight
  calc
    (qA.under A).primeHeight = qA.primeHeight := hunder
    _ < (maximalIdeal B).primeHeight := hheightA
    _ = p.asIdeal.primeHeight := hmax

/-- Helper for Lemma 10.163.8: `(R₀)` and `(S₁)` force every prime localization to be reduced. -/
private lemma isReduced_localizationAtPrime_of_serreConditionR_zero_and_serreConditionS_one_entry
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (hR : SerreConditionR A 0) (hS : SerreConditionS A 1)
    (p : PrimeSpectrum A) :
    IsReduced (Localization.AtPrime p.asIdeal) := by
  -- Route correction: follow the source induction on prime height from the reducedness criterion.
  let P : ℕ → Prop := fun n =>
    ∀ q : PrimeSpectrum A,
      ENat.toNat q.asIdeal.primeHeight = n → IsReduced (Localization.AtPrime q.asIdeal)
  have hP : ∀ n : ℕ, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih q hqn
    by_cases hq0 : q.asIdeal.primeHeight = 0
    · have hregular : IsRegularLocalRing (Localization.AtPrime q.asIdeal) :=
        hR.isRegularLocalRing_localizationAtPrime q hq0.le
      letI := hregular
      have hdim : ringKrullDim (Localization.AtPrime q.asIdeal) = 0 := by
        simpa [Ideal.height_eq_primeHeight, hq0] using
          (IsLocalization.AtPrime.ringKrullDim_eq_height
            q.asIdeal (Localization.AtPrime q.asIdeal))
      letI : Field (Localization.AtPrime q.asIdeal) :=
        (regularLocalRing_isField_of_krullDim_eq_zero
          (A := Localization.AtPrime q.asIdeal) hdim).toField
      infer_instance
    · let B := Localization.AtPrime q.asIdeal
      have hdepth_ne_zero :
          moduleDepth B B ≠ 0 :=
        localized_depth_ne_zero_of_serreConditionS_one (A := A) hS q hq0
      obtain ⟨t, ht_mem, ht_reg⟩ :=
        exists_mem_maximalIdeal_isSMulRegular_of_moduleDepth_ne_zero
          (R := B) (M := B) hdepth_ne_zero
      have hinj : Function.Injective (algebraMap B (Localization.Away t)) :=
        localizationAway_injective_of_regular_element (A := B) ht_reg
      have hAwayReduced : IsReduced (Localization.Away t) := by
        refine isReduced_ofLocalizationMaximal (Localization.Away t) fun m _ ↦ ?_
        let qA : Ideal B := Ideal.comap (algebraMap B (Localization.Away t)) m
        haveI : qA.IsPrime := Ideal.comap_isPrime (algebraMap B (Localization.Away t)) m
        let qR : Ideal A := qA.under A
        haveI : qR.IsPrime := by
          simpa [qR, Ideal.under_def] using (Ideal.comap_isPrime (algebraMap A B) qA)
        let q' : PrimeSpectrum A := ⟨qR, inferInstance⟩
        have hltHeight : qR.primeHeight < q.asIdeal.primeHeight := by
          simpa [B, qA, qR] using
            away_maximal_under_primeHeight_lt_entry (A := A) q ht_mem m
        have hltNat : ENat.toNat qR.primeHeight < n := by
          rw [← hqn]
          have hltCoe :
              ((ENat.toNat qR.primeHeight : ℕ∞) < ENat.toNat q.asIdeal.primeHeight) := by
            simpa
              [ENat.coe_toNat (ne_of_lt (Ideal.primeHeight_lt_top qR)),
                ENat.coe_toNat (ne_of_lt (Ideal.primeHeight_lt_top q.asIdeal))] using hltHeight
          exact_mod_cast hltCoe
        have hred_qR : IsReduced (Localization.AtPrime qR) :=
          ih (ENat.toNat qR.primeHeight) hltNat q' rfl
        have hred_qA : IsReduced (Localization.AtPrime qA) := by
          let e := atPrime_localization_compare_to_under (A := A) q qA
          letI : IsReduced (Localization.AtPrime qR) := hred_qR
          exact isReduced_of_injective e.symm.toRingHom e.symm.injective
        let eAway := away_localization_compare_to_contracted_prime (A := B) (t := t) m
        letI : IsReduced (Localization.AtPrime qA) := hred_qA
        exact isReduced_of_injective eAway.symm.toRingHom eAway.symm.injective
      letI : IsReduced (Localization.Away t) := hAwayReduced
      exact isReduced_of_injective (algebraMap B (Localization.Away t)) hinj
  exact hP (ENat.toNat p.asIdeal.primeHeight) p rfl

/-
Domain-style sampling pass:
* primary domain: Noetherian commutative algebra of ascent of normality along flat maps;
* sampled owner declarations of the same kind:
  - `IsNormalRing`, the chapter owner for ring normality;
  - `isNormalRing_iff_serreConditionR_one_and_serreConditionS_two`, the canonical Serre-criterion
    owner-level characterization of normality;
  - `serreConditionR_of_flat_of_fiber`, the chapter ascent theorem for `(R₁)`;
  - `serreConditionS_of_flat_of_fiber`, the chapter ascent theorem for `(S₂)`;
  - `Algebra.EssFiniteType.isNoetherianRing`, the canonical Noetherianity owner for the fiber
    ring `p.asIdeal.Fiber S` via the upstream instance `Algebra.EssFiniteType R p.asIdeal.ResidueField`.

Best owner abstraction:
* the public target stays the source-facing normality theorem, but its proof should pass entirely
  through the owner predicates `IsNormalRing`, `SerreConditionR`, and `SerreConditionS`, rather
  than duplicating local wheel definitions for the Serre conditions.

Primitive data vs. derived API:
* primitive data: the flat algebra `R → S`, the Noetherian hypotheses on `R` and `S`, the normal
  base-ring owner `[IsNormalRing R]`, and the fiberwise normality hypothesis `hfiber`;
* derived API: the `(R₁)` and `(S₂)` instances for the base and the fibers, obtained canonically
  from the Serre criterion, together with fiberwise Noetherianity obtained canonically from
  `Algebra.EssFiniteType.isNoetherianRing`, and then fed into the existing ascent theorems.

Source/core/bridge triage:
* `source-facing`: `isNormalRing_of_flat_of_fiber`, the textbook ascent statement for normality;
* `core/canonical`: `IsNormalRing`, `SerreConditionR`, and `SerreConditionS`;
* `bridge/view`: the two ascent theorems for `(R₁)` and `(S₂)` along the flat map.
-/

/-- Helper for Lemma 10.163.8: `(R₁)` and `(S₂)` imply the weaker Serre conditions `(R₀)` and
`(S₁)`. -/
lemma weaker_serre_conditions_of_serre_conditions
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (hR : A ⊧ (R₁)) (hS : A ⊧ (S₂)) :
    SerreConditionR A 0 ∧ SerreConditionS A 1 := by
  refine ⟨?_, ?_⟩
  · -- Proof comment: the codimension bound in `(R₁)` immediately weakens to the `(R₀)` clause.
    refine
      { toIsNoetherian := inferInstance
        isRegularLocalRing_localizationAtPrime := ?_ }
    intro p hp0
    exact hR.isRegularLocalRing_localizationAtPrime p (le_trans hp0 (by norm_num))
  · -- Proof comment: the depth lower bound for `(S₂)` weakens from `min (2, dim)` to
    -- `min (1, dim)` on the self-module.
    refine
      { toIsNoetherian := inferInstance
        toSerreConditionS := ?_ }
    refine
      { toFinite := inferInstance
        moduleDepth_localizationAtPrime_ge_min_supportDim := ?_ }
    intro p
    rw [Module.supportDim_self_eq_ringKrullDim]
    have hdepth := SerreConditionS.moduleDepth_localizationAtPrime_ge_min (R := A) hS p
    exact le_trans (min_le_min (by norm_num) le_rfl) hdepth

/-- Helper for Lemma 10.163.8: a normal Noetherian ring satisfies Serre's conditions `(R₁)` and
`(S₂)`. -/
lemma normal_serre_conditions
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsNormalRing A] :
    A ⊧ (R₁) ∧ A ⊧ (S₂) := by
  -- Proof comment: recover the two Serre conditions separately from the local normal-domain properties.
  exact ⟨normal_ring_serreConditionR_one (A := A), normal_ring_serreConditionS_two (A := A)⟩

/-- Helper for Lemma 10.163.8: a reduced Noetherian ring with `(R₁)` and `(S₂)` is normal. -/
theorem isNormalRing_of_isReduced_serre_conditions
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsReduced A]
    (hR : A ⊧ (R₁)) (hS : A ⊧ (S₂)) :
    IsNormalRing A := by
  -- Route correction: now that the owner-level Serre-criterion file imports cleanly, close this
  -- step exactly as in the source by applying the converse direction of Serre's criterion.
  exact
    (isNormalRing_iff_serreConditionR_one_and_serreConditionS_two (R := A)).2 ⟨hR, hS⟩

/-- Helper for Lemma 10.163.8: the weaker Serre conditions `(R₀)` and `(S₁)` imply reducedness for
a Noetherian ring. -/
theorem isReduced_of_weaker_serre_conditions
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (hR : SerreConditionR A 0) (hS : SerreConditionS A 1) :
    IsReduced A := by
  -- Proof comment: reducedness is local on maximal localizations, so the prime-height induction
  -- above globalizes the reducedness criterion.
  refine isReduced_ofLocalizationMaximal A fun p _ ↦ ?_
  let p' : PrimeSpectrum A := ⟨p, inferInstance⟩
  simpa using
    isReduced_localizationAtPrime_of_serreConditionR_zero_and_serreConditionS_one
      (R := A) hR hS p'

/-- Helper for Lemma 10.163.8: the owner-level Serre conditions suffice for normality after
recovering reducedness from the weaker Serre conditions `(R₀)` and `(S₁)`. -/
theorem isNormalRing_of_serre_conditions
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (hR : A ⊧ (R₁)) (hS : A ⊧ (S₂)) :
    IsNormalRing A := by
  -- Proof comment: first weaken the Serre conditions to `(R₀)` and `(S₁)` in order to invoke the
  -- reducedness criterion from Lemma `10.157.3`.
  have hWeak :
      SerreConditionR A 0 ∧ SerreConditionS A 1 :=
    weaker_serre_conditions_of_serre_conditions hR hS
  have hReduced : IsReduced A :=
    isReduced_of_weaker_serre_conditions hWeak.1 hWeak.2
  let _ : IsReduced A := hReduced
  -- Proof comment: once reducedness is available, the remaining step is the converse direction of
  -- Serre's criterion for normality.
  exact isNormalRing_of_isReduced_serre_conditions hR hS

/- The main proof follows the textbook route exactly: convert normality of the base and the fiber
rings to Serre conditions, apply the flat ascent results for `(R₁)` and `(S₂)`, and then recover
normality from the two ascended conditions. -/
/-- Helper for Lemma 10.163.8: the normal base ring already satisfies the Serre conditions needed
for flat ascent. -/
lemma base_serre_conditions_of_normal :
    R ⊧ (R₁) ∧ R ⊧ (S₂) := by
  -- Proof comment: this is the base specialization of the normal-to-Serre conversion.
  exact normal_serre_conditions (A := R)

/-- Helper for Lemma 10.163.8: each normal fiber ring satisfies the two Serre conditions used in
the flat ascent theorems. -/
lemma fiber_serre_conditions_of_normal
    (p : PrimeSpectrum R) (hp : IsNormalRing (p.asIdeal.Fiber S)) :
    (p.asIdeal.Fiber S) ⊧ (R₁) ∧ (p.asIdeal.Fiber S) ⊧ (S₂) := by
  -- Proof comment: the fiber is Noetherian by the canonical tensor-product presentation, so the
  -- local Serre-criterion placeholder applies directly to the normal fiber ring.
  let _ : Algebra.EssFiniteType S (S ⊗[R] p.asIdeal.ResidueField) := inferInstance
  let _ : IsNoetherianRing (S ⊗[R] p.asIdeal.ResidueField) :=
    Algebra.EssFiniteType.isNoetherianRing S (S ⊗[R] p.asIdeal.ResidueField)
  let _ : IsNoetherianRing (p.asIdeal.Fiber S) :=
    isNoetherianRing_of_ringEquiv (S ⊗[R] p.asIdeal.ResidueField)
      (Algebra.TensorProduct.comm R p.asIdeal.ResidueField S).toRingEquiv.symm
  let _ : IsNormalRing (p.asIdeal.Fiber S) := hp
  exact normal_serre_conditions (A := p.asIdeal.Fiber S)

/-- Helper for Lemma 10.163.8: the fiberwise normality hypothesis gives `(R₁)` on `S` after flat
ascent. -/
lemma target_serreConditionR_of_fiber_normality
    (hfiber : ∀ p : PrimeSpectrum R, IsNormalRing (p.asIdeal.Fiber S)) :
    S ⊧ (R₁) := by
  -- Proof comment: apply Lemma `10.163.5` to the base `(R₁)` condition and the fiberwise `(R₁)`
  -- conditions extracted from normality.
  let _ : R ⊧ (R₁) := (base_serre_conditions_of_normal (R := R)).1
  exact
    serreConditionR_of_flat_of_fiber
      (R := R) (S := S) fun p ↦ (fiber_serre_conditions_of_normal (R := R) (S := S) p (hfiber p)).1

/-- Helper for Lemma 10.163.8: the fiberwise normality hypothesis gives `(S₂)` on `S` after flat
ascent. -/
lemma target_serreConditionS_of_fiber_normality
    (hfiber : ∀ p : PrimeSpectrum R, IsNormalRing (p.asIdeal.Fiber S)) :
    S ⊧ (S₂) := by
  -- Proof comment: apply Lemma `10.163.4` to the base `(S₂)` condition and the fiberwise `(S₂)`
  -- conditions extracted from normality.
  let _ : R ⊧ (S₂) := (base_serre_conditions_of_normal (R := R)).2
  exact
    serreConditionS_of_flat_of_fiber
      (R := R) (S := S) fun p ↦ (fiber_serre_conditions_of_normal (R := R) (S := S) p (hfiber p)).2

-- Proof sketch: by Serre's criterion, it is enough to prove that `S` satisfies `(R_1)` and
-- `(S_2)`. The normality of `R` and of each fiber ring gives these Serre conditions on `R` and on
-- every fiber. Apply Lemmas `10.163.5` and `10.163.4` to ascend `(R_1)` and `(S_2)` along the flat
-- map `R → S`, and conclude that `S` is normal by Serre's criterion again.
/-- Lemma 10.163.8: for a flat ring map `R → S` between Noetherian rings, if `R` is normal and
every fiber ring `κ(𝔭) ⊗[R] S`, formalized as `p.asIdeal.Fiber S`, is normal, then `S` is a
normal ring. -/
@[stacks 0C22]
theorem isNormalRing_of_flat_of_fiber
    (hfiber : ∀ p : PrimeSpectrum R, IsNormalRing (p.asIdeal.Fiber S)) :
    IsNormalRing S := by
  -- Proof comment: first ascend the codimension-one regularity condition `(R₁)` along the flat
  -- map using the base and fiber Serre conditions.
  have hSR : S ⊧ (R₁) :=
    target_serreConditionR_of_fiber_normality (R := R) (S := S) hfiber
  -- Proof comment: next ascend the depth condition `(S₂)` by the sibling flat ascent theorem.
  have hSS : S ⊧ (S₂) :=
    target_serreConditionS_of_fiber_normality (R := R) (S := S) hfiber
  -- Proof comment: the remaining step is the converse direction of Serre's criterion.
  exact isNormalRing_of_serre_conditions (A := S) hSR hSS

end
