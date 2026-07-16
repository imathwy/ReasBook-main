import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_162_1
import stacks_proof.stacks_project.Chap10.Definition_10_162_9
import stacks_proof.stacks_project.Chap10.Definition_10_64_1
import stacks_proof.stacks_project.Chap10.Definition_10_67_1
import stacks_proof.stacks_project.Chap10.Definition_10_37_11
import stacks_proof.stacks_project.Chap10.Lemma_10_61_4
import stacks_proof.stacks_project.Chap10.Lemma_10_63_19
import stacks_proof.stacks_project.Chap10.Lemma_10_64_2
import stacks_proof.stacks_project.Chap10.Lemma_10_65_3
import stacks_proof.stacks_project.Chap10.Lemma_10_65_5
import stacks_proof.stacks_project.Chap10.Lemma_10_97_8
import stacks_proof.stacks_project.Chap10.Lemma_10_112_4
import stacks_proof.stacks_project.Chap10.Lemma_10_60_11
import stacks_proof.stacks_project.Chap10.Lemma_10_72_7
import stacks_proof.stacks_project.Chap10.Lemma_10_157_2
import stacks_proof.stacks_project.Chap10.Lemma_10_161_17
import stacks_proof.stacks_project.Chap10.Lemma_10_162_4
import stacks_proof.stacks_project.Chap10.Lemma_10_162_11
import stacks_proof.stacks_project.Chap10.Lemma_10_162_12
import stacks_proof.stacks_project.Chap10.Lemma_10_97_3
import stacks_proof.stacks_project.Chap10.Lemma_10_119_1
import stacks_proof.stacks_project.Chap10.Lemma_10_119_2_Koll_r
import stacks_proof.stacks_project.Chap10.Lemma_10_119_3
import stacks_proof.stacks_project.Chap10.Lemma_10_119_7
import stacks_proof.stacks_project.Chap10.Proposition_10_63_6
import stacks_proof.stacks_project.Chap10.Proposition_10_162_15_Nagata

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open IsLocalRing
open scoped Pointwise TensorProduct

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- Helper for Chap10 Lemma 10 162 13: a Nagata domain is `N-2`. -/
lemma nagataRing_isN2Ring
    {A : Type u} [CommRing A] [IsDomain A] [NagataRing A] : IsN2Ring A := by
  letI : IsN2Ring (A ⧸ (⊥ : Ideal A)) :=
    NagataRing.quotient_isN2Ring (R := A) (p := (⊥ : Ideal A))
  exact isN2Ring_of_ringEquiv (RingEquiv.quotientBot A)

/-- Helper for Chap10 Lemma 10 162 13: finite type algebras over a Nagata ring are Nagata. -/
lemma nagataRing_of_finiteType_from_tfae
    (A : Type u) {S : Type u} [CommRing A] [CommRing S] [Algebra A S]
    [NagataRing A] [Algebra.FiniteType A S] : NagataRing S := by
  have htfae :
      List.TFAE
        [ NagataRing A,
          ∀ (T : Type u) [CommRing T] [Algebra A T] [Algebra.FiniteType A T], NagataRing T,
          UniversallyJapaneseRing.{u, u} A ∧ IsNoetherianRing A ] :=
    nagataRing_tfae_finiteType_algebra_nagata_universallyJapanese_noetherian (R := A)
  let hA : NagataRing A := inferInstance
  let hFiniteType := (htfae.out 0 1).1 hA
  exact hFiniteType S

/-- Helper for Chap10 Lemma 10 162 13: localizations of Nagata rings are Nagata. -/
lemma localization_nagataRing_from_tfae
    {A : Type u} {Aₘ : Type u} [CommRing A] [CommRing Aₘ] [Algebra A Aₘ]
    (M : Submonoid A) [IsLocalization M Aₘ] [NagataRing A] : NagataRing Aₘ := by
  -- Proof comment: the localization is essentially of finite type over the source Nagata ring, so
  -- the TFAE transfers the universally Japanese property and Noetherianity.
  letI : IsNoetherianRing Aₘ := IsLocalization.isNoetherianRing M Aₘ inferInstance
  refine NagataRing.mk ?_
  intro q
  letI : Algebra.EssFiniteType A Aₘ := Algebra.EssFiniteType.of_isLocalization Aₘ M
  let hEssFiniteType : Algebra.EssFiniteType A (Aₘ ⧸ q) := inferInstance
  let hUniversallyJapanese : UniversallyJapaneseRing A :=
    (nagataRing_iff_universallyJapaneseRing_and_isNoetherianRing (R := A)).1 inferInstance |>.1
  letI : Algebra.EssFiniteType A (Aₘ ⧸ q) := hEssFiniteType
  letI : UniversallyJapaneseRing (Aₘ ⧸ q) :=
    @universallyJapaneseRing_of_essFiniteType A (Aₘ ⧸ q) _ _ _ hUniversallyJapanese hEssFiniteType
  exact inferInstance

/-- Helper for Chap10 Lemma 10 162 13: quotients of Nagata rings are Nagata. -/
lemma quotient_nagataRing_of_nagataRing
    {A : Type u} [CommRing A] [NagataRing A] (I : Ideal A) : NagataRing (A ⧸ I) := by
  -- Proof comment: quotient algebras are finite type over the source ring, so the finite-type
  -- Nagata criterion applies directly.
  letI : Algebra.FiniteType A (A ⧸ I) := inferInstance
  exact nagataRing_of_finiteType_from_tfae A

/-- Helper for Chap10 Lemma 10 162 13: a non-field local ring has a nonzero element in its
maximal ideal. -/
lemma exists_nonzero_mem_maximalIdeal_of_not_isField_local
    {A : Type u} [CommRing A] [IsLocalRing A] (hA : ¬ IsField A) :
    ∃ x : A, x ∈ maximalIdeal A ∧ x ≠ 0 := by
  have hmax_ne : maximalIdeal A ≠ ⊥ :=
    IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hA
  exact Submodule.exists_mem_ne_zero_of_ne_bot hmax_ne

/-- Helper for Chap10 Lemma 10 162 13: the field case is analytically unramified. -/
lemma field_isAnalyticallyUnramified_of_isField
    {A : Type u} [CommRing A] [IsLocalRing A] (hA : IsField A) :
    IsAnalyticallyUnramified A := by
  letI : Field A := hA.toField
  infer_instance

/-- Helper for Chap10 Lemma 10 162 13: localizing `QuotSMulTop a R` at `p` agrees with
quotienting the localized ring by the image of `a`. -/
private noncomputable def localizedQuotSMulTopAtPrimeEquiv
    {R : Type u} [CommRing R] (p : PrimeSpectrum R) (a : R) :
    LocalizedModule.AtPrime p.asIdeal (QuotSMulTop a R) ≃ₗ[Localization.AtPrime p.asIdeal]
      QuotSMulTop (algebraMap R (Localization.AtPrime p.asIdeal) a)
        (Localization.AtPrime p.asIdeal) :=
  let e₁ := LocalizedModule.equivTensorProduct (R := R) p.asIdeal.primeCompl (QuotSMulTop a R)
  let e₂ := (QuotSMulTop.algebraMapTensorEquivTensorQuotSMulTop
    (R := R) (r := a) (M := R) (Localization.AtPrime p.asIdeal)).symm
  let e₃ := QuotSMulTop.congr (algebraMap R (Localization.AtPrime p.asIdeal) a)
    (LocalizedModule.equivTensorProduct (R := R) p.asIdeal.primeCompl R).symm
  e₁.trans (e₂.trans e₃)

/-- Helper for Chap10 Lemma 10 162 13: if the principal generator is a unit, its quotient module
is trivial. -/
private lemma quotSMulTopSubsingletonOfIsUnit
    {R : Type u} [CommRing R] {a : R} (ha : IsUnit a) :
    Subsingleton (QuotSMulTop a R) := by
  -- Proof comment: a unit already generates the whole ambient module, so the quotient is
  -- trivial.
  rw [Submodule.Quotient.subsingleton_iff]
  refine top_unique ?_
  intro x hx
  rcases ha with ⟨u, rfl⟩
  rw [Submodule.mem_smul_pointwise_iff_exists]
  refine ⟨(↑u⁻¹ : R) • x, by simp, ?_⟩
  simp

/-- Helper for Chap10 Lemma 10 162 13: a finite subsingleton module over a Noetherian local ring
has infinite depth. -/
private lemma moduleDepthEqTopOfSubsingleton
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M] [Subsingleton M] :
    moduleDepth A M = ⊤ := by
  -- Proof comment: the maximal ideal acts trivially on the unique element, so the depth is top.
  have htop_eq_bot : (⊤ : Submodule A M) = ⊥ := by
    ext x
    simp [Subsingleton.elim x 0]
  have hsmul_bot : maximalIdeal A • (⊥ : Submodule A M) = ⊥ := by
    ext x
    simp
  have hsmul_top : maximalIdeal A • (⊤ : Submodule A M) = ⊤ := by
    rw [htop_eq_bot, hsmul_bot, ← htop_eq_bot]
  change Ideal.depth (maximalIdeal A) M = ⊤
  simpa using Ideal.depth_eq_top_of_smul_top (maximalIdeal A) M hsmul_top

/-- Helper for Chap10 Lemma 10 162 13: a Noetherian normal local domain satisfies the depth lower
bound coming from `(S₂)`. -/
private lemma normalLocalDomainNoExceptionalFiniteExtension
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
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
      exact hxreg.right_eq_zero_of_smul <| by simp [hx0]
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
      simp [ha_zero]
    · intro ha
      have ha_zero : a = 0 := by
        simpa [Submodule.mem_bot] using ha
      simp [ha_zero]
  have hxreg_image : IsSMulRegular T (algebraMap A T x) := by
    -- Proof comment: regular scalar multiplication by `x` transports to regular multiplication
    -- by its image.
    refine IsSMulRegular.of_right_eq_zero_of_smul ?_
    intro t ht
    exact hxreg.right_eq_zero_of_smul <| by simpa [Algebra.smul_def] using ht
  have hAwayInj : Function.Injective (Localization.awayMap η x) := by
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
  have hAwaySurj : Function.Surjective (Localization.awayMap η x) := by
    rw [Localization.awayMap_surjective_iff]
    intro t
    -- Proof comment: the cokernel torsion condition writes a power of `x` times `t` inside the
    -- image.
    have hxt_mem : x ^ n • t ∈ (maximalIdeal A) ^ n • (⊤ : Submodule A T) := by
      exact Submodule.smul_mem_smul (Ideal.pow_mem_pow hx n) (by simp)
    have hxt_range : x ^ n • t ∈ (Algebra.linearMap A T).range := hcokerPow hxt_mem
    rcases hxt_range with ⟨a, ha⟩
    refine ⟨a, n, ?_⟩
    simpa [η, Algebra.smul_def, map_pow] using ha
  let e : Localization.Away x ≃ₐ[A] Localization.Away (η x) :=
    AlgEquiv.ofBijective (Localization.awayMapₐ (Algebra.ofId A T) x) <|
      by
        simpa [Localization.awayMapₐ] using ⟨hAwayInj, hAwaySurj⟩
  have hpow : Submonoid.powers x ≤ nonZeroDivisors A := by
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
  have hTLocInj : Function.Injective (algebraMap T (Localization.Away (η x))) := by
    refine IsLocalization.injective
      (M := Submonoid.powers (η x)) (S := Localization.Away (η x)) ?_
    intro y hy
    rcases
      (show ∃ m : ℕ, (η x) ^ m = y by simpa [Submonoid.mem_powers_iff] using hy) with ⟨m, rfl⟩
    rw [mem_nonZeroDivisors_iff_right]
    intro t ht
    exact (hxreg_image.pow m) <| by simpa [mul_comm] using ht
  have hFracInj : Function.Injective (algebraMap (Localization.Away x) (FractionRing A)) := by
    simpa using (IsFractionRing.injective (Localization.Away x) (FractionRing A))
  have hψinj : Function.Injective ψ := by
    exact hFracInj.comp (e.symm.injective.comp hTLocInj)
  have hηsurj : Function.Surjective η := by
    intro t
    -- Proof comment: every integral element in the fraction field comes from the integrally
    -- closed base.
    have ht_integral : IsIntegral A t := Algebra.IsIntegral.isIntegral t
    have hψt_integral : IsIntegral A (ψ t) := IsIntegral.map ψ ht_integral
    obtain ⟨a, ha⟩ :=
      IsIntegrallyClosed.algebraMap_eq_of_integral (K := FractionRing A) hψt_integral
    refine ⟨a, hψinj ?_⟩
    calc
      ψ (η a) = algebraMap A (FractionRing A) a := by
        dsimp [η]
        exact AlgHom.commutes ψ a
      _ = ψ t := ha
  exact hnotbij ⟨hηinj, hηsurj⟩

/-- Helper for Chap10 Lemma 10 162 13: a Noetherian normal local domain satisfies the depth lower
bound coming from `(S₂)`. -/
private lemma localNormalDomainDepthGeMinTwo
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    [IsIntegrallyClosed A] :
    WithBot.some (moduleDepth A A : ℕ∞) ≥
      min (2 : WithBot ℕ∞) (ringKrullDim A) := by
  -- Proof comment: use the normal local-domain trichotomy by dimension.
  by_cases hdim0 : ringKrullDim A = 0
  · simp [hdim0]
  · by_cases hdim1 : ringKrullDim A = 1
    · have hNormalDimOne :
          ∃ (_ : IsLocalRing A) (_ : IsNoetherianRing A) (_ : IsDomain A)
            (_ : IsIntegrallyClosed A), ringKrullDim A = 1 := by
        exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, hdim1⟩
      have hRegDim : IsRegularLocalRing A ∧ ringKrullDim A = 1 := by
        exact ((discreteValuationRing_tfae (A := A)).out 4 2).mp hNormalDimOne
      letI : IsRegularLocalRing A := hRegDim.1
      have hCM : Module.CohenMacaulay A A := inferInstance
      have hdepth_eq : WithBot.some (moduleDepth A A : ℕ∞) = 1 := by
        simpa [Module.supportDim_self_eq_ringKrullDim, hRegDim.2] using
          hCM.supportDim_eq_moduleDepth.symm
      simp [hdim1, hdepth_eq]
    · have hArtFalse : ¬ IsArtinianRing A := by
        intro hArt
        exact hdim0 <|
          ringKrullDimZero_iff_ringKrullDim_eq_zero.mp
            ((isArtinianRing_iff_krullDimLE_zero).mp hArt)
      have hRegFalse : ¬ (IsRegularLocalRing A ∧ ringKrullDim A = 1) := by
        rintro ⟨_, hdimA⟩
        exact hdim1 hdimA
      have hExceptionalFalse : ¬ HasKollarExceptionalFiniteExtension A :=
        normalLocalDomainNoExceptionalFiniteExtension (A := A) hdim0
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

/-- Helper for Chap10 Lemma 10 162 13: over a Noetherian normal local domain, quotienting by a
nonzero element of the maximal ideal satisfies the local `(S₁)` depth bound. -/
private lemma localPrincipalQuotSMulTopDepthGeMinOne
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    [IsIntegrallyClosed A] {a : A} (ha : a ≠ 0) (ha_mem : a ∈ maximalIdeal A) :
    WithBot.some (moduleDepth A (QuotSMulTop a A) : ℕ∞) ≥
      min (1 : WithBot ℕ∞) (Module.supportDim A (QuotSMulTop a A)) := by
  have hreg : IsSMulRegular A a := IsSMulRegular.of_ne_zero ha
  have hdepth_drop :
      moduleDepth A (QuotSMulTop a A) = moduleDepth A A - 1 :=
    IsSMulRegular.moduleDepth_quotSMulTop_eq_sub_one (R := A) (M := A) hreg ha_mem
  have hsupport_drop :
      Module.supportDim A (QuotSMulTop a A) + 1 = Module.supportDim A A :=
    Module.supportDim_quotSMulTop_succ_eq_supportDim (M := A) hreg ha_mem
  have hdepth_A :
      WithBot.some (moduleDepth A A : ℕ∞) ≥
        min (2 : WithBot ℕ∞) (ringKrullDim A) :=
    localNormalDomainDepthGeMinTwo A
  cases hq : Module.supportDim A (QuotSMulTop a A) with
  | bot =>
      simp
  | coe qdim =>
      by_cases hqdim_zero : qdim = 0
      · simp [hqdim_zero]
      · have hqdim_ge_one : (1 : ℕ∞) ≤ qdim :=
          ENat.one_le_iff_ne_zero.2 hqdim_zero
        have hdim_ge_two : (2 : WithBot ℕ∞) ≤ ringKrullDim A := by
          have hqdim_succ : (2 : ℕ∞) ≤ qdim + 1 := by
            calc
              (2 : ℕ∞) = 1 + 1 := by norm_num
              _ ≤ qdim + 1 := by
                simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hqdim_ge_one 1
          calc
            (2 : WithBot ℕ∞) ≤ (((qdim + 1 : ℕ∞) : WithBot ℕ∞)) := by
              exact WithBot.coe_le_coe.2 hqdim_succ
            _ = ringKrullDim A := by
              simpa [hq, Module.supportDim_self_eq_ringKrullDim] using hsupport_drop
        have hdepth_A_ge_two : (2 : WithBot ℕ∞) ≤ WithBot.some (moduleDepth A A : ℕ∞) := by
          simpa [min_eq_left hdim_ge_two] using hdepth_A
        have hdepth_A_ge_two' : (2 : ℕ∞) ≤ moduleDepth A A := by
          exact WithBot.coe_le_coe.mp (by simpa [WithBot.some_eq_coe] using hdepth_A_ge_two)
        have hdepth_quot_ne_zero : moduleDepth A (QuotSMulTop a A) ≠ 0 := by
          intro hzero
          have hdepth_A_le_one : moduleDepth A A ≤ 1 := by
            have htsub_zero : moduleDepth A A - 1 = 0 := by
              simpa [hdepth_drop] using hzero
            exact (tsub_eq_zero_iff_le).1 htsub_zero
          have : (2 : ℕ∞) ≤ 1 := le_trans hdepth_A_ge_two' hdepth_A_le_one
          norm_num at this
        have hdepth_quot_ge_one : (1 : ℕ∞) ≤ moduleDepth A (QuotSMulTop a A) :=
          ENat.one_le_iff_ne_zero.2 hdepth_quot_ne_zero
        have hdepth_quot_ge_one' :
            (1 : WithBot ℕ∞) ≤ WithBot.some (moduleDepth A (QuotSMulTop a A) : ℕ∞) := by
          simpa [WithBot.some_eq_coe] using hdepth_quot_ge_one
        have hmin_eq :
            min (1 : WithBot ℕ∞) ((qdim : ℕ∞) : WithBot ℕ∞) = 1 := by
          exact min_eq_left (WithBot.coe_le_coe.2 hqdim_ge_one)
        simpa [hq, hmin_eq] using hdepth_quot_ge_one'

/-- Helper for Chap10 Lemma 10 162 13: the principal quotient `R / aR` satisfies `(S₁)` when
`a ≠ 0` in a Noetherian normal local domain. -/
private lemma quotSMulTopSubmoduleEqPrincipalIdeal
    {A : Type u} [CommRing A] (a : A) :
    a • (⊤ : Submodule A A) = Ideal.span ({a} : Set A) := by
  -- Proof comment: scalar multiplication of the self-module by `a` is the principal ideal `(a)`.
  simp [← Submodule.ideal_span_singleton_smul]

/-- Helper for Chap10 Lemma 10 162 13: the self-module quotient `A / aA` agrees with the usual
principal ring quotient. -/
private noncomputable def quotSMulTopToPrincipalQuotientLinearEquiv
    {A : Type u} [CommRing A] (a : A) :
    QuotSMulTop a A ≃ₗ[A] A ⧸ Ideal.span ({a} : Set A) :=
  Submodule.quotEquivOfEq (a • (⊤ : Submodule A A)) (Ideal.span ({a} : Set A))
    (quotSMulTopSubmoduleEqPrincipalIdeal (A := A) a)

/-- Helper for Chap10 Lemma 10 162 13: the principal quotient `R / aR` satisfies `(S₁)` when
`a ≠ 0` in a Noetherian normal local domain. -/
private lemma quotientSpanSingletonSerreConditionSOneOfNonzero
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]
    [IsIntegrallyClosed R] {a : R} (ha : a ≠ 0) :
    Module.SerreConditionS R (R ⧸ Ideal.span ({a} : Set R)) 1 := by
  have hquot : Module.SerreConditionS R (QuotSMulTop a R) 1 := by
    refine
      { toFinite := inferInstance
        moduleDepth_localizationAtPrime_ge_min_supportDim := ?_ }
    intro p
    let A := Localization.AtPrime p.asIdeal
    let e := localizedQuotSMulTopAtPrimeEquiv (R := R) p a
    by_cases ha_mem : a ∈ p.asIdeal
    · have ha_loc : algebraMap R A a ∈ maximalIdeal A := by
        exact (IsLocalization.AtPrime.to_map_mem_maximal_iff A p.asIdeal a).2 ha_mem
      letI : IsDomain A := isDomain_localizationAtPrime p
      letI : IsIntegrallyClosed A := isIntegrallyClosed_localizationAtPrime p
      have hlocal :
          WithBot.some
              (moduleDepth A (QuotSMulTop (algebraMap R A a) A) : ℕ∞) ≥
            min (1 : WithBot ℕ∞)
              (Module.supportDim A (QuotSMulTop (algebraMap R A a) A)) :=
        localPrincipalQuotSMulTopDepthGeMinOne A
          (show algebraMap R A a ≠ 0 by
            intro hzero
            apply ha
            apply (IsLocalization.injective A p.asIdeal.primeCompl_le_nonZeroDivisors)
            simpa using hzero)
          ha_loc
      have hdepth_eq :
          moduleDepth A (LocalizedModule.AtPrime p.asIdeal (QuotSMulTop a R)) =
            moduleDepth A (QuotSMulTop (algebraMap R A a) A) := by
        simpa [A] using moduleDepth_eq_of_equiv (R := A) (e := e)
      have hsupport_eq :
          Module.supportDim A (LocalizedModule.AtPrime p.asIdeal (QuotSMulTop a R)) =
            Module.supportDim A (QuotSMulTop (algebraMap R A a) A) := by
        simpa [A] using Module.supportDim_eq_of_equiv e
      rw [hdepth_eq, hsupport_eq]
      exact hlocal
    · have ha_loc_not_mem : algebraMap R A a ∉ maximalIdeal A := by
        intro ha_loc
        exact ha_mem ((IsLocalization.AtPrime.to_map_mem_maximal_iff A p.asIdeal a).1 ha_loc)
      have ha_unit : IsUnit (algebraMap R A a) := by
        simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Classical.not_not] using
          ha_loc_not_mem
      letI : Subsingleton (QuotSMulTop (algebraMap R A a) A) :=
        quotSMulTopSubsingletonOfIsUnit (R := A) ha_unit
      letI : Subsingleton (LocalizedModule.AtPrime p.asIdeal (QuotSMulTop a R)) :=
        e.injective.subsingleton
      have hdepth :
          moduleDepth A (LocalizedModule.AtPrime p.asIdeal (QuotSMulTop a R)) = ⊤ := by
        exact moduleDepthEqTopOfSubsingleton (A := A)
      have hsupport :
          Module.supportDim A (LocalizedModule.AtPrime p.asIdeal (QuotSMulTop a R)) = ⊥ := by
        exact Module.supportDim_eq_bot_of_subsingleton (R := A)
          (M := LocalizedModule.AtPrime p.asIdeal (QuotSMulTop a R))
      rw [hdepth, hsupport]
      simp
  let ePrincipal : QuotSMulTop a R ≃ₗ[R] (R ⧸ Ideal.span ({a} : Set R)) :=
    quotSMulTopToPrincipalQuotientLinearEquiv a
  letI : Module.SerreConditionS R (QuotSMulTop a R) 1 := hquot
  exact Module.SerreConditionS.of_linearEquiv ePrincipal

/-- Helper for Chap10 Lemma 10 162 13: in a Noetherian normal local domain, a nonzero principal
quotient has no embedded primes and all associated primes have height `1`. -/
private theorem principalQuotientNoEmbeddedAndAssociatedPrimesHeightEqOne
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]
    [IsIntegrallyClosed R] {a : R} (ha : a ≠ 0) :
    embeddedAssociatedPrimes R (R ⧸ Ideal.span ({a} : Set R)) = ∅ ∧
      ∀ p ∈ associatedPrimes R (R ⧸ Ideal.span ({a} : Set R)), p.height = 1 := by
  have hS1 : Module.SerreConditionS R (R ⧸ Ideal.span ({a} : Set R)) 1 :=
    quotientSpanSingletonSerreConditionSOneOfNonzero (R := R) ha
  have hno_embedded :
      embeddedAssociatedPrimes R (R ⧸ Ideal.span ({a} : Set R)) = ∅ :=
    (Module.embeddedAssociatedPrimes_eq_empty_iff_serreConditionS_one
      (R := R) (M := R ⧸ Ideal.span ({a} : Set R))).2 hS1
  refine ⟨hno_embedded, ?_⟩
  intro p hp
  let pPoint : PrimeSpectrum R := ⟨p, hp.1⟩
  have hpAssoc : IsAssociatedPrime pPoint.asIdeal (R ⧸ Ideal.span ({a} : Set R)) := by
    simpa [pPoint] using hp
  have hpMin :
      p ∈ (Ideal.span ({a} : Set R)).minimalPrimes :=
    associatedPrime_quotient_mem_minimalPrimes_span_singleton
      (R := R) (x := a) hno_embedded pPoint hpAssoc
  letI : p.IsPrime := hp.1
  have hprimeHeight : p.primeHeight = 1 :=
    primeHeight_eq_one_of_mem_minimalPrimes_span_singleton_of_nonzero
      (x := a) ha p hpMin
  simpa [Ideal.height_eq_primeHeight] using hprimeHeight

/-- Helper for Chap10 Lemma 10 162 13: in a local ring, every element outside the maximal ideal
is a unit. -/
private lemma primeComplLeIsUnitSubmonoidOfLocal
    (A : Type u) [CommRing A] [IsLocalRing A] :
    (maximalIdeal A).primeCompl ≤ IsUnit.submonoid A := by
  -- Proof comment: the complement of the maximal ideal is exactly the unit group in a local ring.
  intro x hx
  simpa [Ideal.mem_primeCompl_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Classical.not_not] using hx

/-- Helper for Chap10 Lemma 10 162 13: a local ring is canonically the localization at the
complement of its maximal ideal. -/
private noncomputable def localizationAtMaximalRingEquiv
    (A : Type u) [CommRing A] [IsLocalRing A] :
    Localization.AtPrime (maximalIdeal A) ≃ₐ[A] A :=
  letI : IsLocalization (maximalIdeal A).primeCompl A :=
    IsLocalization.self (primeComplLeIsUnitSubmonoidOfLocal A)
  IsLocalization.algEquiv (maximalIdeal A).primeCompl
    (Localization.AtPrime (maximalIdeal A)) A

/-- Helper for Chap10 Lemma 10 162 13: the normalization map into
`integralClosure A (FractionRing A)` is injective. -/
lemma integralClosure_algebraMap_injective
    {A : Type u} [CommRing A] [IsDomain A] :
    Function.Injective (algebraMap A (integralClosure A (FractionRing A))) := by
  intro x y hxy
  apply IsFractionRing.injective A (FractionRing A)
  simpa using
    congrArg (fun z : integralClosure A (FractionRing A) => (z : FractionRing A)) hxy

/-- Helper for Chap10 Lemma 10 162 13: prime localizations do not increase Krull dimension. -/
lemma ringKrullDim_localizationAtPrime_le_ringKrullDim
    {A : Type u} [CommRing A] (I : Ideal A) [I.IsPrime] :
    ringKrullDim (Localization.AtPrime I) ≤ ringKrullDim A := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height I (Localization.AtPrime I)]
  exact Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'

/-- Helper for Chap10 Lemma 10 162 13: products of reduced rings are reduced. -/
lemma isReduced_pi_of_forall
    {ι : Type*} {A : ι → Type*} [∀ i, CommRing (A i)]
    (hA : ∀ i, IsReduced (A i)) :
    IsReduced (∀ i, A i) := by
  constructor
  intro x hx
  funext i
  letI : IsReduced (A i) := hA i
  exact IsReduced.eq_zero (x i) (hx.map (Pi.evalRingHom A i))

/-- Helper for Chap10 Lemma 10 162 13: tensoring the completion with an injective algebra map
preserves injectivity on the completion side. -/
lemma completionTensor_injective_of_algebraMap_injective
    {A : Type u} {S : Type u} [CommRing A] [CommRing S] [Algebra A S]
    [IsLocalRing A] [IsNoetherianRing A]
    (hinj : Function.Injective (algebraMap A S)) :
    Function.Injective
      (algebraMap (AdicCompletion (maximalIdeal A) A)
        ((AdicCompletion (maximalIdeal A) A) ⊗[A] S)) := by
  let C := AdicCompletion (maximalIdeal A) A
  letI : Module.Flat A C := inferInstance
  simpa [C] using
    (Algebra.TensorProduct.includeLeft_injective
      (R := A) (S := C) (A := C) (B := S) hinj)

/-- Helper for Chap10 Lemma 10 162 13: reducedness of the completed tensor product descends to
analytic unramifiedness of the base. -/
lemma isAnalyticallyUnramified_of_reduced_completionTensor
    {A : Type u} {S : Type u} [CommRing A] [CommRing S] [Algebra A S]
    [IsLocalRing A] [IsNoetherianRing A]
    (hinj : Function.Injective (algebraMap A S))
    (hred : IsReduced ((AdicCompletion (maximalIdeal A) A) ⊗[A] S)) :
    IsAnalyticallyUnramified A := by
  let C := AdicCompletion (maximalIdeal A) A
  letI : IsReduced (C ⊗[A] S) := hred
  have hinjC :
      Function.Injective (algebraMap C (C ⊗[A] S)) := by
    simpa [C] using
      completionTensor_injective_of_algebraMap_injective (A := A) (S := S) hinj
  exact ⟨isReduced_of_injective (algebraMap C (C ⊗[A] S)) hinjC⟩

/-- Helper for Chap10 Lemma 10 162 13: the zero locus of a prime ideal is the upper interval
above that prime. -/
lemma primeSpectrum_zeroLocus_prime_eq_Ici_local
    {A : Type u} [CommRing A] {p : Ideal A} (hp : p.IsPrime) :
    PrimeSpectrum.zeroLocus (R := A) p = Set.Ici ⟨p, hp⟩ := by
  ext q
  change p ≤ q.asIdeal ↔ (⟨p, hp⟩ : PrimeSpectrum A) ≤ q
  rfl

/-- Helper for Chap10 Lemma 10 162 13: quotienting by a nonzero prime strictly lowers Krull
dimension in a local domain. -/
lemma primeQuotient_ringKrullDim_lt_of_neBot
    {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]
    (p : PrimeSpectrum A) (hp : p.asIdeal ≠ ⊥) :
    ringKrullDim (A ⧸ p.asIdeal) < ringKrullDim A := by
  let p0 : PrimeSpectrum A := ⟨(⊥ : Ideal A), Ideal.isPrime_bot⟩
  have hp0 : p0 < p := by
    change (⊥ : Ideal A) < p.asIdeal
    exact bot_lt_iff_ne_bot.mpr hp
  have hpFinite : Order.coheight p < ⊤ := by
    obtain ⟨n, hn⟩ := exists_nat_ringKrullDim_of_local_noetherian_ring (A := A)
    have hpLe : ((Order.coheight p : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim A :=
      Order.coheight_le_krullDim p
    have hnatTop : ((n : ℕ∞) : WithBot ℕ∞) < ((⊤ : ℕ∞) : WithBot ℕ∞) := by
      exact_mod_cast (show (n : ℕ∞) < ⊤ from by simp)
    have hpLt : ((Order.coheight p : ℕ∞) : WithBot ℕ∞) < ((⊤ : ℕ∞) : WithBot ℕ∞) :=
      lt_of_le_of_lt hpLe (by simpa [hn] using hnatTop)
    exact WithBot.coe_lt_coe.mp hpLt
  have hpQuot :
      ringKrullDim (A ⧸ p.asIdeal) = (Order.coheight p : WithBot ℕ∞) := by
    rw [ringKrullDim_quotient,
      primeSpectrum_zeroLocus_prime_eq_Ici_local (A := A) (p := p.asIdeal) p.isPrime]
    exact (Order.coheight_eq_krullDim_Ici p).symm
  have hp0Quot :
      ringKrullDim A = (Order.coheight p0 : WithBot ℕ∞) := by
    calc
      ringKrullDim A = ringKrullDim (A ⧸ p0.asIdeal) := by
        symm
        simpa [p0] using
          ringKrullDim_eq_of_ringEquiv
            (RingEquiv.quotientBot A : A ⧸ (⊥ : Ideal A) ≃+* A)
      _ = (Order.coheight p0 : WithBot ℕ∞) := by
        rw [ringKrullDim_quotient,
          primeSpectrum_zeroLocus_prime_eq_Ici_local (A := A) (p := p0.asIdeal) p0.isPrime]
        exact (Order.coheight_eq_krullDim_Ici p0).symm
  calc
    ringKrullDim (A ⧸ p.asIdeal) = (Order.coheight p : WithBot ℕ∞) := hpQuot
    _ < (Order.coheight p0 : WithBot ℕ∞) := by
      exact WithBot.coe_lt_coe.mpr (Order.coheight_strictAnti hp0 hpFinite)
    _ = ringKrullDim A := hp0Quot.symm

/-- Helper for Chap10 Lemma 10 162 13: an associated prime of `A / xA` is nonzero when `x ≠ 0`.
-/
lemma associatedPrimeQuotient_neBot_of_nonzero
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    {x : A} (hx0 : x ≠ 0)
    (p : PrimeSpectrum A)
    (hp : IsAssociatedPrime p.asIdeal (A ⧸ Ideal.span ({x} : Set A))) :
    p.asIdeal ≠ ⊥ := by
  -- Proof comment: convert the associated-prime witness to support membership, then read support
  -- of the principal quotient as containment of `(x)`.
  have hp_support : p ∈ Module.support A (A ⧸ Ideal.span ({x} : Set A)) := by
    simpa using IsAssociatedPrime.mem_support hp
  have hspan_le : Ideal.span ({x} : Set A) ≤ p.asIdeal :=
    (support_quotient_span_singleton_le_iff (R := A) (x := x) p).1 hp_support
  have hx_mem : x ∈ p.asIdeal :=
    hspan_le (Ideal.subset_span (Set.mem_singleton x))
  intro hbot
  have hx_bot : x ∈ (⊥ : Ideal A) := by
    simpa [hbot] using hx_mem
  exact hx0 (Ideal.mem_bot.mp hx_bot)

/-- Helper for Chap10 Lemma 10 162 13: an associated prime quotient has strictly smaller
maximal-ideal height. -/
lemma associatedPrimeQuotient_maximalIdealPrimeHeight_lt_of_nonzero_mem_maximalIdeal
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    {x : A} (_hx : x ∈ maximalIdeal A) (hx0 : x ≠ 0)
    (p : PrimeSpectrum A)
    (hp : IsAssociatedPrime p.asIdeal (A ⧸ Ideal.span ({x} : Set A))) :
    (maximalIdeal (A ⧸ p.asIdeal)).primeHeight < (maximalIdeal A).primeHeight := by
  have hp_ne : p.asIdeal ≠ ⊥ :=
    associatedPrimeQuotient_neBot_of_nonzero hx0 p hp
  have hdim : ringKrullDim (A ⧸ p.asIdeal) < ringKrullDim A :=
    primeQuotient_ringKrullDim_lt_of_neBot p hp_ne
  have hdim' :
      ((maximalIdeal (A ⧸ p.asIdeal)).primeHeight : WithBot ℕ∞) <
        ((maximalIdeal A).primeHeight : WithBot ℕ∞) := by
    simpa [IsLocalRing.maximalIdeal_primeHeight_eq_ringKrullDim] using hdim
  exact WithBot.coe_lt_coe.mp hdim'

/-- Helper for Chap10 Lemma 10 162 13: a height-one prime localization of a Noetherian normal
local domain is regular. -/
lemma normalLocalizationAtPrime_regular_of_height_eq_one
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    [IsIntegrallyClosed A]
    (p : PrimeSpectrum A) (hheight : p.asIdeal.height = 1) :
    IsRegularLocalRing (Localization.AtPrime p.asIdeal) := by
  -- Proof comment: identify the localization as a one-dimensional normal local domain and apply
  -- the `10.119.7` DVR/regular-local equivalence.
  have hheight' : (((p.asIdeal.height : ℕ∞) : WithBot ℕ∞) = 1) := by
    exact_mod_cast hheight
  have hdim : ringKrullDim (Localization.AtPrime p.asIdeal) = 1 := by
    calc
      ringKrullDim (Localization.AtPrime p.asIdeal) =
          (((p.asIdeal.height : ℕ∞) : WithBot ℕ∞)) :=
        IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal
          (Localization.AtPrime p.asIdeal)
      _ = 1 := hheight'
  have hNormalDimOne :
      ∃ (_ : IsLocalRing (Localization.AtPrime p.asIdeal))
        (_ : IsNoetherianRing (Localization.AtPrime p.asIdeal))
        (_ : IsDomain (Localization.AtPrime p.asIdeal))
        (_ : IsIntegrallyClosed (Localization.AtPrime p.asIdeal)),
          ringKrullDim (Localization.AtPrime p.asIdeal) = 1 := by
    exact ⟨inferInstance, inferInstance, inferInstance,
      isIntegrallyClosed_localizationAtPrime p, hdim⟩
  have hRegDim :
      IsRegularLocalRing (Localization.AtPrime p.asIdeal) ∧
        ringKrullDim (Localization.AtPrime p.asIdeal) = 1 := by
    exact
      ((discreteValuationRing_tfae (A := Localization.AtPrime p.asIdeal)).out 4 2).mp
        hNormalDimOne
  exact hRegDim.1

/-- Helper for Chap10 Lemma 10 162 13: a normal local domain is analytically unramified once all
strictly smaller nonzero prime quotients are. -/
lemma normalLocalDomain_isAnalyticallyUnramified_of_smaller_prime_quotients
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    [IsIntegrallyClosed A]
    (hsmaller :
      ∀ p : PrimeSpectrum A,
        p.asIdeal ≠ ⊥ →
          (maximalIdeal (A ⧸ p.asIdeal)).primeHeight < (maximalIdeal A).primeHeight →
            IsAnalyticallyUnramified (A ⧸ p.asIdeal)) :
    IsAnalyticallyUnramified A := by
  by_cases hfieldA : IsField A
  · -- Proof comment: the completion of a field is the field itself, so the field case is
    -- immediate.
    exact field_isAnalyticallyUnramified_of_isField hfieldA
  · obtain ⟨x, hx, hx0⟩ :=
      exists_nonzero_mem_maximalIdeal_of_not_isField_local hfieldA
    obtain ⟨hnoEmbedded, hheightOne⟩ :=
      principalQuotientNoEmbeddedAndAssociatedPrimesHeightEqOne
        (R := A) hx0
    -- Route correction: now that the principal-quotient package is imported, follow the source
    -- proof through Lemma `10.162.12` instead of leaving the normal-local step as a stub.
    refine
      isAnalyticallyUnramified_of_nonzero_in_maximalIdeal_of_associatedPrimes_quotient_regular
        (R := A) (x := x) hx hx0 hnoEmbedded ?_ ?_
    · intro p hp
      -- Proof comment: associated primes of `A / xA` have height one, so their localizations are
      -- one-dimensional normal local domains and hence regular.
      have hheight : p.asIdeal.height = 1 := by
        exact hheightOne p.asIdeal (by simpa using hp)
      exact normalLocalizationAtPrime_regular_of_height_eq_one (A := A) p hheight
    · intro p hp
      -- Proof comment: feed the smaller prime quotient hypothesis into the analytic branch of
      -- Lemma `10.162.12`.
      have hp_ne : p.asIdeal ≠ ⊥ :=
        associatedPrimeQuotient_neBot_of_nonzero hx0 p hp
      have hp_lt :
          (maximalIdeal (A ⧸ p.asIdeal)).primeHeight < (maximalIdeal A).primeHeight :=
        associatedPrimeQuotient_maximalIdealPrimeHeight_lt_of_nonzero_mem_maximalIdeal
          hx hx0 p hp
      simpa [PrimeSpectrum.IsAnalyticallyUnramified] using hsmaller p hp_ne hp_lt

/-- Helper for Chap10 Lemma 10 162 13: a smaller nonzero prime quotient of a localization of the
normalization is analytically unramified by the outer induction. -/
lemma normalizationLocalFactorSmallerPrimeQuotient_isAnalyticallyUnramified
    {B : Type u} [CommRing B] [IsLocalRing B] [IsDomain B] [NagataRing B]
    {n : ℕ}
    (ih :
      ∀ m < n,
        ∀ {C : Type u} [CommRing C] [IsLocalRing C] [IsDomain C] [NagataRing C],
          ringKrullDim C = m → IsAnalyticallyUnramified C)
    (hdimB : ringKrullDim B = n)
    (q : (maximalIdeal B).primesOver (integralClosure B (FractionRing B)))
    {T : Type u} [CommRing T] [Algebra (integralClosure B (FractionRing B)) T]
    [IsLocalization q.1.primeCompl T] [IsLocalRing T]
    (p : PrimeSpectrum T)
    (hp_ne : p.asIdeal ≠ ⊥)
    (_hp_lt :
      (maximalIdeal (T ⧸ p.asIdeal)).primeHeight <
        (maximalIdeal T).primeHeight) :
    IsAnalyticallyUnramified (T ⧸ p.asIdeal) := by
  let K := FractionRing B
  let S := integralClosure B K
  let qSpec : PrimeSpectrum S := ⟨q.1, inferInstance⟩
  letI : IsFractionRing S K :=
    integralClosure.isFractionRing_of_finite_extension (A := B) (K := K) (L := K)
  letI : IsDomain S := inferInstance
  have hfiniteS : Module.Finite B S := by
    -- Proof comment: the normalization is finite over a Nagata domain by the `N-2` criterion.
    letI : IsN2Ring B := nagataRing_isN2Ring (A := B)
    exact IsN2Ring.integralClosure_finite_of_finiteDimensional (R := B) (L := K)
  letI : Module.Finite B S := hfiniteS
  letI : NagataRing S := nagataRing_of_finiteType_from_tfae B
  letI : NagataRing T := localization_nagataRing_from_tfae q.1.primeCompl
  letI : IsDomain T := IsLocalization.isDomain_of_atPrime T qSpec.asIdeal
  letI : IsLocalRing (T ⧸ p.asIdeal) := primeSpectrum_quotient_isLocalRing p
  letI : NagataRing (T ⧸ p.asIdeal) := quotient_nagataRing_of_nagataRing p.asIdeal
  have hdimBS : ringKrullDim B = ringKrullDim S :=
    ringKrullDim_eq_of_injective_algebraMap_of_isIntegral
      (integralClosure_algebraMap_injective (A := B))
  have hdimT_le_n : ringKrullDim T ≤ n := by
    -- Proof comment: localizing the normalization cannot increase dimension, and the
    -- normalization preserves the dimension of the Nagata domain.
    calc
      ringKrullDim T = (((qSpec.asIdeal.height : ℕ∞) : WithBot ℕ∞)) :=
        IsLocalization.AtPrime.ringKrullDim_eq_height qSpec.asIdeal T
      _ ≤ ringKrullDim S :=
        Ideal.height_le_ringKrullDim_of_ne_top qSpec.isPrime.ne_top
      _ = ringKrullDim B := hdimBS.symm
      _ = n := hdimB
  have hdimQuot_lt_n : ringKrullDim (T ⧸ p.asIdeal) < n := by
    exact
      lt_of_lt_of_le
        (primeQuotient_ringKrullDim_lt_of_neBot (A := T) p hp_ne)
        hdimT_le_n
  obtain ⟨m, hm⟩ := exists_nat_ringKrullDim_of_local_noetherian_ring (A := T ⧸ p.asIdeal)
  have hm_lt_n : m < n := by
    have hm_lt_n' : ((m : ℕ∞) : WithBot ℕ∞) < n := by
      simpa [hm] using hdimQuot_lt_n
    exact ENat.coe_lt_coe.mp (WithBot.coe_lt_coe.mp hm_lt_n')
  exact ih m hm_lt_n (C := T ⧸ p.asIdeal) hm

/-- Helper for Chap10 Lemma 10 162 13: each maximal localization of the normalization is
analytically unramified. -/
lemma normalizationLocalFactor_isAnalyticallyUnramified
    {B : Type u} [CommRing B] [IsLocalRing B] [IsDomain B] [NagataRing B]
    {n : ℕ}
    (ih :
      ∀ m < n,
        ∀ {C : Type u} [CommRing C] [IsLocalRing C] [IsDomain C] [NagataRing C],
          ringKrullDim C = m → IsAnalyticallyUnramified C)
    (hdimB : ringKrullDim B = n)
    (q : (maximalIdeal B).primesOver (integralClosure B (FractionRing B))) :
    IsAnalyticallyUnramified (Localization.AtPrime q.1) := by
  let K := FractionRing B
  let S := integralClosure B K
  let qSpec : PrimeSpectrum S := ⟨q.1, inferInstance⟩
  let T := Localization.AtPrime qSpec.asIdeal
  letI : IsFractionRing S K :=
    integralClosure.isFractionRing_of_finite_extension (A := B) (K := K) (L := K)
  letI : IsDomain S := inferInstance
  letI : IsIntegrallyClosed S := by
    exact (isIntegrallyClosed_iff_isIntegrallyClosedIn (R := S) (K := K)).2 inferInstance
  letI : IsNormalRing S := inferInstance
  have hfiniteS : Module.Finite B S := by
    -- Proof comment: as above, the normalization is finite over the Nagata domain.
    letI : IsN2Ring B := nagataRing_isN2Ring (A := B)
    exact IsN2Ring.integralClosure_finite_of_finiteDimensional (R := B) (L := K)
  letI : Module.Finite B S := hfiniteS
  letI : NagataRing S := nagataRing_of_finiteType_from_tfae B
  letI : NagataRing T := localization_nagataRing_from_tfae q.1.primeCompl
  letI : IsDomain T := IsLocalization.isDomain_of_atPrime T qSpec.asIdeal
  letI : IsIntegrallyClosed T := isIntegrallyClosed_localizationAtPrime qSpec
  exact
    normalLocalDomain_isAnalyticallyUnramified_of_smaller_prime_quotients
      (A := T) fun p hp_ne hp_lt ↦
        normalizationLocalFactorSmallerPrimeQuotient_isAnalyticallyUnramified
          ih hdimB q p hp_ne hp_lt

/-- Helper for Chap10 Lemma 10 162 13: a ring equivalence of local rings is a local
homomorphism. -/
private theorem ringEquiv_isLocalHom_of_localRings
    {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    IsLocalHom e.toRingHom := by
  -- Proof comment: a surjective map between local rings is local, and ring equivalences are
  -- automatically surjective.
  exact Function.Surjective.isLocalHom _ e.surjective

/-- Helper for Chap10 Lemma 10 162 13: a local-ring equivalence sends the maximal ideal onto the
target maximal ideal. -/
private theorem ringEquiv_map_maximalIdeal_eq_of_localRings
    {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    Ideal.map e.toRingHom (maximalIdeal A) = maximalIdeal B := by
  letI : IsLocalHom e.toRingHom := ringEquiv_isLocalHom_of_localRings e
  -- Proof comment: surjectivity identifies the image of the unique maximal ideal with the target
  -- maximal ideal.
  simpa using IsLocalRing.map_maximalIdeal_of_surjective e.toRingHom e.surjective

/-- Helper for Chap10 Lemma 10 162 13: a local-ring equivalence sends source maximal-ideal powers
into the corresponding target maximal-ideal powers. -/
private theorem ringEquiv_pow_maximalIdeal_le_comap_pow_maximalIdeal
    {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) (n : ℕ) :
    maximalIdeal A ^ n ≤ Ideal.comap e.toRingHom (maximalIdeal B ^ n) := by
  letI : IsLocalHom e.toRingHom := ringEquiv_isLocalHom_of_localRings e
  -- Proof comment: this is the standard maximal-ideal power containment for local
  -- homomorphisms.
  simpa using pow_maximalIdeal_le_comap_pow_maximalIdeal e.toRingHom n

/-- Helper for Chap10 Lemma 10 162 13: contracting a target maximal-ideal power along a
local-ring equivalence recovers the corresponding source maximal-ideal power. -/
private theorem ringEquiv_comap_maximalIdeal_pow_eq
    {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) (n : ℕ) :
    Ideal.comap e.toRingHom (maximalIdeal B ^ n) = maximalIdeal A ^ n := by
  have hker : Ideal.comap e.toRingHom (⊥ : Ideal B) = ⊥ := by
    ext x
    simp [Ideal.mem_comap]
  have hmap :
      Ideal.map e.toRingHom (maximalIdeal A ^ n) = maximalIdeal B ^ n := by
    calc
      Ideal.map e.toRingHom (maximalIdeal A ^ n) =
          Ideal.map e.toRingHom (maximalIdeal A) ^ n := by
            rw [Ideal.map_pow]
      _ = maximalIdeal B ^ n := by
            rw [ringEquiv_map_maximalIdeal_eq_of_localRings e]
  -- Proof comment: surjectivity identifies contraction after extension with the original ideal.
  calc
    Ideal.comap e.toRingHom (maximalIdeal B ^ n) =
        Ideal.comap e.toRingHom (Ideal.map e.toRingHom (maximalIdeal A ^ n)) := by
          rw [hmap]
    _ = maximalIdeal A ^ n ⊔ Ideal.comap e.toRingHom (⊥ : Ideal B) := by
          exact Ideal.comap_map_of_surjective e.toRingHom e.surjective (maximalIdeal A ^ n)
    _ = maximalIdeal A ^ n := by rw [hker, sup_bot_eq]

/-- Helper for Chap10 Lemma 10 162 13: a local-ring equivalence induces a bijection on the
quotients by maximal-ideal powers. -/
private theorem ringEquiv_quotient_maximalIdeal_pow_bijective
    {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) (n : ℕ) :
    Function.Bijective
      (Ideal.quotientMap (maximalIdeal B ^ n) e.toRingHom
        (ringEquiv_pow_maximalIdeal_le_comap_pow_maximalIdeal e n)) := by
  let qPow :
      A ⧸ Ideal.comap e.toRingHom (maximalIdeal B ^ n) →+* B ⧸ maximalIdeal B ^ n :=
    Ideal.quotientMap (maximalIdeal B ^ n) e.toRingHom le_rfl
  let eSource :
      A ⧸ Ideal.comap e.toRingHom (maximalIdeal B ^ n) ≃+* A ⧸ maximalIdeal A ^ n :=
    Ideal.quotEquivOfEq (ringEquiv_comap_maximalIdeal_pow_eq e n)
  have hEq :
      Ideal.quotientMap (maximalIdeal B ^ n) e.toRingHom
          (ringEquiv_pow_maximalIdeal_le_comap_pow_maximalIdeal e n) =
        qPow.comp eSource.symm.toRingHom := by
    apply Ideal.Quotient.ringHom_ext
    ext x
    have hs :
        eSource.symm ((Ideal.Quotient.mk (maximalIdeal A ^ n)) x) =
          Ideal.Quotient.mk (Ideal.comap e.toRingHom (maximalIdeal B ^ n)) x := by
      apply eSource.symm_apply_eq.2
      rw [Ideal.quotEquivOfEq_mk]
    -- Proof comment: both quotient maps send the class of `x` to the class of `e x`.
    calc
      (Ideal.quotientMap (maximalIdeal B ^ n) e.toRingHom
          (ringEquiv_pow_maximalIdeal_le_comap_pow_maximalIdeal e n))
          ((Ideal.Quotient.mk (maximalIdeal A ^ n)) x) =
        (Ideal.Quotient.mk (maximalIdeal B ^ n)) (e.toRingHom x) := by
          rw [Ideal.quotientMap_mk]
      _ = qPow (eSource.symm ((Ideal.Quotient.mk (maximalIdeal A ^ n)) x)) := by
          rw [hs, Ideal.quotientMap_mk]
  have hqPow_inj : Function.Injective qPow := by
    change Function.Injective (Ideal.quotientMap (maximalIdeal B ^ n) e.toRingHom le_rfl)
    exact Ideal.quotientMap_injective
  have hqPow_surj : Function.Surjective qPow := by
    intro z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨a, rfl⟩ := e.surjective b
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    rw [Ideal.quotientMap_mk]
    rfl
  rw [hEq]
  constructor
  · intro x y hxy
    apply eSource.symm.injective
    exact hqPow_inj hxy
  · intro z
    obtain ⟨w, hw⟩ := hqPow_surj z
    refine ⟨eSource w, ?_⟩
    change qPow (eSource.symm (eSource w)) = z
    rw [eSource.symm_apply_apply]
    exact hw

/-- Helper for Chap10 Lemma 10 162 13: a local-ring equivalence induces quotient-power
equivalences on the maximal-ideal inverse systems. -/
private noncomputable abbrev ringEquiv_quotient_maximalIdeal_pow
    {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) (n : ℕ) :
    A ⧸ maximalIdeal A ^ n ≃+* B ⧸ maximalIdeal B ^ n :=
  let _ : IsLocalHom e.toRingHom := ringEquiv_isLocalHom_of_localRings e
  RingEquiv.ofBijective
    (Ideal.quotientMap (maximalIdeal B ^ n) e.toRingHom
      (ringEquiv_pow_maximalIdeal_le_comap_pow_maximalIdeal e n))
    (ringEquiv_quotient_maximalIdeal_pow_bijective e n)

/-- Helper for Chap10 Lemma 10 162 13: the quotient-power equivalences from a local-ring
equivalence commute with the inverse-system transition maps. -/
private theorem ringEquiv_quotient_maximalIdeal_pow_compatible
    {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (maximalIdeal B) hle).comp
        (ringEquiv_quotient_maximalIdeal_pow e n).toRingHom =
      (ringEquiv_quotient_maximalIdeal_pow e m).toRingHom.comp
        (Ideal.Quotient.factorPow (maximalIdeal A) hle) := by
  letI : IsLocalHom e.toRingHom := ringEquiv_isLocalHom_of_localRings e
  -- Proof comment: both routes send the class of `x` to the smaller quotient class of `e x`.
  apply Ideal.Quotient.ringHom_ext
  ext x
  simp [ringEquiv_quotient_maximalIdeal_pow, Ideal.quotientMap_mk]

/-- Helper for Chap10 Lemma 10 162 13: quotient-stage evaluations on an adic completion commute
with the inverse-system transition maps. -/
private theorem completion_eval_factor
    {A : Type u} [CommRing A] (I : Ideal A) {m n : ℕ} (hle : m ≤ n)
    (x : AdicCompletion I A) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  let p : AdicCompletion I A → Prop := fun y ↦
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n y) =
      AdicCompletion.evalₐ I m y
  change p x
  -- Proof comment: reduce to a Cauchy representative and use compatibility of its quotient
  -- classes.
  refine AdicCompletion.induction_on I A x ?_
  intro f
  change
    Ideal.Quotient.factorPow I hle
        (AdicCompletion.evalₐ I n (AdicCompletion.mk I A f)) =
      AdicCompletion.evalₐ I m (AdicCompletion.mk I A f)
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
  simpa using (AdicCompletion.Ideal.mk_eq_mk I hle f)

/-- Helper for Chap10 Lemma 10 162 13: a local-ring equivalence induces the canonical completion
map between maximal-ideal completions. -/
private noncomputable abbrev ringEquiv_completionMap
    {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    AdicCompletion (maximalIdeal A) A →+* AdicCompletion (maximalIdeal B) B :=
  let _ : IsLocalHom e.toRingHom := ringEquiv_isLocalHom_of_localRings e
  maximalIdealCompletionMap e.toRingHom

/-- Helper for Chap10 Lemma 10 162 13: a local-ring equivalence induces a bijection on
maximal-ideal completions. -/
private theorem maximalIdealCompletionMap_bijective_of_localRingEquiv
    {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    Function.Bijective (ringEquiv_completionMap e) := by
  letI : IsLocalHom e.toRingHom := ringEquiv_isLocalHom_of_localRings e
  change Function.Bijective (maximalIdealCompletionMap e.toRingHom)
  let π : ∀ n : ℕ, A ⧸ maximalIdeal A ^ n →+* B ⧸ maximalIdeal B ^ n :=
    fun n ↦ (ringEquiv_quotient_maximalIdeal_pow e n).toRingHom
  let eQuot : ∀ n : ℕ, A ⧸ maximalIdeal A ^ n ≃+* B ⧸ maximalIdeal B ^ n :=
    fun n ↦ ringEquiv_quotient_maximalIdeal_pow e n
  let q : ∀ n : ℕ, AdicCompletion (maximalIdeal B) B →+*
      A ⧸ maximalIdeal A ^ n :=
    fun n ↦ (eQuot n).symm.toRingHom.comp (AdicCompletion.evalₐ (maximalIdeal B) n)
  have hπ_compat :
      ∀ {m n : ℕ} (hle : m ≤ n),
        (Ideal.Quotient.factorPow (maximalIdeal B) hle).comp (π n) =
          (π m).comp (Ideal.Quotient.factorPow (maximalIdeal A) hle) := by
    intro m n hle
    -- Proof comment: the quotient-stage equivalences already commute with the transition maps.
    simpa [π, eQuot] using ringEquiv_quotient_maximalIdeal_pow_compatible e hle
  have hq_compat :
      ∀ {m n : ℕ} (hle : m ≤ n),
        (Ideal.Quotient.factorPow (maximalIdeal A) hle).comp (q n) = q m := by
    intro m n hle
    ext x
    -- Proof comment: compare after postcomposing with the quotient equivalence `π m`.
    apply (eQuot m).injective
    calc
      π m ((Ideal.Quotient.factorPow (maximalIdeal A) hle) (q n x)) =
          (Ideal.Quotient.factorPow (maximalIdeal B) hle) (π n (q n x)) := by
            symm
            exact DFunLike.congr_fun (hπ_compat hle) (q n x)
      _ = (Ideal.Quotient.factorPow (maximalIdeal B) hle)
            (AdicCompletion.evalₐ (maximalIdeal B) n x) := by
              congr 1
              exact RingEquiv.apply_symm_apply (eQuot n) (AdicCompletion.evalₐ (maximalIdeal B) n x)
      _ = AdicCompletion.evalₐ (maximalIdeal B) m x := by
              simpa using completion_eval_factor (maximalIdeal B) hle x
      _ = π m (q m x) := by
              exact
                (RingEquiv.apply_symm_apply
                  (eQuot m) (AdicCompletion.evalₐ (maximalIdeal B) m x)).symm
  let ψ : AdicCompletion (maximalIdeal B) B →+*
      AdicCompletion (maximalIdeal A) A :=
    AdicCompletion.liftRingHom (maximalIdeal A) q hq_compat
  let φ : AdicCompletion (maximalIdeal A) A →+*
      AdicCompletion (maximalIdeal B) B :=
    maximalIdealCompletionMap e.toRingHom
  have hφ_eval :
      ∀ n : ℕ, ∀ x : AdicCompletion (maximalIdeal A) A,
        AdicCompletion.evalₐ (maximalIdeal B) n (φ x) =
          π n (AdicCompletion.evalₐ (maximalIdeal A) n x) := by
    intro n x
    let p : AdicCompletion (maximalIdeal A) A → Prop := fun y ↦
      AdicCompletion.evalₐ (maximalIdeal B) n (φ y) =
        π n (AdicCompletion.evalₐ (maximalIdeal A) n y)
    change p x
    -- Proof comment: on Cauchy representatives the stage formula is definitional.
    refine AdicCompletion.induction_on (maximalIdeal A) A x ?_
    intro f
    rfl
  have hleft : ψ.comp φ = RingHom.id _ := by
    apply RingHom.ext
    intro x
    -- Proof comment: both completion endomorphisms agree on every quotient stage of `A^∧`.
    apply AdicCompletion.ext_evalₐ
    intro n
    calc
      AdicCompletion.evalₐ (maximalIdeal A) n ((ψ.comp φ) x) = q n (φ x) := by
          simp [ψ]
      _ = (eQuot n).symm (AdicCompletion.evalₐ (maximalIdeal B) n (φ x)) := by
          rfl
      _ = (eQuot n).symm (π n (AdicCompletion.evalₐ (maximalIdeal A) n x)) := by
          rw [hφ_eval n x]
      _ = AdicCompletion.evalₐ (maximalIdeal A) n x := by
          exact RingEquiv.symm_apply_apply (eQuot n) (AdicCompletion.evalₐ (maximalIdeal A) n x)
  have hright : φ.comp ψ = RingHom.id _ := by
    apply RingHom.ext
    intro x
    -- Proof comment: the same quotientwise computation shows the opposite composite is the
    -- identity on `B^∧`.
    apply AdicCompletion.ext_evalₐ
    intro n
    calc
      AdicCompletion.evalₐ (maximalIdeal B) n ((φ.comp ψ) x) =
          π n (AdicCompletion.evalₐ (maximalIdeal A) n (ψ x)) := by
            change AdicCompletion.evalₐ (maximalIdeal B) n (φ (ψ x)) =
              π n (AdicCompletion.evalₐ (maximalIdeal A) n (ψ x))
            rw [hφ_eval n (ψ x)]
      _ = π n (q n x) := by
            simp [ψ]
      _ = π n ((eQuot n).symm (AdicCompletion.evalₐ (maximalIdeal B) n x)) := by
            rfl
      _ = AdicCompletion.evalₐ (maximalIdeal B) n x := by
            exact RingEquiv.apply_symm_apply (eQuot n) (AdicCompletion.evalₐ (maximalIdeal B) n x)
  exact
    ⟨Function.LeftInverse.injective (fun x ↦ by simpa using DFunLike.congr_fun hleft x),
      Function.RightInverse.surjective (fun x ↦ by simpa using DFunLike.congr_fun hright x)⟩

/-- Helper for Chap10 Lemma 10 162 13: a local-ring equivalence induces a ring equivalence on
maximal-ideal completions. -/
private noncomputable def completionCompareRingEquivOfLocalRingEquiv
    {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    AdicCompletion (maximalIdeal A) A ≃+* AdicCompletion (maximalIdeal B) B :=
  RingEquiv.ofBijective
    (ringEquiv_completionMap e)
    (maximalIdealCompletionMap_bijective_of_localRingEquiv e)

/-- Helper for Chap10 Lemma 10 162 13: the completion comparison from a local-ring equivalence
intertwines the canonical completion maps. -/
private theorem completionCompareRingEquivOfLocalRingEquiv_comp
    {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    (completionCompareRingEquivOfLocalRingEquiv e).toRingHom.comp
        (algebraMap A (AdicCompletion (maximalIdeal A) A)) =
      (algebraMap B (AdicCompletion (maximalIdeal B) B)).comp e.toRingHom := by
  letI : IsLocalHom e.toRingHom := ringEquiv_isLocalHom_of_localRings e
  -- Proof comment: the completion comparison was defined from the canonical completion map.
  simpa [completionCompareRingEquivOfLocalRingEquiv, ringEquiv_completionMap] using
    (maximalIdealCompletionMap_comp e.toRingHom)

/-- Helper for Chap10 Lemma 10 162 13: the completion map induced by the canonical localization
at the maximal ideal is bijective. -/
lemma maximalIdealCompletionMap_bijective_of_localizationAtMaximal
    {B : Type u} [CommRing B] [IsLocalRing B] :
    Function.Bijective
      (ringEquiv_completionMap
        ((localizationAtMaximalRingEquiv B).toRingEquiv)) := by
  let eLoc : Localization.AtPrime (maximalIdeal B) ≃+* B :=
    (localizationAtMaximalRingEquiv B).toRingEquiv
  simpa [ringEquiv_completionMap] using
    (maximalIdealCompletionMap_bijective_of_localRingEquiv eLoc)

/-- Helper for Chap10 Lemma 10 162 13: the canonical localization at the maximal ideal induces a
ring equivalence between the two maximal-ideal completions. -/
noncomputable def completionLocalizationAtMaximal_ringEquiv
    {B : Type u} [CommRing B] [IsLocalRing B] :
    AdicCompletion
        (maximalIdeal (Localization.AtPrime (maximalIdeal B)))
        (Localization.AtPrime (maximalIdeal B)) ≃+*
      AdicCompletion (maximalIdeal B) B := by
  let eLoc : Localization.AtPrime (maximalIdeal B) ≃+* B :=
    (localizationAtMaximalRingEquiv B).toRingEquiv
  -- Proof comment: package the bijective completion comparison into a ring equivalence.
  exact completionCompareRingEquivOfLocalRingEquiv eLoc

/-- Helper for Chap10 Lemma 10 162 13: the maximal-localization completion comparison commutes
with the original base algebra map. -/
private theorem completionLocalizationAtMaximal_ringEquiv_commutes
    {B : Type u} [CommRing B] [IsLocalRing B] (x : B) :
    completionLocalizationAtMaximal_ringEquiv (B := B)
      (algebraMap B
        (AdicCompletion
          (maximalIdeal (Localization.AtPrime (maximalIdeal B)))
          (Localization.AtPrime (maximalIdeal B))) x) =
      algebraMap B (AdicCompletion (maximalIdeal B) B) x := by
  let eLoc : Localization.AtPrime (maximalIdeal B) ≃+* B :=
    (localizationAtMaximalRingEquiv B).toRingEquiv
  have hcomp :=
    DFunLike.congr_fun (completionCompareRingEquivOfLocalRingEquiv_comp eLoc)
      (algebraMap B (Localization.AtPrime (maximalIdeal B)) x)
  -- Proof comment: evaluate the generic completion comparison on the localized image of `x`,
  -- then use that `eLoc` is an algebra equivalence over `B`.
  calc
    completionLocalizationAtMaximal_ringEquiv (B := B)
        (algebraMap
          (Localization.AtPrime (maximalIdeal B))
          (AdicCompletion
            (maximalIdeal (Localization.AtPrime (maximalIdeal B)))
            (Localization.AtPrime (maximalIdeal B)))
          (algebraMap B (Localization.AtPrime (maximalIdeal B)) x)) =
      algebraMap B (AdicCompletion (maximalIdeal B) B)
        (eLoc (algebraMap B (Localization.AtPrime (maximalIdeal B)) x)) := by
          simpa [completionLocalizationAtMaximal_ringEquiv, RingHom.comp_apply] using hcomp
    _ = algebraMap B (AdicCompletion (maximalIdeal B) B) x := by
          congr 1
          exact (localizationAtMaximalRingEquiv B).commutes x

/-- Helper for Chap10 Lemma 10 162 13: the maximal-localization completion comparison is an
algebra equivalence over the original base ring. -/
private noncomputable def completionLocalizationAtMaximal_algEquiv
    {B : Type u} [CommRing B] [IsLocalRing B] :
    AdicCompletion
        (maximalIdeal (Localization.AtPrime (maximalIdeal B)))
        (Localization.AtPrime (maximalIdeal B)) ≃ₐ[B]
      AdicCompletion (maximalIdeal B) B :=
  AlgEquiv.ofRingEquiv
    (f := completionLocalizationAtMaximal_ringEquiv (B := B))
    (completionLocalizationAtMaximal_ringEquiv_commutes (B := B))

/-- Helper for Chap10 Lemma 10 162 13: specializing Lemma `10.97.8` at the closed point of
`Spec B` gives a ring equivalence from the completed tensor product over `B` to the product of
the completed local factors. -/
noncomputable def completionTensor_closedPoint_ringEquiv_piLocalCompletion
    {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    {S : Type u} [CommRing S] [Algebra B S] [Module.Finite B S] :
    ((AdicCompletion (maximalIdeal B) B) ⊗[B] S) ≃+*
      ∀ q : (maximalIdeal B).primesOver S,
        AdicCompletion (maximalIdeal (Localization.AtPrime q.1)) (Localization.AtPrime q.1) := by
  let closedPoint : PrimeSpectrum B := ⟨maximalIdeal B, (maximalIdeal.isMaximal B).isPrime⟩
  let eBase :
      AdicCompletion (maximalIdeal B) B ≃ₐ[B]
        AdicCompletion
          (maximalIdeal (Localization.AtPrime (maximalIdeal B)))
          (Localization.AtPrime (maximalIdeal B)) :=
    (completionLocalizationAtMaximal_algEquiv (B := B)).symm
  let eTensor :
      ((AdicCompletion (maximalIdeal B) B) ⊗[B] S) ≃+*
        ((AdicCompletion
            (maximalIdeal (Localization.AtPrime (maximalIdeal B)))
            (Localization.AtPrime (maximalIdeal B))) ⊗[B] S) :=
    (Algebra.TensorProduct.congr eBase (show S ≃ₐ[B] S from AlgEquiv.refl)).toRingEquiv
  let ePi :
      ((AdicCompletion
          (maximalIdeal (Localization.AtPrime (maximalIdeal B)))
          (Localization.AtPrime (maximalIdeal B))) ⊗[B] S) ≃+*
        ∀ q : (maximalIdeal B).primesOver S,
          AdicCompletion (maximalIdeal (Localization.AtPrime q.1)) (Localization.AtPrime q.1) := by
    -- Proof comment: `closedPoint.asIdeal = maximalIdeal B`, so the owner theorem specializes
    -- directly.
    simpa [closedPoint] using
      completion_tensorProductOverBase_ringEquiv_pi_localRingCompletion (R := B) (S := S)
        closedPoint
  -- Proof comment: first rewrite the completed base factor via the canonical completion
  -- comparison, then apply the closed-point form of Lemma `10.97.8`.
  exact eTensor.trans ePi

/-- Helper for Chap10 Lemma 10 162 13: factorwise analytic unramifiedness of the maximal
localizations of a finite algebra makes the completed tensor product reduced. -/
lemma reduced_completionTensor_of_factorwiseAnalytic
    {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    {S : Type u} [CommRing S] [Algebra B S] [Module.Finite B S]
    (hfactor :
      ∀ q : (maximalIdeal B).primesOver S,
        IsAnalyticallyUnramified (Localization.AtPrime q.1)) :
    IsReduced ((AdicCompletion (maximalIdeal B) B) ⊗[B] S) := by
  -- Route correction: instead of a generic completion-comparison API, specialize directly to the
  -- canonical equivalence `Localization.AtPrime (maximalIdeal B) ≃ₐ[B] B`, then use the closed
  -- point of Lemma `10.97.8`.
  let ePi := completionTensor_closedPoint_ringEquiv_piLocalCompletion (B := B) (S := S)
  have hReducedFactors :
      IsReduced
        (∀ q : (maximalIdeal B).primesOver S,
          AdicCompletion (maximalIdeal (Localization.AtPrime q.1)) (Localization.AtPrime q.1)) := by
    -- Proof comment: each coordinate is reduced because the corresponding local ring is assumed
    -- analytically unramified.
    refine isReduced_pi_of_forall ?_
    intro q
    letI : IsAnalyticallyUnramified (Localization.AtPrime q.1) := hfactor q
    infer_instance
  letI :
      IsReduced
        (∀ q : (maximalIdeal B).primesOver S,
          AdicCompletion (maximalIdeal (Localization.AtPrime q.1)) (Localization.AtPrime q.1)) :=
    hReducedFactors
  -- Proof comment: pull reducedness back across the closed-point tensor/product equivalence.
  exact isReduced_of_injective ePi.toRingHom ePi.injective

/-- Helper for Chap10 Lemma 10 162 13: a local Nagata domain is analytically unramified. -/
lemma nagataLocalDomain_isAnalyticallyUnramified_by_normalization
    {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [NagataRing A] :
    IsAnalyticallyUnramified A := by
  obtain ⟨n, hnA⟩ := exists_nat_ringKrullDim_of_local_noetherian_ring (A := A)
  let P : ℕ → Prop := fun n =>
    ∀ {B : Type u} [CommRing B] [IsLocalRing B] [IsDomain B] [NagataRing B],
      ringKrullDim B = n → IsAnalyticallyUnramified B
  have hPstep : ∀ n : ℕ, (∀ m < n, P m) → P n := by
    intro n ih B _ _ _ _ hdimB
    by_cases hfieldB : IsField B
    · exact field_isAnalyticallyUnramified_of_isField hfieldB
    · let K := FractionRing B
      let S := integralClosure B K
      have hfiniteS : Module.Finite B S := by
        -- Proof comment: the normalization is finite, so the induction step can run through its
        -- maximal localizations.
        letI : IsN2Ring B := nagataRing_isN2Ring (A := B)
        exact IsN2Ring.integralClosure_finite_of_finiteDimensional (R := B) (L := K)
      letI : Module.Finite B S := hfiniteS
      letI : NagataRing S := nagataRing_of_finiteType_from_tfae B
      have hfactor :
          ∀ q : (maximalIdeal B).primesOver S,
            IsAnalyticallyUnramified (Localization.AtPrime q.1) := by
        intro q
        exact normalizationLocalFactor_isAnalyticallyUnramified ih hdimB q
      have hredTensor :
          IsReduced ((AdicCompletion (maximalIdeal B) B) ⊗[B] S) :=
        reduced_completionTensor_of_factorwiseAnalytic (B := B) (S := S) hfactor
      exact
        isAnalyticallyUnramified_of_reduced_completionTensor
          (A := B) (S := S)
          (integralClosure_algebraMap_injective (A := B))
          hredTensor
  have hP : ∀ n : ℕ, P n := by
    intro n
    exact Nat.strong_induction_on (p := P) n hPstep
  exact hP n (B := A) hnA

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsDomain R] [NagataRing R]

/-- Chap10 Lemma 10 162 13: a local Nagata domain is analytically unramified. -/
@[stacks 0331]
instance isAnalyticallyUnramified_of_nagataRing : IsAnalyticallyUnramified R := by
  exact nagataLocalDomain_isAnalyticallyUnramified_by_normalization

end
