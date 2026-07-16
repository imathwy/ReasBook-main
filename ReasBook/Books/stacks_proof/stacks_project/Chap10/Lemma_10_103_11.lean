import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_103_1
import stacks_proof.stacks_project.Chap10.Lemma_10_72_3
import stacks_proof.stacks_project.Chap10.Lemma_10_72_10
import stacks_proof.stacks_project.Chap10.Lemma_10_103_6
import stacks_proof.stacks_project.Chap10.Lemma_10_103_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped ENat
open IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type u} [AddCommGroup M] [Module R M] [Module.CohenMacaulay R M]

namespace Module.CohenMacaulay

variable (p : Ideal R) [hp : p.IsPrime]

local notation "Rₚ" => Localization.AtPrime p
local notation "Mₚ" => LocalizedModule.AtPrime p M

/-- Helper for Lemma 10.103.11: Cohen-Macaulayness is unchanged by a linear equivalence of finite
modules over a Noetherian local ring. -/
private theorem moduleDepth_eq_of_linearEquiv
    {A : Type*} [CommRing A] [IsLocalRing A]
    {N N' : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
    [AddCommGroup N'] [Module A N'] [Module.Finite A N']
    (e : N ≃ₗ[A] N') :
    moduleDepth A N = moduleDepth A N' := by
  change Ideal.depth (maximalIdeal A) N = Ideal.depth (maximalIdeal A) N'
  -- Compare the two depth computations by transporting regular sequences across the equivalence.
  have htop :
      maximalIdeal A • (⊤ : Submodule A N) = ⊤ ↔
        maximalIdeal A • (⊤ : Submodule A N') = ⊤ := by
    constructor
    · intro h
      have hmap := congrArg (Submodule.map e.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.surjective] using hmap
    · intro h
      have hmap := congrArg (Submodule.map e.symm.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.symm.surjective] using hmap
  have hreg :
      Ideal.regularSequenceLengths (maximalIdeal A) N =
        Ideal.regularSequenceLengths (maximalIdeal A) N' := by
    ext d
    constructor
    · rintro ⟨rs, hregular, hmem, rfl⟩
      exact ⟨rs, (e.isRegular_congr rs).1 hregular, hmem, rfl⟩
    · rintro ⟨rs, hregular, hmem, rfl⟩
      exact ⟨rs, (e.isRegular_congr rs).2 hregular, hmem, rfl⟩
  by_cases hN : maximalIdeal A • (⊤ : Submodule A N) = ⊤
  · rw [Ideal.depth_eq_top_of_smul_top (maximalIdeal A) N hN,
      Ideal.depth_eq_top_of_smul_top (maximalIdeal A) N' (htop.mp hN)]
  · rw [Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal A) N hN,
      Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal A) N' (mt htop.mpr hN),
      hreg]

/-- Helper for Lemma 10.103.11: Cohen-Macaulayness is unchanged by a linear equivalence of finite
modules over a Noetherian local ring. -/
private theorem of_linearEquiv
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {N N' : Type*} [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']
    (e : N ≃ₗ[A] N') [h : Module.CohenMacaulay A N] :
    Module.CohenMacaulay A N' := by
  let _ : Module.Finite A N' := Module.Finite.equiv e
  -- Transport the defining support-dimension/depth equality across the linear equivalence.
  exact ⟨by
    rw [← Module.supportDim_eq_of_equiv e, ← moduleDepth_eq_of_linearEquiv e,
      h.supportDim_eq_moduleDepth]⟩

/-- Helper for Lemma 10.103.11: the Krull dimension of a Noetherian local ring is represented by a
natural number. -/
private lemma ringKrullDim_eq_nat_of_local_noetherian_ring
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    ∃ n : ℕ, ringKrullDim A = n := by
  -- Local Noetherian rings have finite Krull dimension, so the `ℕ∞` value comes from an actual
  -- natural number.
  have hbot : ringKrullDim A ≠ ⊥ := ringKrullDim_ne_bot
  have htop : ringKrullDim A ≠ ⊤ := ringKrullDim_ne_top
  let n : ℕ := ((ringKrullDim A).unbot hbot).toNat
  have hneTop : (ringKrullDim A).unbot hbot ≠ ⊤ := by
    intro htop'
    exact htop <| by
      simpa [WithBot.coe_unbot] using
        congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) htop'
  have hdim' : ((ringKrullDim A).unbot hbot : WithBot ℕ∞) = n := by
    simpa [n] using
      congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat hneTop).symm
  refine ⟨n, ?_⟩
  calc
    ringKrullDim A = (ringKrullDim A).unbot hbot := by
      exact (WithBot.coe_unbot (ringKrullDim A) hbot).symm
    _ = n := hdim'

/-- Helper for Lemma 10.103.11: a `WithBot ℕ∞` value that is neither bottom nor top is represented
by a natural number. -/
private lemma withBot_enat_eq_nat_of_ne_bot_of_ne_top
    (x : WithBot ℕ∞) (hbot : x ≠ ⊥) (htop : x ≠ ⊤) :
    ∃ n : ℕ, x = n := by
  let n : ℕ := (x.unbot hbot).toNat
  have hneTop : x.unbot hbot ≠ ⊤ := by
    intro htop'
    exact htop <| by
      simpa [WithBot.coe_unbot] using
        congrArg (fun y : ℕ∞ ↦ (y : WithBot ℕ∞)) htop'
  have hx' : ((x.unbot hbot : ℕ∞) : WithBot ℕ∞) = n := by
    simpa [n] using
      congrArg (fun y : ℕ∞ ↦ (y : WithBot ℕ∞)) (ENat.coe_toNat hneTop).symm
  refine ⟨n, ?_⟩
  calc
    x = (x.unbot hbot : ℕ∞) := by
      exact (WithBot.coe_unbot x hbot).symm
    _ = n := hx'

/-- Helper for Lemma 10.103.11: after passing to `R / Ann_R(M)`, the induced module is faithful. -/
private theorem annihilator_eq_bot_over_annihilator_quotient :
    let A := R ⧸ Module.annihilator R M
    letI : Module A M := Module.quotientAnnihilator
    Module.annihilator A M = ⊥ := by
  let A := R ⧸ Module.annihilator R M
  letI : Module A M := Module.quotientAnnihilator
  have hsurj_mk : Function.Surjective (Ideal.Quotient.mk (Module.annihilator R M)) :=
    Ideal.Quotient.mk_surjective
  refine le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨r, rfl⟩ := hsurj_mk x
  rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
  -- An element of the quotient annihilator is represented by an element of the original
  -- annihilator.
  rw [Module.mem_annihilator] at hx ⊢
  intro m
  simpa [Module.IsTorsionBySet.mk_smul (Module.isTorsionBySet_annihilator R M) r m] using hx m

/-- Helper for Lemma 10.103.11: the support over `R / Ann_R(M)` is all of `Spec`. -/
private theorem support_eq_univ_over_annihilator_quotient :
    let A := R ⧸ Module.annihilator R M
    letI : Module A M := Module.quotientAnnihilator
    letI : IsScalarTower R A M :=
      Module.IsTorsionBySet.isScalarTower (Module.isTorsionBySet_annihilator R M)
    letI : IsNoetherianRing A := Ideal.Quotient.isNoetherianRing (Module.annihilator R M)
    letI : Module.Finite A M := Module.Finite.of_restrictScalars_finite R A M
    Module.support A M = Set.univ := by
  let A := R ⧸ Module.annihilator R M
  letI : Module A M := Module.quotientAnnihilator
  letI : IsScalarTower R A M :=
    Module.IsTorsionBySet.isScalarTower (Module.isTorsionBySet_annihilator R M)
  letI : IsNoetherianRing A := Ideal.Quotient.isNoetherianRing (Module.annihilator R M)
  letI : Module.Finite A M := Module.Finite.of_restrictScalars_finite R A M
  -- Faithfulness over the quotient identifies the support with `V(0) = Spec A`.
  have hsupp : Module.support A M = Set.univ := by
    rw [Module.support_eq_zeroLocus, annihilator_eq_bot_over_annihilator_quotient (R := R) (M := M),
      PrimeSpectrum.zeroLocus_bot]
  simpa [A] using hsupp

/-- Helper for Lemma 10.103.11: the original annihilator still kills the localization `Mₚ`. -/
private theorem annihilator_le_localizedModule_annihilator :
    Module.annihilator R M ≤ Module.annihilator R Mₚ := by
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  -- Localizing a vector killed in `M` stays killed in `Mₚ`.
  induction x using LocalizedModule.induction_on with
  | h m s =>
      rw [Module.mem_annihilator] at hr
      simpa [LocalizedModule.smul'_mk, hr m]

/-- Helper for Lemma 10.103.11: the image of `Ann_R(M)` in `Rₚ` annihilates the localized
module `Mₚ`. -/
private theorem annihilator_map_le_localizedModule_annihilator :
    Ideal.map (algebraMap R Rₚ) (Module.annihilator R M) ≤ Module.annihilator Rₚ Mₚ := by
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  rw [Ideal.mem_comap, Module.mem_annihilator]
  -- Every generator coming from `Ann_R(M)` still acts by zero after localization.
  intro x
  induction x using LocalizedModule.induction_on with
  | h m s =>
      rw [Module.mem_annihilator] at hr
      simpa [LocalizedModule.smul'_mk, hr m]

/-- Helper for Lemma 10.103.11: after quotienting by `Ann_R(M)`, the complement of `p` descends
to the complement of the induced prime ideal. -/
private theorem annihilator_quotient_primeCompl_eq
    (hIp : Module.annihilator R M ≤ p) :
    let I := Module.annihilator R M
    let A := R ⧸ I
    let pA : Ideal A := Ideal.map (Ideal.Quotient.mk I) p
    letI : pA.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime (I := I) (p := p) hIp
    Algebra.algebraMapSubmonoid A p.primeCompl = pA.primeCompl := by
  let I := Module.annihilator R M
  let A := R ⧸ I
  let pA : Ideal A := Ideal.map (Ideal.Quotient.mk I) p
  letI : pA.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime (I := I) (p := p) hIp
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    change Ideal.Quotient.mk I r ∉ pA
    intro hx
    have hcomap :
        Ideal.comap (Ideal.Quotient.mk I) pA = p := by
      dsimp [pA]
      exact Ideal.comap_map_mk (I := I) (J := p) hIp
    have : r ∈ p := by
      have hx' : r ∈ Ideal.comap (Ideal.Quotient.mk I) pA := hx
      simpa [hcomap] using hx'
    exact hr this
  · intro hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨r, ?_, rfl⟩
    intro hr
    exact hx (Ideal.mem_map_of_mem (Ideal.Quotient.mk I) hr)

/-- Helper for Lemma 10.103.11: localizing `R / Ann_R(M)` at the induced prime agrees with the
quotient of `Rₚ` by the localized annihilator ideal. -/
private noncomputable def localized_annihilator_quotient_ringEquiv
    (hIp : Module.annihilator R M ≤ p) :
    let I := Module.annihilator R M
    let A := R ⧸ I
    let pA : Ideal A := Ideal.map (Ideal.Quotient.mk I) p
    letI : pA.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime (I := I) (p := p) hIp
    Localization.AtPrime pA ≃ₐ[A]
      (Rₚ ⧸ Ideal.map (algebraMap R Rₚ) I) := by
  let I := Module.annihilator R M
  let A := R ⧸ I
  let pA : Ideal A := Ideal.map (Ideal.Quotient.mk I) p
  let Iₚ : Ideal Rₚ := Ideal.map (algebraMap R Rₚ) I
  let Q := Rₚ ⧸ Iₚ
  letI : pA.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime (I := I) (p := p) hIp
  letI : Algebra A Q := Ideal.Quotient.algebraQuotientMapQuotient
  letI : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr <| by
    intro htop
    have hmap_le : Iₚ ≤ maximalIdeal Rₚ := by
      calc
        Iₚ ≤ Ideal.map (algebraMap R Rₚ) p := Ideal.map_mono hIp
        _ = maximalIdeal Rₚ := Localization.AtPrime.map_eq_maximalIdeal (I := p)
    exact (maximalIdeal.isMaximal Rₚ).ne_top <| top_unique <| by
      simpa [Q, Iₚ, htop] using hmap_le
  let hprimeCompl :
      Algebra.algebraMapSubmonoid A p.primeCompl = pA.primeCompl :=
    annihilator_quotient_primeCompl_eq (R := R) (M := M) (p := p) hIp
  letI : IsLocalization (Algebra.algebraMapSubmonoid A p.primeCompl) Q := by
    let f : R →+* A := Ideal.Quotient.mk I
    let g : Rₚ →+* Q := Ideal.Quotient.mk Iₚ
    refine IsLocalization.of_surjective (M := p.primeCompl) (S := Rₚ) f
      Ideal.Quotient.mk_surjective g Ideal.Quotient.mk_surjective ?_ ?_
    · ext r
      rfl
    · intro x hx
      have hx' : x ∈ Iₚ := by
        simpa [g] using (Ideal.Quotient.eq_zero_iff_mem.mp hx)
      have hker : RingHom.ker f = I := by
        change RingHom.ker (Ideal.Quotient.mk I) = I
        exact Ideal.mk_ker (I := I)
      rw [hker]
      exact hx'
  letI : IsLocalization pA.primeCompl Q := by
    simpa [hprimeCompl] using
      (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid A p.primeCompl) Q)
  -- The quotient presentation carries exactly the same localization universal property.
  exact Localization.algEquiv pA.primeCompl Q

/-- Helper for Lemma 10.103.11: the support dimension of `Mₚ` is bounded by the dimension of the
localized annihilator quotient. -/
private theorem supportDim_localizedModule_atPrime_le_localized_annihilator_quotient_dim :
    Module.supportDim Rₚ Mₚ ≤
      ringKrullDim (Rₚ ⧸ Ideal.map (algebraMap R Rₚ) (Module.annihilator R M)) := by
  have hann_le :
      Ideal.map (algebraMap R Rₚ) (Module.annihilator R M) ≤ Module.annihilator Rₚ Mₚ :=
    annihilator_map_le_localizedModule_annihilator (R := R) (M := M) (p := p)
  -- Compare the annihilator quotient of `Mₚ` with the larger quotient by the localized global
  -- annihilator.
  rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator (R := Rₚ) (M := Mₚ)]
  exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hann_le)
    (Ideal.Quotient.factor_surjective hann_le)

/-- Helper for Lemma 10.103.11: the localized support dimension plus `dim(R / p)` is bounded by
the global support dimension. -/
private theorem supportDim_localizedModule_atPrime_add_ringKrullDim_quotient_le_supportDim
    (hpM : (⟨p, hp⟩ : PrimeSpectrum R) ∈ Module.support R M) :
    Module.supportDim Rₚ Mₚ + ringKrullDim (R ⧸ p) ≤ Module.supportDim R M := by
  let I := Module.annihilator R M
  let A := R ⧸ I
  let pA : Ideal A := Ideal.map (Ideal.Quotient.mk I) p
  let Iₚ : Ideal Rₚ := Ideal.map (algebraMap R Rₚ) I
  have hIp : I ≤ p := Module.annihilator_le_of_mem_support hpM
  letI : pA.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime (I := I) (p := p) hIp
  letI : Module A M := Module.quotientAnnihilator
  letI : IsScalarTower R A M :=
    Module.IsTorsionBySet.isScalarTower (Module.isTorsionBySet_annihilator R M)
  letI : Nontrivial A := Ideal.Quotient.nontrivial_iff.mpr <| by
    intro htop
    exact hp.ne_top <| top_unique <| by simpa [A, I, htop] using hIp
  letI : IsLocalRing A := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  letI : IsNoetherianRing A := Ideal.Quotient.isNoetherianRing I
  letI : Module.Finite A M := Module.Finite.of_restrictScalars_finite R A M
  have hCM_A : Module.CohenMacaulay A M := by
    exact
      (Module.cohenMacaulay_iff_restrictScalars_of_surjective
        (R := R) (S := A) (N := M) Ideal.Quotient.mk_surjective).2 inferInstance
  have hsupp_A : Module.support A M = Set.univ :=
    support_eq_univ_over_annihilator_quotient (R := R) (M := M)
  have hdim_A :
      ringKrullDim A = ringKrullDim (Localization.AtPrime pA) + ringKrullDim (A ⧸ pA) :=
    @ringKrullDim_eq_ringKrullDim_atPrime_add_ringKrullDim_quotient_of_full_support_cohenMacaulay
      A _ _ _ M _ _ hCM_A hsupp_A pA inferInstance
  have hloc :
      ringKrullDim (Localization.AtPrime pA) = ringKrullDim (Rₚ ⧸ Iₚ) := by
    exact ringKrullDim_eq_of_ringEquiv
      (localized_annihilator_quotient_ringEquiv (R := R) (M := M) (p := p) hIp).toRingEquiv
  have hquot :
      ringKrullDim (A ⧸ pA) = ringKrullDim (R ⧸ p) := by
    exact ringKrullDim_eq_of_ringEquiv
      (DoubleQuot.quotQuotEquivQuotOfLE (R := R) (I := I) (J := p) hIp)
  have hsplit :
      ringKrullDim (Rₚ ⧸ Iₚ) + ringKrullDim (R ⧸ p) = Module.supportDim R M := by
    calc
      ringKrullDim (Rₚ ⧸ Iₚ) + ringKrullDim (R ⧸ p) =
          ringKrullDim (Localization.AtPrime pA) + ringKrullDim (A ⧸ pA) := by
            rw [hloc, hquot]
      _ = ringKrullDim A := hdim_A.symm
      _ = Module.supportDim R M := by
            simpa [A, I] using
              (Module.supportDim_eq_ringKrullDim_quotient_annihilator (R := R) (M := M)).symm
  -- First compare with the quotient ring obtained from the global annihilator, then rewrite the
  -- resulting sum using the quotient-side dimension formula over `R / Ann_R(M)`.
  calc
    Module.supportDim Rₚ Mₚ + ringKrullDim (R ⧸ p)
        ≤ ringKrullDim (Rₚ ⧸ Iₚ) + ringKrullDim (R ⧸ p) := by
          exact add_le_add
            (supportDim_localizedModule_atPrime_le_localized_annihilator_quotient_dim
              (R := R) (M := M) (p := p)) le_rfl
    _ = Module.supportDim R M := hsplit

/-- Helper for Lemma 10.103.11: the support dimension of `Mₚ` is at most the localized module
depth. -/
private theorem supportDim_le_moduleDepth_of_localized_split
    (hpM : (⟨p, hp⟩ : PrimeSpectrum R) ∈ Module.support R M) :
    Module.supportDim Rₚ Mₚ ≤ WithBot.some (moduleDepth Rₚ Mₚ) := by
  letI : Nontrivial Mₚ := Module.mem_support_iff.mp hpM
  have hsupport_split :
      Module.supportDim Rₚ Mₚ + ringKrullDim (R ⧸ p) ≤ Module.supportDim R M :=
    supportDim_localizedModule_atPrime_add_ringKrullDim_quotient_le_supportDim
      (R := R) (M := M) (p := p) hpM
  have hdepth_split :
      WithBot.some (moduleDepth R M : ℕ∞) ≤
        WithBot.some (moduleDepth Rₚ Mₚ : ℕ∞) + ringKrullDim (R ⧸ p) := by
    simpa [ge_iff_le] using
      (@moduleDepth_localizedModule_atPrime_add_ringKrullDim_quotient_ge_moduleDepth
        R _ _ _ M _ _ inferInstance p hp)
  have hdepth_le_support :
      WithBot.some (moduleDepth Rₚ Mₚ : ℕ∞) ≤ Module.supportDim Rₚ Mₚ :=
    depth_le_supportDim (R := Rₚ) (M := Mₚ)
  have hsupport_le_ring :
      Module.supportDim Rₚ Mₚ ≤ ringKrullDim Rₚ :=
    Module.supportDim_le_ringKrullDim (R := Rₚ) (M := Mₚ)
  have hsupport_ne_bot : Module.supportDim Rₚ Mₚ ≠ ⊥ :=
    Module.supportDim_ne_bot_of_nontrivial Rₚ Mₚ
  obtain ⟨nR, hnR⟩ := ringKrullDim_eq_nat_of_local_noetherian_ring (A := R)
  obtain ⟨nRp, hnRp⟩ := ringKrullDim_eq_nat_of_local_noetherian_ring (A := Rₚ)
  letI : IsLocalRing (R ⧸ p) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  obtain ⟨nQuot, hnQuot⟩ := ringKrullDim_eq_nat_of_local_noetherian_ring (A := R ⧸ p)
  have hsupport_ne_top : Module.supportDim Rₚ Mₚ ≠ ⊤ := by
    intro htop
    have : ringKrullDim Rₚ = ⊤ := by
      exact top_unique <| by simpa [htop] using hsupport_le_ring
    exact ringKrullDim_ne_top this
  obtain ⟨nSuppLoc, hSuppLoc⟩ :=
    withBot_enat_eq_nat_of_ne_bot_of_ne_top
      (x := Module.supportDim Rₚ Mₚ) hsupport_ne_bot hsupport_ne_top
  have hdepth_ne_top : moduleDepth Rₚ Mₚ ≠ ⊤ := by
    intro htop
    have : Module.supportDim Rₚ Mₚ = ⊤ := by
      exact top_unique <| by simpa [htop] using hdepth_le_support
    exact hsupport_ne_top this
  obtain ⟨nDepthLoc, hDepthLocENat⟩ := ENat.ne_top_iff_exists.mp hdepth_ne_top
  have hDepthLoc : WithBot.some (moduleDepth Rₚ Mₚ : ℕ∞) = nDepthLoc := by
    simpa using congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) hDepthLocENat.symm
  have hglobal_ne_bot : Module.supportDim R M ≠ ⊥ := by
    simpa [Module.CohenMacaulay.supportDim_eq_moduleDepth (R := R) (M := M)]
  have hglobal_ne_top : Module.supportDim R M ≠ ⊤ := by
    intro htop
    have hsupport_global :
        Module.supportDim R M ≤ ringKrullDim R :=
      Module.supportDim_le_ringKrullDim (R := R) (M := M)
    have : ringKrullDim R = ⊤ := by
      exact top_unique <| by simpa [htop] using hsupport_global
    exact ringKrullDim_ne_top this
  obtain ⟨nGlobal, hGlobal⟩ :=
    withBot_enat_eq_nat_of_ne_bot_of_ne_top
      (x := Module.supportDim R M) hglobal_ne_bot hglobal_ne_top
  have hGlobalDepth : WithBot.some (moduleDepth R M : ℕ∞) = nGlobal := by
    calc
      WithBot.some (moduleDepth R M : ℕ∞) = Module.supportDim R M := by
        symm
        exact Module.CohenMacaulay.supportDim_eq_moduleDepth (R := R) (M := M)
      _ = nGlobal := hGlobal
  have hsupport_nat : nSuppLoc + nQuot ≤ nGlobal := by
    exact_mod_cast (show ((nSuppLoc + nQuot : ℕ) : WithBot ℕ∞) ≤ (nGlobal : WithBot ℕ∞) by
      simpa [hSuppLoc, hnQuot, hGlobal] using hsupport_split)
  have hdepth_nat : nGlobal ≤ nDepthLoc + nQuot := by
    exact_mod_cast
      (show (nGlobal : WithBot ℕ∞) ≤ ((nDepthLoc + nQuot : ℕ) : WithBot ℕ∞) by
        simpa [hGlobalDepth, hDepthLoc, hnQuot,
          add_comm, add_left_comm, add_assoc] using hdepth_split)
  have hcompare : nSuppLoc ≤ nDepthLoc := by
    omega
  -- Reduce both sides to natural representatives and cancel the common quotient dimension.
  rw [hSuppLoc, hDepthLoc]
  exact_mod_cast hcompare

/- Domain-style sampling:
* primary domain: Cohen-Macaulay modules over Noetherian local rings and their behavior under
  localization at a prime;
* sampled owner declarations of the same kind:
  `Module.CohenMacaulay`,
  `Module.CohenMacaulay.supportDim_eq_moduleDepth`,
  `Localization.AtPrime`,
  `LocalizedModule.AtPrime`;
* best owner abstraction: the chapter owner class `Module.CohenMacaulay`;
* primitive data: the ambient local Noetherian ring, the module structure on `M`, and the owner
  instance `[Module.CohenMacaulay R M]`;
* derived API: the equality `Module.supportDim R M = .some (moduleDepth R M)` and the inherited
  finiteness instance.

Source/core/bridge triage:
* `source-facing`: preservation of the Cohen-Macaulay condition under localization at a prime;
* `core/canonical`: the owner class `Module.CohenMacaulay` together with the canonical
  localization objects `Rₚ` and `Mₚ`;
* `bridge/view`: the equality `supportDim_eq_moduleDepth` extracted from the owner class.

The localized depth-equals-support-dimension equality is derived API from the owner class, so the
public statement should return `Module.CohenMacaulay Rₚ Mₚ` directly instead of restating that
equality as a parallel theorem. The Stacks statement is for any prime; with the current Lean owner
zero modules do not satisfy `Module.CohenMacaulay`, so the formal statement records the source
proof's nonzero-localization case by requiring `p` to lie in `Module.support R M`.
-/

-- Proof sketch: use Lemma `10.72.10` to bound the depth of `Mₚ` from below by the depth of `M`
-- minus `dim (R / p)`, and use Lemma `10.72.3` over `Rₚ` to bound the localized depth above by
-- the support dimension of `Mₚ`. Comparing these inequalities with
-- `supportDim_eq_moduleDepth` for `M` yields the Cohen-Macaulay equality for `Mₚ`.
/-- Lemma 10.103.11: if `M` is a Cohen-Macaulay finite module over a Noetherian local ring `R`,
then for any prime ideal `p` in the support of `M`, the localization `Mₚ` is Cohen-Macaulay over
`Rₚ`. -/
@[stacks 0AAG]
theorem localizedModule_atPrime
    (hpM : (⟨p, hp⟩ : PrimeSpectrum R) ∈ Module.support R M) :
    Module.CohenMacaulay Rₚ Mₚ := by
  letI : Nontrivial Mₚ := Module.mem_support_iff.mp hpM
  -- Route correction: stay on the textbook numerical route. First bound `Supp(Mₚ)` from above
  -- by the quotient-side dimension split, then combine it with the localized depth lower bound.
  refine ⟨le_antisymm ?_ ?_⟩
  · exact supportDim_le_moduleDepth_of_localized_split (R := R) (M := M) (p := p) hpM
  · exact depth_le_supportDim (R := Rₚ) (M := Mₚ)

end Module.CohenMacaulay

end
