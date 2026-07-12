import Mathlib
import StacksProject_2024.Chap10.Definition_10_104_6
import StacksProject_2024.Chap10.Definition_10_105_3
import StacksProject_2024.Chap05.Lemma_5_20_2
import StacksProject_2024.Chap10.Lemma_10_105_6
import StacksProject_2024.Chap10.Lemma_10_105_7
import StacksProject_2024.Chap10.Lemma_10_103_13
import StacksProject_2024.Chap10.Lemma_10_157_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped TensorProduct

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Helper for Chap10 Lemma 10 105 9: if `M` has full support over `R`, then every prime localization
`M_𝔭` still has full support over `R_𝔭`. -/
private lemma localized_support_eq_univ_of_support_eq_univ [Module.Finite R M]
    (hsupp : Module.support R M = Set.univ) (p : PrimeSpectrum R) :
    Module.support (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) =
      Set.univ := by
  ext q
  -- Detect support after localizing by contracting the prime back to `Spec R`.
  rw [Module.mem_support_localizationAtPrime_iff (R := R) (M := M) p q, hsupp]
  simp

/-- Helper for Chap10 Lemma 10 105 9: localizing the global hypotheses at a prime produces the local
source theorem input. -/
private theorem localized_cohenMacaulay_and_support_eq_univ
    (hCM : Module.LocallyCohenMacaulay R M) (hsupp : Module.support R M = Set.univ)
    (p : PrimeSpectrum R) :
    Module.CohenMacaulay (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) ∧
      Module.support (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) =
        Set.univ := by
  let _ : Module.Finite R M := hCM.toFinite
  constructor
  · -- The locally Cohen-Macaulay owner already packages the localized Cohen-Macaulay statement.
    exact hCM.localizedModule_cohenMacaulay p
  · -- Full support survives the same localization.
    exact localized_support_eq_univ_of_support_eq_univ (R := R) (M := M) hsupp p

/-- Helper for Chap10 Lemma 10 105 9: catenarity transports across ring equivalences. -/
private theorem isCatenaryRing_of_ringEquiv {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (e : A ≃+* B) [IsCatenaryRing A] :
    IsCatenaryRing B := by
  -- Transport the catenary-space owner across the induced homeomorphism of spectra.
  simpa [IsCatenaryRing] using
    (PrimeSpectrum.homeomorphOfRingEquiv e).catenarySpace

/-- Helper for Chap10 Lemma 10 105 9: Cohen-Macaulayness is unchanged by a linear equivalence
over the same local Noetherian ring. -/
private theorem cohenMacaulay_of_linearEquiv {A : Type u}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {N : Type v} {N' : Type*} [AddCommGroup N] [Module A N]
    [AddCommGroup N'] [Module A N'] (e : N ≃ₗ[A] N')
    [h : Module.CohenMacaulay A N] :
    Module.CohenMacaulay A N' := by
  let _ : Module.Finite A N' := Module.Finite.equiv e
  -- The defining support dimension and depth are invariant under the equivalence.
  exact ⟨by
    rw [← Module.supportDim_eq_of_equiv e, ← moduleDepth_eq_of_equiv e,
      h.supportDim_eq_moduleDepth]⟩

/-- Helper for Chap10 Lemma 10 105 9: full support survives arbitrary finite base change. -/
private lemma support_tensor_eq_univ_of_support_eq_univ
    {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
    (hsupp : Module.support A N = Set.univ) :
    Module.support S (S ⊗[A] N) = Set.univ := by
  -- Pull support back along the algebra map, then use that the source support is all of `Spec A`.
  rw [Module.Lemma_10_40_6, hsupp]
  ext q
  simp

/-- Helper for Chap10 Lemma 10 105 9: quotient by a prime has Krull dimension equal to the
coheight of the corresponding point of the prime spectrum. -/
private lemma primeQuotientKrullDim_eq_coheight
    {A : Type u} [CommRing A] (p : PrimeSpectrum A) :
    ringKrullDim (A ⧸ p.asIdeal) = (Order.coheight p : WithBot ℕ∞) := by
  -- Rewrite the quotient spectrum as the upper interval of primes containing `p`.
  rw [ringKrullDim_quotient]
  have hzero : PrimeSpectrum.zeroLocus (p.asIdeal : Set A) = Set.Ici p := by
    ext q
    change p.asIdeal ≤ q.asIdeal ↔ p ≤ q
    rfl
  rw [hzero]
  exact (Order.coheight_eq_krullDim_Ici p).symm

/-- Helper for Chap10 Lemma 10 105 9: the full-support Cohen-Macaulay dimension formula with a
module in an arbitrary universe, reduced to the already proved same-universe theorem by `ULift`. -/
private theorem ringKrullDim_eq_atPrime_add_quotient_of_fullSupportCohenMacaulay
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {N : Type v} [AddCommGroup N] [Module A N]
    (hCM : Module.CohenMacaulay A N) (hsupp : Module.support A N = Set.univ)
    (p : Ideal A) [p.IsPrime] :
    ringKrullDim A = ringKrullDim (Localization.AtPrime p) + ringKrullDim (A ⧸ p) := by
  let Au := ULift.{max u v, u} A
  let Nu := ULift.{max u v, v} N
  let eA : Au ≃+* A := ULift.ringEquiv
  let eN : Nu ≃ₗ[A] N := ULift.moduleEquiv
  letI : IsLocalRing Au := IsLocalRing.of_surjective' eA.symm.toRingHom eA.symm.surjective
  letI : IsNoetherianRing Au := isNoetherianRing_of_ringEquiv A eA.symm
  letI : Algebra Au A := eA.toRingHom.toAlgebra
  letI : Module Au Nu := Module.compHom Nu eA.toRingHom
  letI : IsScalarTower Au A Nu :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hCMNuA : Module.CohenMacaulay A Nu := by
    let _ : Module.CohenMacaulay A N := hCM
    exact cohenMacaulay_of_linearEquiv eN.symm
  have hsuppNuA : Module.support A Nu = Set.univ := by
    rw [LinearEquiv.support_eq eN]
    exact hsupp
  have hCMNuAu : Module.CohenMacaulay Au Nu := by
    let _ : Module.CohenMacaulay A Nu := hCMNuA
    have hTower : IsScalarTower Au A Nu :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    exact
      (@Module.cohenMacaulay_iff_restrictScalars_of_surjective
        Au A Nu inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
        inferInstance inferInstance inferInstance inferInstance hTower eA.surjective).1 hCMNuA
  have hsuppNuAu : Module.support Au Nu = Set.univ := by
    let _ : Module.CohenMacaulay Au Nu := hCMNuAu
    let _ : Module.CohenMacaulay A Nu := hCMNuA
    ext P
    constructor
    · intro _
      simp
    · intro _
      rw [Module.support_eq_zeroLocus]
      rw [PrimeSpectrum.mem_zeroLocus]
      intro x hxann
      have hPA_support :
          PrimeSpectrum.comap eA.symm.toRingHom P ∈ Module.support A Nu := by
        simp [hsuppNuA]
      rw [Module.support_eq_zeroLocus] at hPA_support
      have hleA : Module.annihilator A Nu ≤
          (PrimeSpectrum.comap eA.symm.toRingHom P).asIdeal := by
        simpa [PrimeSpectrum.mem_zeroLocus] using hPA_support
      have hxannAu : ∀ n : Nu, x • n = 0 := Module.mem_annihilator.mp hxann
      have hxannA : eA x ∈ Module.annihilator A Nu := by
        rw [Module.mem_annihilator]
        intro n
        simpa using hxannAu n
      have hxP : eA x ∈ Ideal.comap eA.symm.toRingHom P.asIdeal := hleA hxannA
      simpa using hxP
  let pU : Ideal Au := Ideal.comap eA.toRingHom p
  letI : pU.IsPrime := Ideal.comap_isPrime eA.toRingHom p
  have hformulaU :
      ringKrullDim Au =
        ringKrullDim (Localization.AtPrime pU) + ringKrullDim (Au ⧸ pU) := by
    -- Apply the same-universe theorem to the lifted ring and lifted module.
    exact
      ringKrullDim_eq_ringKrullDim_atPrime_add_ringKrullDim_quotient_of_full_support_cohenMacaulay
        (R := Au) (M := Nu) hCMNuAu hsuppNuAu pU
  have hring : ringKrullDim Au = ringKrullDim A :=
    ringKrullDim_eq_of_ringEquiv eA
  have hloc :
      ringKrullDim (Localization.AtPrime pU) =
        ringKrullDim (Localization.AtPrime p) := by
    let eLoc := Localization.localRingEquiv pU p eA rfl
    exact ringKrullDim_eq_of_ringEquiv eLoc
  have hp_map : p = Ideal.map eA.toRingHom pU := by
    simpa [pU] using (Ideal.map_comap_eq_self_of_equiv eA p).symm
  have hquot : ringKrullDim (Au ⧸ pU) = ringKrullDim (A ⧸ p) := by
    let eQuot := Ideal.quotientEquiv pU p eA hp_map
    exact ringKrullDim_eq_of_ringEquiv eQuot
  -- Transport the lifted dimension formula back through the ring, localization, and quotient
  -- equivalences.
  calc
    ringKrullDim A = ringKrullDim Au := hring.symm
    _ = ringKrullDim (Localization.AtPrime pU) + ringKrullDim (Au ⧸ pU) := hformulaU
    _ = ringKrullDim (Localization.AtPrime p) + ringKrullDim (A ⧸ p) := by
      rw [hloc, hquot]

/-- Helper for Chap10 Lemma 10 105 9: the prime-quotient dimension expression strictly decreases
under proper specialization in finite Krull dimension. -/
private lemma primeQuotientKrullDimension_strict_of_specializes
    {A : Type u} [CommRing A] [FiniteRingKrullDim A] {p q : PrimeSpectrum A}
    (hpq : p ⤳ q) (hpq_ne : p ≠ q) :
    (((ringKrullDim (A ⧸ p.asIdeal)).unbotD 0).toNat : ℤ) >
      (((ringKrullDim (A ⧸ q.asIdeal)).unbotD 0).toNat : ℤ) := by
  -- Replace quotient dimensions by coheights and use strict antitonicity of coheight.
  have hpq_lt : p < q :=
    lt_of_le_of_ne ((PrimeSpectrum.le_iff_specializes p q).2 hpq) hpq_ne
  have hq_fin : Order.coheight q < ⊤ := by
    have hq_le :
        ((Order.coheight q : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim A :=
      Order.coheight_le_krullDim q
    have hq_lt :
        ((Order.coheight q : ℕ∞) : WithBot ℕ∞) <
          ((⊤ : ℕ∞) : WithBot ℕ∞) :=
      lt_of_le_of_lt hq_le (ringKrullDim_lt_top (R := A))
    exact WithBot.coe_lt_coe.mp hq_lt
  have hp_fin : Order.coheight p < ⊤ := by
    have hp_le :
        ((Order.coheight p : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim A :=
      Order.coheight_le_krullDim p
    have hp_lt :
        ((Order.coheight p : ℕ∞) : WithBot ℕ∞) <
          ((⊤ : ℕ∞) : WithBot ℕ∞) :=
      lt_of_le_of_lt hp_le (ringKrullDim_lt_top (R := A))
    exact WithBot.coe_lt_coe.mp hp_lt
  have hcoheight : Order.coheight q < Order.coheight p :=
    Order.coheight_strictAnti hpq_lt hq_fin
  have hnat : (Order.coheight q).toNat < (Order.coheight p).toNat := by
    rw [← ENat.coe_lt_coe, ENat.coe_toNat hq_fin.ne, ENat.coe_toNat hp_fin.ne]
    exact hcoheight
  have hpdim := primeQuotientKrullDim_eq_coheight (A := A) p
  have hqdim := primeQuotientKrullDim_eq_coheight (A := A) q
  rw [hpdim, hqdim]
  simp only [WithBot.unbotD_coe]
  exact_mod_cast hnat

/-- Helper for Chap10 Lemma 10 105 9: the Krull dimension of a Noetherian local ring is a
natural number. -/
private lemma ringKrullDim_eq_nat_of_local_noetherian_ring
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    ∃ n : ℕ, ringKrullDim A = n := by
  -- Convert the finite local Krull dimension into its natural-number representative.
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

/-- Helper for Chap10 Lemma 10 105 9: a point covered by the top element has coheight one. -/
private lemma coheight_eq_one_of_covBy_top {α : Type*} [PartialOrder α] [OrderTop α]
    {x : α} (hcov : x ⋖ (⊤ : α)) (hfin : Order.coheight x < ⊤) :
    Order.coheight x = (1 : ℕ) := by
  -- Use the recursive characterization of finite coheight and the cover relation with `⊤`.
  rw [Order.coheight_eq_coe_iff]
  refine ⟨hfin, ?_, ?_⟩
  · right
    exact ⟨⊤, hcov.lt, by simp⟩
  · intro y hy
    have hy_top : y = ⊤ := by
      rcases hcov.eq_or_eq hy.le le_top with hyx | hytop
      · exact (hy.ne hyx.symm).elim
      · exact hytop
    simp [hy_top]

/-- Helper for Chap10 Lemma 10 105 9: after localizing at the upper prime of an immediate
specialization, the quotient by the lower prime has Krull dimension one. -/
private lemma localizedQuotientKrullDim_eq_one_of_immediateSpecialization
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {p q : PrimeSpectrum A} (hpq : IsImmediateSpecialization p q) :
    let pq : PrimeSpectrum (Localization.AtPrime q.asIdeal) :=
      (IsLocalization.AtPrime.primeSpectrumOrderIso
          (Localization.AtPrime q.asIdeal) q.asIdeal).symm
        ⟨p, (PrimeSpectrum.le_iff_specializes p q).2 hpq.specializes⟩
    ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸ pq.asIdeal) = 1 := by
  intro pq
  let Lq := Localization.AtPrime q.asIdeal
  let e := IsLocalization.AtPrime.primeSpectrumOrderIso Lq q.asIdeal
  have hp_le_q : p ≤ q := (PrimeSpectrum.le_iff_specializes p q).2 hpq.specializes
  have hp_lt_q : p < q := lt_of_le_of_ne hp_le_q hpq.ne
  have hq_mem_iic : q ∈ Set.Iic q := by simp
  have hpq_cov : p ⋖ q := by
    refine covBy_of_eq_or_eq hp_lt_q ?_
    intro r hpr hrq
    have hpr' : p ⤳ r := (PrimeSpectrum.le_iff_specializes p r).1 hpr
    have hrq' : r ⤳ q := (PrimeSpectrum.le_iff_specializes r q).1 hrq
    exact hpq.eq_or_eq hpr' hrq'
  have hcov_sub : (⟨p, hp_le_q⟩ : Set.Iic q) ⋖ ⟨q, hq_mem_iic⟩ := by
    refine covBy_of_eq_or_eq ?_ ?_
    · exact hp_lt_q
    · intro r hpr hrq
      rcases hpq_cov.eq_or_eq hpr hrq with h | h
      · left
        exact Subtype.ext h
      · right
        exact Subtype.ext h
  have htop : e (⊤ : PrimeSpectrum Lq) = ⟨q, hq_mem_iic⟩ := by
    apply Subtype.ext
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap A Lq) (IsLocalRing.maximalIdeal Lq) = q.asIdeal
    exact IsLocalization.AtPrime.comap_maximalIdeal Lq q.asIdeal
  have hpq_apply : e pq = ⟨p, hp_le_q⟩ := by
    change
      (IsLocalization.AtPrime.primeSpectrumOrderIso Lq q.asIdeal)
          ((IsLocalization.AtPrime.primeSpectrumOrderIso Lq q.asIdeal).symm
            ⟨p, hp_le_q⟩) =
        ⟨p, hp_le_q⟩
    exact (IsLocalization.AtPrime.primeSpectrumOrderIso Lq q.asIdeal).apply_symm_apply
      ⟨p, hp_le_q⟩
  have hcov_pq_top : pq ⋖ (⊤ : PrimeSpectrum Lq) := by
    -- Transport the ambient cover `p ⋖ q` through the localized spectrum order isomorphism.
    apply (apply_covBy_apply_iff e).mp
    simpa [hpq_apply, htop] using hcov_sub
  have hfin : Order.coheight pq < ⊤ := by
    have hpq_le : ((Order.coheight pq : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim Lq :=
      Order.coheight_le_krullDim pq
    have hpq_lt : ((Order.coheight pq : ℕ∞) : WithBot ℕ∞) <
        ((⊤ : ℕ∞) : WithBot ℕ∞) :=
      lt_of_le_of_lt hpq_le (ringKrullDim_lt_top (R := Lq))
    exact WithBot.coe_lt_coe.mp hpq_lt
  have hcoh : Order.coheight pq = (1 : ℕ) :=
    coheight_eq_one_of_covBy_top hcov_pq_top hfin
  -- Quotient dimension is coheight, and the localized lower prime has coheight one.
  rw [primeQuotientKrullDim_eq_coheight (A := Lq) pq, hcoh]
  norm_num

/-- Helper for Chap10 Lemma 10 105 9: local dimension increases by one across an immediate
specialization under the full-support Cohen-Macaulay dimension formula. -/
private lemma localizedRingKrullDim_eq_add_one_of_immediateSpecialization
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {N : Type v} [AddCommGroup N] [Module A N]
    (hCM : Module.CohenMacaulay A N) (hsupp : Module.support A N = Set.univ)
    {p q : PrimeSpectrum A} (hpq : IsImmediateSpecialization p q) :
    ringKrullDim (Localization.AtPrime q.asIdeal) =
      ringKrullDim (Localization.AtPrime p.asIdeal) + 1 := by
  let _ : Module.Finite A N := hCM.toFinite
  let Lq := Localization.AtPrime q.asIdeal
  let Nq := LocalizedModule.AtPrime q.asIdeal N
  have hp_le_q : p ≤ q := (PrimeSpectrum.le_iff_specializes p q).2 hpq.specializes
  let pq : PrimeSpectrum Lq :=
    (IsLocalization.AtPrime.primeSpectrumOrderIso Lq q.asIdeal).symm ⟨p, hp_le_q⟩
  have hLCM : Module.LocallyCohenMacaulay A N := by
    let _ : Module.CohenMacaulay A N := hCM
    exact Module.locallyCohenMacaulay_of_cohenMacaulay A N hsupp
  have hCMq : Module.CohenMacaulay Lq Nq :=
    hLCM.localizedModule_cohenMacaulay q
  have hsuppq : Module.support Lq Nq = Set.univ :=
    localized_support_eq_univ_of_support_eq_univ (R := A) (M := N) hsupp q
  have hformula :
      ringKrullDim Lq =
        ringKrullDim (Localization.AtPrime pq.asIdeal) + ringKrullDim (Lq ⧸ pq.asIdeal) := by
    -- Apply the full-support Cohen-Macaulay dimension formula inside the upper-prime localization.
    exact
      ringKrullDim_eq_atPrime_add_quotient_of_fullSupportCohenMacaulay
        (A := Lq) (N := Nq) hCMq hsuppq pq.asIdeal
  have hquot : ringKrullDim (Lq ⧸ pq.asIdeal) = 1 := by
    simpa [Lq, pq] using
      localizedQuotientKrullDim_eq_one_of_immediateSpecialization
        (A := A) (p := p) (q := q) hpq
  have hpq_comap : Ideal.comap (algebraMap A Lq) pq.asIdeal = p.asIdeal := by
    have hpq_point : PrimeSpectrum.comap (algebraMap A Lq) pq = p := by
      change ((IsLocalization.AtPrime.primeSpectrumOrderIso Lq q.asIdeal) pq).1 = p
      simp [pq]
    simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hpq_point
  have hiter :
      ringKrullDim (Localization.AtPrime pq.asIdeal) =
        ringKrullDim (Localization.AtPrime p.asIdeal) := by
    let eDouble :=
      IsLocalization.localizationLocalizationAtPrimeIsoLocalization
        (M := q.asIdeal.primeCompl) pq.asIdeal
    have hiter0 :
        ringKrullDim (Localization.AtPrime pq.asIdeal) =
          ringKrullDim
            (Localization.AtPrime (Ideal.comap (algebraMap A Lq) pq.asIdeal)) := by
      exact (ringKrullDim_eq_of_ringEquiv eDouble.toRingEquiv).symm
    let Icomap : Ideal A := Ideal.comap (algebraMap A Lq) pq.asIdeal
    letI : Icomap.IsPrime := Ideal.comap_isPrime (algebraMap A Lq) pq.asIdeal
    have htarget :
        ringKrullDim (Localization.AtPrime Icomap) =
          ringKrullDim (Localization.AtPrime p.asIdeal) := by
      let eEq : Localization.AtPrime Icomap ≃+* Localization.AtPrime p.asIdeal :=
        Localization.localRingEquiv Icomap p.asIdeal (RingEquiv.refl A) (by
          simpa [Icomap] using hpq_comap)
      exact ringKrullDim_eq_of_ringEquiv eEq
    exact hiter0.trans htarget
  -- The localized formula now reads `dim A_q = dim A_p + 1`.
  rw [hquot, hiter] at hformula
  exact hformula

/-- Helper for Chap10 Lemma 10 105 9: the prime-quotient dimension drops by exactly one along an
immediate specialization for full-support Cohen-Macaulay modules over local rings. -/
private lemma primeQuotientKrullDimension_eq_add_one_of_immediateSpecialization
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {N : Type v} [AddCommGroup N] [Module A N]
    (hCM : Module.CohenMacaulay A N) (hsupp : Module.support A N = Set.univ)
    {p q : PrimeSpectrum A} (hpq : IsImmediateSpecialization p q) :
    (((ringKrullDim (A ⧸ p.asIdeal)).unbotD 0).toNat : ℤ) =
      (((ringKrullDim (A ⧸ q.asIdeal)).unbotD 0).toNat : ℤ) + 1 := by
  obtain ⟨dA, hA⟩ := ringKrullDim_eq_nat_of_local_noetherian_ring (A := A)
  obtain ⟨dpLoc, hpLoc⟩ :=
    ringKrullDim_eq_nat_of_local_noetherian_ring
      (A := Localization.AtPrime p.asIdeal)
  obtain ⟨dqLoc, hqLoc⟩ :=
    ringKrullDim_eq_nat_of_local_noetherian_ring
      (A := Localization.AtPrime q.asIdeal)
  letI : IsLocalRing (A ⧸ p.asIdeal) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p.asIdeal) Ideal.Quotient.mk_surjective
  letI : IsLocalRing (A ⧸ q.asIdeal) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk q.asIdeal) Ideal.Quotient.mk_surjective
  obtain ⟨dpQuot, hpQuot⟩ :=
    ringKrullDim_eq_nat_of_local_noetherian_ring (A := A ⧸ p.asIdeal)
  obtain ⟨dqQuot, hqQuot⟩ :=
    ringKrullDim_eq_nat_of_local_noetherian_ring (A := A ⧸ q.asIdeal)
  have hpFormula :
    ringKrullDim A =
        ringKrullDim (Localization.AtPrime p.asIdeal) + ringKrullDim (A ⧸ p.asIdeal) :=
    ringKrullDim_eq_atPrime_add_quotient_of_fullSupportCohenMacaulay
      (A := A) (N := N) hCM hsupp p.asIdeal
  have hqFormula :
      ringKrullDim A =
        ringKrullDim (Localization.AtPrime q.asIdeal) + ringKrullDim (A ⧸ q.asIdeal) :=
    ringKrullDim_eq_atPrime_add_quotient_of_fullSupportCohenMacaulay
      (A := A) (N := N) hCM hsupp q.asIdeal
  have hLoc :
      ringKrullDim (Localization.AtPrime q.asIdeal) =
        ringKrullDim (Localization.AtPrime p.asIdeal) + 1 :=
    localizedRingKrullDim_eq_add_one_of_immediateSpecialization
      (A := A) (N := N) hCM hsupp hpq
  have hpNat : dA = dpLoc + dpQuot := by
    have hpNatWB : ((dA : ℕ∞) : WithBot ℕ∞) =
        ((dpLoc + dpQuot : ℕ) : WithBot ℕ∞) := by
      simpa [hA, hpLoc, hpQuot] using hpFormula
    exact_mod_cast hpNatWB
  have hqNat : dA = dqLoc + dqQuot := by
    have hqNatWB : ((dA : ℕ∞) : WithBot ℕ∞) =
        ((dqLoc + dqQuot : ℕ) : WithBot ℕ∞) := by
      simpa [hA, hqLoc, hqQuot] using hqFormula
    exact_mod_cast hqNatWB
  have hLocNat : dqLoc = dpLoc + 1 := by
    have hLocNatWB : ((dqLoc : ℕ∞) : WithBot ℕ∞) =
        ((dpLoc + 1 : ℕ) : WithBot ℕ∞) := by
      simpa [hqLoc, hpLoc] using hLoc
    exact_mod_cast hLocNatWB
  have hQuotNat : dpQuot = dqQuot + 1 := by
    -- Cancel the common local dimension from the two dimension-formula equalities.
    omega
  have hpUnbot :
      (ringKrullDim (A ⧸ p.asIdeal)).unbotD 0 = (dpQuot : ℕ∞) := by
    rw [hpQuot]
    exact WithBot.unbotD_coe 0 (dpQuot : ℕ∞)
  have hqUnbot :
      (ringKrullDim (A ⧸ q.asIdeal)).unbotD 0 = (dqQuot : ℕ∞) := by
    rw [hqQuot]
    exact WithBot.unbotD_coe 0 (dqQuot : ℕ∞)
  rw [hpUnbot, hqUnbot]
  simp only [ENat.toNat_coe]
  exact_mod_cast hQuotNat

/-- Helper for Chap10 Lemma 10 105 9: prime-quotient Krull dimension is a dimension function for
a full-support Cohen-Macaulay module over a Noetherian local ring. -/
private lemma primeQuotientKrullDimension_isDimensionFunction_of_fullSupportCohenMacaulay
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {N : Type v} [AddCommGroup N] [Module A N]
    (hCM : Module.CohenMacaulay A N) (hsupp : Module.support A N = Set.univ) :
    IsDimensionFunction
      (fun p : PrimeSpectrum A ↦
        (((ringKrullDim (A ⧸ p.asIdeal)).unbotD 0).toNat : ℤ)) where
  strict_of_specializes := by
    intro p q hpq hpq_ne
    -- Proper specialization is the already-proved strict coheight decrease.
    exact primeQuotientKrullDimension_strict_of_specializes hpq hpq_ne
  eq_add_one_of_immediateSpecialization := by
    intro p q hpq
    -- Immediate specialization is the exact one-step drop isolated above.
    exact
      primeQuotientKrullDimension_eq_add_one_of_immediateSpecialization
        (A := A) (N := N) hCM hsupp hpq

/-- Helper for Chap10 Lemma 10 105 9: a dimension function given by prime-quotient dimensions
forces catenarity of a Noetherian local ring. -/
private theorem isCatenaryRing_of_primeQuotientKrullDimension_isDimensionFunction
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hdim :
      IsDimensionFunction
        (fun p : PrimeSpectrum A ↦
          (((ringKrullDim (A ⧸ p.asIdeal)).unbotD 0).toNat : ℤ))) :
    IsCatenaryRing A := by
  -- The topological criterion from Lemma 5.20.2 turns the dimension function into catenarity of
  -- `Spec A`, which is the ring-level catenary predicate.
  rw [isCatenaryRing_iff_catenarySpace_primeSpectrum]
  exact hdim.catenarySpace

/-- Helper for Chap10 Lemma 10 105 9: a Noetherian local ring carrying a full-support
Cohen-Macaulay module is catenary. -/
private theorem isCatenaryRing_of_cohenMacaulay_of_support_eq_univ_local
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {N : Type v} [AddCommGroup N] [Module A N]
    (hCM : Module.CohenMacaulay A N) (hsupp : Module.support A N = Set.univ) :
    IsCatenaryRing A := by
  -- Package the quotient-dimension function, then apply the topological catenarity criterion.
  exact
    isCatenaryRing_of_primeQuotientKrullDimension_isDimensionFunction
      (primeQuotientKrullDimension_isDimensionFunction_of_fullSupportCohenMacaulay
        (A := A) (N := N) hCM hsupp)

/-- Helper for Chap10 Lemma 10 105 9: a prime localization is catenary when a locally
Cohen-Macaulay module has full support before localization. -/
private theorem isCatenaryRing_localizationAtPrime_of_locallyCohenMacaulay_support_eq_univ
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {N : Type v} [AddCommGroup N] [Module A N]
    (hLCM : Module.LocallyCohenMacaulay A N) (hsupp : Module.support A N = Set.univ)
    (q : PrimeSpectrum A) :
    IsCatenaryRing (Localization.AtPrime q.asIdeal) := by
  let _ : Module.Finite A N := hLCM.toFinite
  have hCMq :
      Module.CohenMacaulay (Localization.AtPrime q.asIdeal)
        (LocalizedModule.AtPrime q.asIdeal N) :=
    hLCM.localizedModule_cohenMacaulay q
  have hsuppq :
      Module.support (Localization.AtPrime q.asIdeal)
          (LocalizedModule.AtPrime q.asIdeal N) =
        Set.univ :=
    localized_support_eq_univ_of_support_eq_univ (R := A) (M := N) hsupp q
  -- The localized Cohen-Macaulay module now satisfies the local full-support catenarity
  -- criterion.
  exact
    isCatenaryRing_of_cohenMacaulay_of_support_eq_univ_local
      (A := Localization.AtPrime q.asIdeal) (N := LocalizedModule.AtPrime q.asIdeal N)
      hCMq hsuppq

/-- Helper for Chap10 Lemma 10 105 9: over a Noetherian local ring, the polynomial ring is catenary once
the base admits a Cohen-Macaulay module with full support. -/
private theorem isCatenaryRing_mvPolynomial_of_cohenMacaulay_of_support_eq_univ_local
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {N : Type v} [AddCommGroup N] [Module A N]
    (hCM : Module.CohenMacaulay A N) (hsupp : Module.support A N = Set.univ) (n : ℕ) :
    IsCatenaryRing (MvPolynomial (Fin n) A) := by
  let _ : Module.Finite A N := hCM.toFinite
  let S := MvPolynomial (Fin n) A
  let P := S ⊗[A] N
  have hLCM : Module.LocallyCohenMacaulay A N := by
    let _ : Module.CohenMacaulay A N := hCM
    exact Module.locallyCohenMacaulay_of_cohenMacaulay A N hsupp
  have hLCMP : Module.LocallyCohenMacaulay S P :=
    Module.LocallyCohenMacaulay.mvPolynomial hLCM n
  have hsuppP :=
    support_tensor_eq_univ_of_support_eq_univ
      (A := A) (S := S) (N := N) hsupp
  let _ : Module.Finite S P := hLCMP.toFinite
  -- Check catenarity after localizing the polynomial ring at each prime.
  refine ((isCatenaryRing_localization_tfae (R := S)).out 1 0 rfl rfl).mp ?_
  intro q
  -- Each localized polynomial ring is handled by the prime-local criterion just isolated.
  exact
    isCatenaryRing_localizationAtPrime_of_locallyCohenMacaulay_support_eq_univ
      (A := S) (N := P) hLCMP hsuppP q

/-- Helper for Chap10 Lemma 10 105 9: over a Noetherian local ring, a Cohen-Macaulay module with full
support forces the ring to be universally catenary. -/
private theorem universallyCatenaryRing_of_cohenMacaulay_of_support_eq_univ_local
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {N : Type v} [AddCommGroup N] [Module A N]
    (hCM : Module.CohenMacaulay A N) (hsupp : Module.support A N = Set.univ) :
    UniversallyCatenaryRing A := by
  let _ : Module.Finite A N := hCM.toFinite
  refine { catenary_of_finiteType := ?_ }
  intro B _ _ _
  obtain ⟨n, π, hπsurj⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := A) (S := B)).mp inferInstance
  let S := MvPolynomial (Fin n) A
  letI : IsCatenaryRing S :=
    isCatenaryRing_mvPolynomial_of_cohenMacaulay_of_support_eq_univ_local
      (A := A) (N := N) hCM hsupp n
  letI : IsCatenaryRing (S ⧸ RingHom.ker π) :=
    quotient_catenaryRing (R := S) (I := RingHom.ker π)
  let e : S ⧸ RingHom.ker π ≃+* B := RingHom.quotientKerEquivOfSurjective hπsurj
  -- Present the finite-type algebra as a quotient of a catenary polynomial ring.
  exact isCatenaryRing_of_ringEquiv e

/-
Domain-style sampling in the Cohen-Macaulay / universal-catenarity interface:
- sampled owner declarations:
  `Module.LocallyCohenMacaulay`,
  `CohenMacaulayRing`,
  `UniversallyCatenaryRing`,
  `Module.support_of_algebra`;
- best owner abstraction: the main theorem is a `bridge/view` from the chapter owner
  `Module.LocallyCohenMacaulay R M` plus full support to `UniversallyCatenaryRing R`;
- primitive data: `hCM : Module.LocallyCohenMacaulay R M` and
  `hsupp : Module.support R M = Set.univ`;
- derived API: the Cohen-Macaulay-ring corollary, obtained by specializing to the self-module
  `R`.

Source/core/bridge triage:
* source-facing: Lemma `10.105.9` itself, expressing the textbook criterion via a
  Cohen-Macaulay module with full support;
* core/canonical: the owner classes `Module.LocallyCohenMacaulay` and
  `UniversallyCatenaryRing`;
* bridge/view: the self-module specialization through `CohenMacaulayRing`.
-/
-- Proof sketch: localize at an arbitrary prime `p` of `R`. The localized module remains
-- Cohen-Macaulay and still has full support, so Lemmas `10.103.13` and `10.103.9` show that each
-- polynomial localization over `Rₚ` has prime chains of the expected length. Applying
-- Lemma `10.104.7` to polynomial algebras and then the localization criterion for universal
-- catenarity yields the conclusion.
/-- Chap10 Lemma 10 105 9: more generally, if `R` is a Noetherian ring and `M` is a Cohen-Macaulay
`R`-module whose support is all of `Spec R`, then `R` is universally catenary. -/
@[stacks 00NM]
theorem universallyCatenaryRing_of_support_eq_univ_of_locallyCohenMacaulay
    (hCM : Module.LocallyCohenMacaulay R M) (hsupp : Module.support R M = Set.univ) :
    UniversallyCatenaryRing R := by
  let _ : Module.Finite R M := hCM.toFinite
  -- Reduce universal catenarity to the prime-local criterion from Lemma `10.105.6`.
  refine ((universallyCatenaryRing_localization_tfae (R := R)).out 1 0 rfl rfl).mp ?_
  intro p
  -- Each prime localization now matches the remaining local theorem.
  obtain ⟨hCMp, hsuppp⟩ :=
    localized_cohenMacaulay_and_support_eq_univ (R := R) (M := M) hCM hsupp p
  exact universallyCatenaryRing_of_cohenMacaulay_of_support_eq_univ_local hCMp hsuppp

end

section

variable {R : Type u} [CommRing R]

-- Proof sketch: apply the general theorem to the self-module `R`. A Cohen-Macaulay ring gives the
-- required local Cohen-Macaulay property for `R`, and the support of the self-module is all of
-- `Spec R`. The theorem header does not repeat a separate `[IsNoetherianRing R]` assumption,
-- since that primitive data already belongs to the owner class `CohenMacaulayRing R`.
/-- A Noetherian Cohen-Macaulay ring is universally catenary. -/
theorem universallyCatenaryRing_of_cohenMacaulayRing (hCM : CohenMacaulayRing R) :
    UniversallyCatenaryRing R := by
  let _ : CohenMacaulayRing R := hCM
  have hker : RingHom.ker (RingHom.id R) = (⊥ : Ideal R) := by
    ext x
    simp
  have hsupp : Module.support R R = Set.univ := by
    simpa [hker, PrimeSpectrum.zeroLocus_bot] using
      (show Module.support R R = PrimeSpectrum.zeroLocus (RingHom.ker (algebraMap R R)) from
        Module.support_of_algebra)
  exact universallyCatenaryRing_of_support_eq_univ_of_locallyCohenMacaulay
    hCM.toLocallyCohenMacaulay hsupp

end
