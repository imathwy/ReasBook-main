import Mathlib
import StacksProject_2024.Chap10.Lemma_10_39_15
import StacksProject_2024.Chap10.Lemma_10_39_18
import StacksProject_2024.Chap10.Lemma_10_40_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open PrimeSpectrum
open TensorProduct.AlgebraTensorModule
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section

variable {R : Type u} {S : Type v} {N : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
variable [Module.Finite S N] [Module.Flat R N]

namespace Module

/-- Helper for Lemma 10.41.12: a nonzero module over a local `B` remains supported at the closed
point after contracting along a local ring map `A → B`. -/
lemma closedPoint_mem_support_of_nontrivial_of_local_map
    {A : Type*} {B : Type*} {M : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    [Nontrivial M] :
    IsLocalRing.closedPoint A ∈ Module.support A M := by
  -- The closed point of `B` lies in the support of any nonzero `B`-module, and support contracts
  -- along the local map.
  have hclosedB : IsLocalRing.closedPoint B ∈ Module.support B M := by
    simpa using IsLocalRing.closedPoint_mem_support B M
  have hpre :=
    Module.support_subset_preimage_comap
      (R := A) (A := B) (M := M) hclosedB
  simpa [IsLocalRing.comap_closedPoint (algebraMap A B)] using hpre

/-- Helper for Lemma 10.41.12: support of a localized module descends to support of the original
module after contracting the prime along the localization map. -/
lemma mem_support_comap_of_mem_support_localized_atPrime
    (q' : PrimeSpectrum S) {Q : PrimeSpectrum (Localization.AtPrime q'.asIdeal)}
    (hQ : Q ∈ Module.support (Localization.AtPrime q'.asIdeal)
      (LocalizedModule.AtPrime q'.asIdeal N)) :
    PrimeSpectrum.comap (algebraMap S (Localization.AtPrime q'.asIdeal)) Q ∈
      Module.support S N := by
  -- Rewrite support through the localized tensor-product model, then descend support by the
  -- canonical base-change theorem for finite modules.
  let e :=
    LocalizedModule.equivTensorProduct q'.asIdeal.primeCompl N
  have hsupp :
      Module.support (Localization.AtPrime q'.asIdeal) (LocalizedModule.AtPrime q'.asIdeal N) =
        Module.support (Localization.AtPrime q'.asIdeal)
          ((Localization.AtPrime q'.asIdeal) ⊗[S] N) :=
    LinearEquiv.support_eq (R := Localization.AtPrime q'.asIdeal) e
  have hQ' : Q ∈ Module.support (Localization.AtPrime q'.asIdeal)
      ((Localization.AtPrime q'.asIdeal) ⊗[S] N) := by
    exact hsupp ▸ hQ
  have hbase :
      Q ∈ PrimeSpectrum.comap (algebraMap S (Localization.AtPrime q'.asIdeal)) ⁻¹'
        Module.support S N := by
    simpa [Module.Lemma_10_40_6 (R := S) (R' := Localization.AtPrime q'.asIdeal) (M := N)]
      using hQ'
  exact hbase

section

omit [Module R N] [IsScalarTower R S N] [Module.Flat R N]

/-- Helper for Lemma 10.41.12: after localizing at `q' ∈ Supp(N)`, quotienting by the maximal
ideal of the localized base ring `R_(q' ∩ R)` stays nontrivial. -/
lemma localized_target_quotient_nontrivial
    (q' : Module.support S N) :
    let A := Localization.AtPrime ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
    let B := Localization.AtPrime q'.1.asIdeal
    let M := LocalizedModule.AtPrime q'.1.asIdeal N
    let _ : Algebra A B :=
      (Localization.localRingHom ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
        q'.1.asIdeal (algebraMap R S) rfl).toAlgebra
    let _ : Module A M :=
      Module.compHom M
        (Localization.localRingHom ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
          q'.1.asIdeal (algebraMap R S) rfl)
    let _ : IsScalarTower A B M := IsScalarTower.restrictScalars A B M
    Nontrivial (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))) := by
  let A := Localization.AtPrime ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
  let B := Localization.AtPrime q'.1.asIdeal
  let M := LocalizedModule.AtPrime q'.1.asIdeal N
  let f :=
    Localization.localRingHom ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
      q'.1.asIdeal (algebraMap R S) rfl
  letI : Algebra A B := f.toAlgebra
  letI : Module A M := Module.compHom M f
  letI : IsScalarTower A B M := IsScalarTower.restrictScalars A B M
  letI : IsLocalHom (algebraMap A B) := by
    -- The localized map `R_(q' ∩ R) → S_q'` is local, so maximal ideals contract correctly.
    simpa [f] using
      Localization.isLocalHom_localRingHom
        ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal) q'.1.asIdeal
        (algebraMap R S) rfl
  have hnontrivialM : Nontrivial M := by
    -- Support membership says exactly that the localization `N_q'` is nonzero.
    simpa [M] using (Module.mem_support_iff.mp q'.2)
  letI : Nontrivial M := hnontrivialM
  let PB : Submodule B M := IsLocalRing.maximalIdeal B • (⊤ : Submodule B M)
  have hquotB : Nontrivial (M ⧸ PB) := by
    -- Nakayama over the local ring `B = S_q'` rules out `maximalIdeal B • M = M`.
    have hPB : PB ≠ ⊤ := by
      dsimp [PB]
      simpa [ne_comm] using
        (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
          (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator B M)))
    exact Submodule.Quotient.nontrivial_iff.2 hPB
  have hquotB_A : Nontrivial (M ⧸ PB.restrictScalars A) := by
    -- Restrict scalars on the quotient so the later factor map lives over `A`.
    exact (Submodule.Quotient.restrictScalarsEquiv A PB).surjective.nontrivial
  have hsmulA_le :
      IsLocalRing.maximalIdeal A • (⊤ : Submodule A M) ≤ PB.restrictScalars A := by
    -- Route correction: instead of comparing mixed-base tensors, contract the maximal ideal of `A`
    -- into the maximal ideal of `B` and compare the two quotient modules.
    refine Submodule.smul_le.2 fun a ha m hm ↦ ?_
    change a • m ∈ PB.restrictScalars A
    change a • m ∈ PB
    dsimp [PB]
    rw [← IsScalarTower.algebraMap_smul B a m]
    have hmem_map :
        algebraMap A B a ∈ Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) :=
      Ideal.mem_map_of_mem _ ha
    have hmem :
        algebraMap A B a ∈ IsLocalRing.maximalIdeal B :=
      (IsLocalRing.map_maximalIdeal_le (algebraMap A B)) hmem_map
    exact Submodule.smul_mem_smul hmem (by simpa using hm)
  -- The quotient by `maximalIdeal A` surjects onto the already nontrivial quotient by
  -- `maximalIdeal B`, so the source quotient is nontrivial as well.
  exact (Submodule.factor_surjective hsmulA_le).nontrivial

/-- Helper for Lemma 10.41.12: the canonical fiber module over a prime is the residue-field
tensor of the module. -/
private noncomputable def fiber_module_linearEquiv
    {A : Type*} {B : Type*} {M : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    (p : PrimeSpectrum A) :
    (p.asIdeal.Fiber B) ⊗[B] M ≃ₗ[B] M ⊗[A] p.asIdeal.ResidueField :=
  TensorProduct.comm B (p.asIdeal.Fiber B) M ≪≫ₗ
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B M)
      (Algebra.TensorProduct.commRight A B p.asIdeal.ResidueField).symm.toLinearEquiv
      ≪≫ₗ
    cancelBaseChange A B B M p.asIdeal.ResidueField

/-- Helper for Lemma 10.41.12: nontriviality of the `κ(p)`-fiber of a localized module yields a
nontrivial module over the corresponding fiber ring. -/
lemma nontrivial_fiber_ring_tensor_of_nontrivial_prime_residue_tensor
    {A : Type*} {B : Type*} {M : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    (p : PrimeSpectrum A)
    (h : Nontrivial (p.asIdeal.ResidueField ⊗[A] M)) :
    Nontrivial ((p.asIdeal.Fiber B) ⊗[B] M) := by
  let K := p.asIdeal.ResidueField
  -- First rewrite the given fiber in the tensor order used by the canonical fiber-module model.
  have hcomm : Nontrivial (M ⊗[A] K) := by
    exact (TensorProduct.comm A K M).nontrivial_congr.mp h
  -- Then transport nontriviality through the standard fiber-module comparison.
  let e := fiber_module_linearEquiv (A := A) (B := B) (M := M) p
  exact e.nontrivial_congr.mpr hcomm

/-- Helper for Lemma 10.41.12: after localizing at `q' ∈ Supp(N)`, the closed fiber over
`R_(q' ∩ R)` is nontrivial, expressed as the quotient by the maximal ideal. -/
lemma nontrivial_closed_fiber_at_localized_target
    (q' : Module.support S N) :
    let A := Localization.AtPrime ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
    let B := Localization.AtPrime q'.1.asIdeal
    let M := LocalizedModule.AtPrime q'.1.asIdeal N
    let _ : Algebra A B :=
      (Localization.localRingHom ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
        q'.1.asIdeal (algebraMap R S) rfl).toAlgebra
    let _ : Module A M :=
      Module.compHom M
        (Localization.localRingHom ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
          q'.1.asIdeal (algebraMap R S) rfl)
    let _ : IsScalarTower A B M := IsScalarTower.restrictScalars A B M
    Nontrivial (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))) := by
  -- The previous helper already proves the needed closed-fiber quotient is nonzero.
  simpa using localized_target_quotient_nontrivial (R := R) (S := S) (N := N) q'

end

/-- Helper for Lemma 10.41.12: the localized module at `q'` is faithfully flat over
`R_(q' ∩ R)`. -/
lemma faithfullyFlat_localized_target
    (q' : Module.support S N) :
    let A := Localization.AtPrime ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
    let M := LocalizedModule.AtPrime q'.1.asIdeal N
    let B := Localization.AtPrime q'.1.asIdeal
    let _ : Algebra A B :=
      (Localization.localRingHom ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
        q'.1.asIdeal (algebraMap R S) rfl).toAlgebra
    let _ : Module A M :=
      Module.compHom M
        (Localization.localRingHom ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
          q'.1.asIdeal (algebraMap R S) rfl)
    let _ : IsScalarTower A B M := IsScalarTower.restrictScalars A B M
    Module.FaithfullyFlat A M := by
  let A := Localization.AtPrime ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
  let M := LocalizedModule.AtPrime q'.1.asIdeal N
  let B := Localization.AtPrime q'.1.asIdeal
  let f :=
    Localization.localRingHom ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
      q'.1.asIdeal (algebraMap R S) rfl
  letI : Algebra A B := f.toAlgebra
  letI : Module A M := Module.compHom M f
  letI : IsScalarTower A B M := IsScalarTower.restrictScalars A B M
  have hflat : Module.Flat A M := by
    -- Flatness localizes from `N` over `R` to `N_q'` over `R_(q' ∩ R)`.
    simpa [A, M] using
      flat_localizedModule_atPrime_over_under_of_flat
        (R := R) (A := S) (M := N) inferInstance q'.1
  letI : Module.Flat A M := hflat
  have hclosed :
      Nontrivial (M ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M))) := by
    simpa [A, B, M] using nontrivial_closed_fiber_at_localized_target (R := R) (S := S) (N := N) q'
  have hmax_ne :
      IsLocalRing.maximalIdeal A • (⊤ : Submodule A M) ≠ ⊤ := by
    exact Submodule.Quotient.nontrivial_iff.mp hclosed
  refine (Module.FaithfullyFlat.iff_flat_and_proper_ideal A M).2 ⟨hflat, ?_⟩
  intro I hI hItop
  have hImax : I ≤ IsLocalRing.maximalIdeal A := IsLocalRing.le_maximalIdeal hI
  apply hmax_ne
  exact eq_top_iff.2 <| by
    calc
      ⊤ = I • (⊤ : Submodule A M) := hItop.symm
      _ ≤ IsLocalRing.maximalIdeal A • (⊤ : Submodule A M) :=
        Submodule.smul_mono hImax le_rfl

/-- Helper for Lemma 10.41.12: a support point of the fiber-ring module contracts to a support
point of the localized module, and its contraction to the localized base is the chosen prime. -/
lemma support_point_contraction_of_fiber_ring_support
    {A : Type*} {B : Type*} {M : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    [Module.Finite B M]
    (p : PrimeSpectrum A) (r : PrimeSpectrum (p.asIdeal.Fiber B))
    (hr : r ∈ Module.support (p.asIdeal.Fiber B) ((p.asIdeal.Fiber B) ⊗[B] M)) :
    let Qover := (PrimeSpectrum.preimageEquivFiber A B p).symm r
    let Q : PrimeSpectrum B := Qover.1
    Q ∈ Module.support B M ∧ PrimeSpectrum.comap (algebraMap A B) Q = p := by
  let Qover := (PrimeSpectrum.preimageEquivFiber A B p).symm r
  let Q : PrimeSpectrum B := Qover.1
  constructor
  · -- Rewrite support on the fiber ring as inverse image of support on `B`.
    change PrimeSpectrum.comap (algebraMap B (p.asIdeal.Fiber B)) r ∈ Module.support B M
    simpa [Module.Lemma_10_40_6 (R := B) (R' := p.asIdeal.Fiber B) (M := M)] using hr
  · -- The fiber equivalence remembers exactly that this contracted prime lies over `p`.
    simpa [Q, Qover] using Qover.2

/-- Helper for Lemma 10.41.12: a support point of the localization at `q'` descends to a support
point of the original module below `q'`. -/
lemma localized_support_point_descends
    (q' : Module.support S N)
    (Q : PrimeSpectrum (Localization.AtPrime q'.1.asIdeal))
    (hQ : Q ∈ Module.support (Localization.AtPrime q'.1.asIdeal)
      (LocalizedModule.AtPrime q'.1.asIdeal N)) :
    PrimeSpectrum.comap (algebraMap S (Localization.AtPrime q'.1.asIdeal)) Q ∈
        Module.support S N ∧
      PrimeSpectrum.comap (algebraMap S (Localization.AtPrime q'.1.asIdeal)) Q ≤ q'.1 := by
  constructor
  · -- Support contracts along the localization map by the earlier localized-support bridge.
    exact mem_support_comap_of_mem_support_localized_atPrime (N := N) q'.1 hQ
  · -- The localization spectrum is exactly the interval of primes below `q'`.
    exact
      (IsLocalization.AtPrime.primeSpectrumOrderIso
        (Localization.AtPrime q'.1.asIdeal) q'.1.asIdeal Q).2

section

omit [Module R N] [IsScalarTower R S N] [Module.Finite S N] [Module.Flat R N]

/-- Helper for Lemma 10.41.12: once a localized prime `Q` contracts to `pLoc`, its descended
prime in `Spec S` contracts further to the original prime `p`. -/
lemma comap_of_descended_prime_eq
    (q' : Module.support S N) (p : PrimeSpectrum R)
    (hpq : p ≤ PrimeSpectrum.comap (algebraMap R S) q'.1)
    (Q : PrimeSpectrum (Localization.AtPrime q'.1.asIdeal))
    (hQ :
      let A := Localization.AtPrime ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
      let B := Localization.AtPrime q'.1.asIdeal
      let _ : Algebra A B :=
        (Localization.localRingHom ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
          q'.1.asIdeal (algebraMap R S) rfl).toAlgebra
      let pLoc : PrimeSpectrum A :=
        (IsLocalization.AtPrime.primeSpectrumOrderIso A
          ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)).symm ⟨p, hpq⟩
      PrimeSpectrum.comap (algebraMap A B) Q = pLoc) :
    PrimeSpectrum.comap (algebraMap R S)
      (PrimeSpectrum.comap (algebraMap S (Localization.AtPrime q'.1.asIdeal)) Q) = p := by
  let A := Localization.AtPrime ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
  let B := Localization.AtPrime q'.1.asIdeal
  let f :=
    Localization.localRingHom ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
      q'.1.asIdeal (algebraMap R S) rfl
  letI : Algebra A B := f.toAlgebra
  let pLoc : PrimeSpectrum A :=
    (IsLocalization.AtPrime.primeSpectrumOrderIso A
      ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)).symm ⟨p, hpq⟩
  have hQ' : PrimeSpectrum.comap (algebraMap A B) Q = pLoc := by
    simpa [A, B, pLoc] using hQ
  let eA := IsLocalization.AtPrime.primeSpectrumOrderIso A
    ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
  have hpLoc_eq : PrimeSpectrum.comap (algebraMap R A) pLoc = p := by
    -- Unpack the defining equation of `pLoc` from the localization order isomorphism on `A`.
    simpa [pLoc, eA] using congrArg Subtype.val (eA.apply_symm_apply ⟨p, hpq⟩)
  have hcompSB :
      PrimeSpectrum.comap (algebraMap R S) (PrimeSpectrum.comap (algebraMap S B) Q) =
        PrimeSpectrum.comap (algebraMap R B) Q := by
    -- Rewrite contraction through the composite `R → S → B`.
    simpa [IsScalarTower.algebraMap_eq R S B] using
      (PrimeSpectrum.comap_comp_apply (algebraMap R S) (algebraMap S B) Q).symm
  have hcompAB :
      PrimeSpectrum.comap (algebraMap R A) (PrimeSpectrum.comap (algebraMap A B) Q) =
        PrimeSpectrum.comap (algebraMap R B) Q := by
    -- Rewrite contraction through the composite `R → A → B`.
    simpa [IsScalarTower.algebraMap_eq R A B] using
      (PrimeSpectrum.comap_comp_apply (algebraMap R A) (algebraMap A B) Q).symm
  -- Route correction: isolate the final contraction calculation from the support descent.
  calc
    PrimeSpectrum.comap (algebraMap R S)
        (PrimeSpectrum.comap (algebraMap S B) Q)
      = PrimeSpectrum.comap (algebraMap R B) Q := hcompSB
    _ = PrimeSpectrum.comap (algebraMap R A)
          (PrimeSpectrum.comap (algebraMap A B) Q) := hcompAB.symm
    _ = PrimeSpectrum.comap (algebraMap R A) pLoc := by rw [hQ']
    _ = p := hpLoc_eq

end

section

omit [Module R N] [IsScalarTower R S N] [Module.Flat R N]

/-- Helper for Lemma 10.41.12: a nontrivial fiber ring module over the localized target produces
a support point below `q'` lying over the original prime `p`. -/
lemma exists_support_prime_below_of_nontrivial_fiber_ring_tensor
    (q' : Module.support S N) (p : PrimeSpectrum R)
    (hpq : p ≤ PrimeSpectrum.comap (algebraMap R S) q'.1)
    (hfiber :
      let A := Localization.AtPrime ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
      let B := Localization.AtPrime q'.1.asIdeal
      let M := LocalizedModule.AtPrime q'.1.asIdeal N
      let _ : Algebra A B :=
        (Localization.localRingHom ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
          q'.1.asIdeal (algebraMap R S) rfl).toAlgebra
      let _ : Module A M :=
        Module.compHom M
          (Localization.localRingHom ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
            q'.1.asIdeal (algebraMap R S) rfl)
      let _ : IsScalarTower A B M := IsScalarTower.restrictScalars A B M
      let pLoc : PrimeSpectrum A :=
        (IsLocalization.AtPrime.primeSpectrumOrderIso A
          ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)).symm ⟨p, hpq⟩
      Nontrivial ((pLoc.asIdeal.Fiber B) ⊗[B] M)) :
      ∃ q : PrimeSpectrum S,
        q ∈ Module.support S N ∧
          q ≤ q'.1 ∧
            PrimeSpectrum.comap (algebraMap R S) q = p := by
  let A := Localization.AtPrime ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
  let B := Localization.AtPrime q'.1.asIdeal
  let M := LocalizedModule.AtPrime q'.1.asIdeal N
  let f :=
    Localization.localRingHom ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
      q'.1.asIdeal (algebraMap R S) rfl
  letI : Algebra A B := f.toAlgebra
  letI : Module A M := Module.compHom M f
  letI : IsScalarTower A B M := IsScalarTower.restrictScalars A B M
  let pLoc : PrimeSpectrum A :=
    (IsLocalization.AtPrime.primeSpectrumOrderIso A
      ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)).symm ⟨p, hpq⟩
  have hfiber' : Nontrivial ((pLoc.asIdeal.Fiber B) ⊗[B] M) := by
    simpa [A, B, M, pLoc] using hfiber
  -- Choose a support point of the nonzero fiber module exactly as in the source proof.
  obtain ⟨r, hr⟩ :
      (Module.support (pLoc.asIdeal.Fiber B) ((pLoc.asIdeal.Fiber B) ⊗[B] M)).Nonempty := by
    exact Module.nonempty_support_iff.mpr hfiber'
  let Qover := (PrimeSpectrum.preimageEquivFiber A B pLoc).symm r
  let Q : PrimeSpectrum B := Qover.1
  have hQ :
      Q ∈ Module.support B M ∧ PrimeSpectrum.comap (algebraMap A B) Q = pLoc := by
    -- Contract the support point of the fiber back to `Spec(B)`.
    simpa [Q, Qover] using
      support_point_contraction_of_fiber_ring_support
        (A := A) (B := B) (M := M) pLoc r hr
  have hq :
      PrimeSpectrum.comap (algebraMap S B) Q ∈ Module.support S N ∧
        PrimeSpectrum.comap (algebraMap S B) Q ≤ q'.1 := by
    -- Descend the localized support point to a point of `Spec(S)` below `q'`.
    simpa [B] using localized_support_point_descends (N := N) q' Q hQ.1
  refine ⟨PrimeSpectrum.comap (algebraMap S B) Q, hq.1, hq.2, ?_⟩
  -- Finish by identifying the contraction of the descended prime with the original `p`.
  exact comap_of_descended_prime_eq (R := R) (S := S) (N := N) q' p hpq Q hQ.2

end

/- Domain triage:
* primary domain: support of finite modules on prime spectra, together with lifting of
  generalizations along the induced support map;
* core/canonical owners: `Module.support S N` for the subset of `Spec S` and `GeneralizingMap`
  for the topological lifting property;
* sampled canonical declarations:
  `Module.support`,
  `Module.mem_support_iff_nontrivial_residueField_tensorProduct`,
  `Module.support_subset_preimage_comap`,
  and `Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap`;
* layer: `bridge/view`, since the source theorem is about the canonical map from the support of
  `N` to `Spec R`, not about introducing a new owner object.

Primitive-vs-derived split:
* primitive data: the finite `S`-module `N`, its `R`-flatness, and the canonical subset
  `Module.support S N`;
* derived API: the induced map `Module.support S N → PrimeSpectrum R`, written canonically as the
  composite of the subtype inclusion with `PrimeSpectrum.comap (algebraMap R S)`.
-/
/-- Lemma 10.41.12: if `N` is a finite `S`-module that is flat over `R`, then generalizations
lift along the support map `support S N → Spec R` induced by
`PrimeSpectrum.comap (algebraMap R S)`. Equivalently, if `p ⤳ p'` in `Spec R` and
`q' ∈ support S N` lies over `p'`, then there exists `q ∈ support S N` with `q ⤳ q'`
lying over `p`. -/
@[stacks 080T]
theorem generalizingMap_support_comap_of_flat :
    GeneralizingMap (comap (algebraMap R S) ∘ ((↑) : support S N → PrimeSpectrum S)) := by
  intro q' p hpq
  have hpq_le : p ≤ PrimeSpectrum.comap (algebraMap R S) q'.1 := by
    simpa using (PrimeSpectrum.le_iff_specializes p (PrimeSpectrum.comap (algebraMap R S) q'.1)).mpr hpq
  let A := Localization.AtPrime ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
  let B := Localization.AtPrime q'.1.asIdeal
  let M := LocalizedModule.AtPrime q'.1.asIdeal N
  let f :=
    Localization.localRingHom ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)
      q'.1.asIdeal (algebraMap R S) rfl
  letI : Algebra A B := f.toAlgebra
  letI : Module A M := Module.compHom M f
  letI : IsScalarTower A B M := IsScalarTower.restrictScalars A B M
  let pLoc : PrimeSpectrum A :=
    (IsLocalization.AtPrime.primeSpectrumOrderIso A
      ((PrimeSpectrum.comap (algebraMap R S) q'.1).asIdeal)).symm
      ⟨p, hpq_le⟩
  have hff : Module.FaithfullyFlat A M := by
    -- Localize at `q'` and use the closed-fiber criterion proved above.
    simpa [A, B, M] using faithfullyFlat_localized_target (R := R) (S := S) (N := N) q'
  have hpLoc_nontrivial : Nontrivial (M ⊗[A] pLoc.asIdeal.ResidueField) := by
    exact (faithfullyFlat_iff_forall_nontrivial_tensor_primeResidueField.1 hff) pLoc
  have hpLoc_nontrivial' : Nontrivial (pLoc.asIdeal.ResidueField ⊗[A] M) := by
    -- Commute the tensor factors to match the fiber-ring helper.
    exact (TensorProduct.comm A pLoc.asIdeal.ResidueField M).nontrivial_congr.mpr hpLoc_nontrivial
  have hfiber :
      Nontrivial ((pLoc.asIdeal.Fiber B) ⊗[B] M) := by
    exact nontrivial_fiber_ring_tensor_of_nontrivial_prime_residue_tensor
      (A := A) (B := B) (M := M) pLoc hpLoc_nontrivial'
  obtain ⟨q, hqsupport, hq_le, hq_comap⟩ :=
    exists_support_prime_below_of_nontrivial_fiber_ring_tensor
      (R := R) (S := S) (N := N) q' p hpq_le hfiber
  refine ⟨⟨q, hqsupport⟩, ?_, hq_comap⟩
  -- The support is stable under specialization, so the order relation downstairs lifts to the
  -- subtype `Module.support S N`.
  exact (subtype_specializes_iff ⟨q, hqsupport⟩ q').2 <|
    (PrimeSpectrum.le_iff_specializes _ _).1 hq_le

end Module

end
