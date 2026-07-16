import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_42_1
import stacks_proof.stacks_project.Chap10.Definition_10_165_2
import stacks_proof.stacks_project.Chap10.Lemma_10_37_13
import stacks_proof.stacks_project.Chap10.Lemma_10_37_15
import stacks_proof.stacks_project.Chap10.Lemma_10_43_5
import stacks_proof.stacks_project.Chap10.Lemma_10_43_6
import stacks_proof.stacks_project.Chap10.Lemma_10_43_8
import stacks_proof.stacks_project.Chap10.Lemma_10_43_9
import stacks_proof.stacks_project.Chap10.Lemma_10_164_3
import stacks_proof.stacks_project.Chap10.Lemma_10_165_1
import stacks_proof.stacks_project.Chap10.Lemma_10_165_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

namespace Algebra

section

variable {k : Type u} {k' : Type u} {A : Type v}
variable [Field k] [Field k'] [CommRing A]
variable [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
variable [Algebra.IsSeparable k k']

/-- Helper for Lemma 10.165.6: normality transports across ring equivalences. -/
theorem isNormalRing_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) [IsNormalRing R] : IsNormalRing S := by
  refine ⟨fun p ↦ ?_⟩
  let q : PrimeSpectrum R := PrimeSpectrum.comap e.toRingHom p
  let eLoc : Localization.AtPrime q.asIdeal ≃+* Localization.AtPrime p.asIdeal :=
    Localization.localRingEquiv _ _ e (PrimeSpectrum.comap_asIdeal (f := e.toRingHom) p)
  have hDomain : IsDomain (Localization.AtPrime q.asIdeal) := isDomain_localizationAtPrime q
  have hIntegrallyClosed : IsIntegrallyClosed (Localization.AtPrime q.asIdeal) :=
    isIntegrallyClosed_localizationAtPrime q
  refine ⟨?_, ?_⟩
  · exact Function.Injective.isDomain eLoc.symm.toRingHom eLoc.symm.injective
  · exact IsIntegrallyClosed.of_equiv eLoc

omit [Field k'] [CommRing A] [Algebra k k'] [Algebra k' A] [Algebra k A]
  [IsScalarTower k k' A] [Algebra.IsSeparable k k'] in
/-- Helper for Chap10 Lemma 10 165 6: a field extension separable in the Stacks sense is
geometrically normal over the base field. -/
@[instance low] theorem isGeometricallyNormal_of_isSeparableOver_local
    {K : Type w} [Field K] [Algebra k K] [IsSeparableOver k K] :
    IsGeometricallyNormal k K := by
  refine ⟨?_⟩
  have hfinite :
      ∀ (L : Type (max u w)) [Field L] [Algebra k L] [FiniteDimensional k L]
        [IsPurelyInseparable k L],
        IsNormalRing (L ⊗[k] K) := by
    intro L _ _ _ _
    have hred : IsReduced (L ⊗[k] K) :=
      isReduced_tensorProduct_of_geometricallyReduced
    let e : L ⊗[k] K ≃ₐ[k] K ⊗[k] L := Algebra.TensorProduct.comm k L K
    letI : IsReduced (K ⊗[k] L) := isReduced_of_injective e.symm.toRingHom e.symm.injective
    letI : IsArtinianRing (K ⊗[k] L) := IsArtinianRing.of_finite K (K ⊗[k] L)
    letI :
        ∀ I : MaximalSpectrum (K ⊗[k] L), IsNormalRing ((K ⊗[k] L) ⧸ I.asIdeal) :=
      fun I ↦ by
        letI : Field ((K ⊗[k] L) ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
        infer_instance
    letI : CommRing (∀ I : MaximalSpectrum (K ⊗[k] L), (K ⊗[k] L) ⧸ I.asIdeal) :=
      inferInstance
    letI : IsNormalRing (∀ I : MaximalSpectrum (K ⊗[k] L), (K ⊗[k] L) ⧸ I.asIdeal) :=
      isNormalRing_pi
    let f : K ⊗[k] L →+* ∀ I : MaximalSpectrum (K ⊗[k] L), (K ⊗[k] L) ⧸ I.asIdeal :=
      IsArtinianRing.equivPi (K ⊗[k] L)
    have hbij : Function.Bijective f := (IsArtinianRing.equivPi (K ⊗[k] L)).bijective
    have hf : RingHom.FaithfullyFlat f := by
      exact RingHom.FaithfullyFlat.of_bijective hbij
    letI : IsNormalRing (K ⊗[k] L) := isNormalRing_of_faithfullyFlat f hf
    let f' : L ⊗[k] K →+* K ⊗[k] L := e.toRingHom
    have hbij' : Function.Bijective f' := e.bijective
    have hf' : RingHom.FaithfullyFlat f' := by
      exact RingHom.FaithfullyFlat.of_bijective hbij'
    exact isNormalRing_of_faithfullyFlat f' hf'
  intro L _ _
  have hall :
      ∀ (L : Type (max u w)) [Field L] [Algebra k L], IsNormalRing (L ⊗[k] K) :=
    (forall_isNormalRing_tensorProduct_iff_finitePurelyInseparable (k := k) (A := K)).2 hfinite
  exact hall L

/-- Helper for Lemma 10.165.6: geometric normality supplies normality for tensor products with
field extensions in the owner universe after transporting across `ULift.algEquiv`. -/
theorem isNormalRing_tensorProduct_of_geometricallyNormal
    [IsGeometricallyNormal k A] (K : Type (max u v)) [Field K] [Algebra k K] :
    IsNormalRing (K ⊗[k] A) := by
  -- Proof comment: this is exactly the owner field of `IsGeometricallyNormal`.
  exact IsGeometricallyNormal.isNormalRing_baseChange (k := k) (R := A) K

/-- Helper for Lemma 10.165.6: geometric normality gives right-oriented tensor normality for
field extensions in the owner universe. -/
theorem isNormalRing_tensorProduct_fieldRight_of_geometricallyNormal
    [IsGeometricallyNormal k A] (K : Type (max u v)) [Field K] [Algebra k K] :
    IsNormalRing (A ⊗[k] K) := by
  -- Proof comment: commute the tensor factors after applying the owner field test.
  have hLeft : IsNormalRing (K ⊗[k] A) :=
    isNormalRing_tensorProduct_of_geometricallyNormal (k := k) (A := A) K
  let e : K ⊗[k] A ≃ₐ[k] A ⊗[k] K := Algebra.TensorProduct.comm k K A
  letI : IsNormalRing (K ⊗[k] A) := hLeft
  exact isNormalRing_of_ringEquiv e.toRingEquiv

/-- Helper for Lemma 10.165.6: geometric normality gives right-oriented tensor normality for
small field extensions. -/
theorem isNormalRing_tensorProduct_fieldRight_small_of_geometricallyNormal
    [IsGeometricallyNormal k A] (K : Type w) [Field K] [Algebra k K]
    [Small.{max u v} K] : IsNormalRing (A ⊗[k] K) := by
  -- Proof comment: shrink the field into the owner universe and transport back.
  have hShrink : IsNormalRing (A ⊗[k] Shrink.{max u v} K) :=
    isNormalRing_tensorProduct_fieldRight_of_geometricallyNormal
      (k := k) (A := A) (Shrink.{max u v} K)
  let eShrink : A ⊗[k] Shrink.{max u v} K ≃+* A ⊗[k] K :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[k] A)
      (Shrink.algEquiv k K)).toRingEquiv
  letI : IsNormalRing (A ⊗[k] Shrink.{max u v} K) := hShrink
  exact isNormalRing_of_ringEquiv eShrink

/-- Helper for Lemma 10.165.6: an algebra equivalence over the base field preserves geometric
normality. -/
theorem IsGeometricallyNormal.of_algEquiv {B : Type v} [CommRing B] [Algebra k B]
    [IsGeometricallyNormal k A] (e : A ≃ₐ[k] B) : IsGeometricallyNormal k B := by
  refine { isNormalRing_baseChange := ?_ }
  intro K _ _
  -- Tensor the given algebra equivalence with the arbitrary field extension.
  let eK : K ⊗[k] A ≃ₐ[K] K ⊗[k] B :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) e
  -- The source tensor product is normal by geometric normality of `A`.
  letI : IsNormalRing (K ⊗[k] A) :=
    isNormalRing_tensorProduct_of_geometricallyNormal (k := k) (A := A) K
  -- Transport normality across the base-changed algebra equivalence.
  exact isNormalRing_of_ringEquiv eK.toRingEquiv

/-- Helper for Lemma 10.165.6: localizing a geometrically normal algebra preserves geometric
normality. -/
theorem IsGeometricallyNormal.of_isLocalization_local {A₀ : Type w} {B : Type w}
    [CommRing A₀] [Algebra k A₀] [CommRing B] [Algebra k B]
    [Algebra A₀ B] [IsScalarTower k A₀ B] (S : Submonoid A₀) [IsLocalization S B]
    [IsGeometricallyNormal k A₀] : IsGeometricallyNormal k B := by
  refine { isNormalRing_baseChange := ?_ }
  intro K instK instKA
  letI := instK
  letI := instKA
  letI : IsNormalRing (TensorProduct k K A₀) :=
    IsGeometricallyNormal.isNormalRing_baseChange (k := k) (R := A₀) K
  letI : Algebra A₀ (TensorProduct k K A₀) := Algebra.TensorProduct.rightAlgebra
  letI : IsLocalization (Algebra.algebraMapSubmonoid (TensorProduct k K A₀) S)
      (TensorProduct A₀ (TensorProduct k K A₀) B) := by
    infer_instance
  letI : IsNormalRing (TensorProduct A₀ (TensorProduct k K A₀) B) :=
    isNormalRing_of_isLocalization (Algebra.algebraMapSubmonoid (TensorProduct k K A₀) S)
  let e : TensorProduct A₀ (TensorProduct k K A₀) B ≃ₐ[K] TensorProduct k K B :=
    Algebra.IsPushout.cancelBaseChangeAlg k K A₀ (TensorProduct k K A₀) B
  let f : TensorProduct k K B →+* TensorProduct A₀ (TensorProduct k K A₀) B :=
    e.symm.toRingHom
  have hf : RingHom.FaithfullyFlat f := by
    let hbij : Function.Bijective f := e.symm.bijective
    exact RingHom.FaithfullyFlat.of_bijective hbij
  -- Proof comment: normality descends along the faithfully flat comparison isomorphism.
  exact isNormalRing_of_faithfullyFlat f hf

/-- Helper for Lemma 10.165.6: tensoring a geometrically normal algebra with a finite-dimensional
normal algebra preserves normality. -/
theorem isNormalRing_tensorProduct_of_isGeometricallyNormal_finiteDimensional
    {B : Type w} [CommRing B] [Algebra k B] [FiniteDimensional k B]
    [IsGeometricallyNormal k A] [IsNormalRing B] :
    IsNormalRing (A ⊗[k] B) := by
  classical
  letI : IsArtinianRing B := IsArtinianRing.of_finite k B
  letI : Fintype (MaximalSpectrum B) := Fintype.ofFinite (MaximalSpectrum B)
  let eB : B ≃ₐ[k] ∀ I : MaximalSpectrum B, B ⧸ I.asIdeal :=
    (IsArtinianRing.equivPi B).restrictScalars k
  let eTensorB :
      A ⊗[k] B ≃ₐ[k] A ⊗[k] (∀ I : MaximalSpectrum B, B ⧸ I.asIdeal) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[k] A) eB
  let ePi :
      A ⊗[k] (∀ I : MaximalSpectrum B, B ⧸ I.asIdeal) ≃ₐ[k]
        ∀ I : MaximalSpectrum B, A ⊗[k] (B ⧸ I.asIdeal) :=
    Algebra.TensorProduct.piRight k k A fun I : MaximalSpectrum B ↦ B ⧸ I.asIdeal
  have hEach : ∀ I : MaximalSpectrum B, IsNormalRing (A ⊗[k] (B ⧸ I.asIdeal)) := by
    intro I
    letI : Field (B ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    have hsmall : Small.{max u v} (B ⧸ I.asIdeal) :=
      Module.Finite.small (R := k) (M := B ⧸ I.asIdeal)
    letI : Small.{max u v} (B ⧸ I.asIdeal) := hsmall
    exact isNormalRing_tensorProduct_fieldRight_small_of_geometricallyNormal
      (k := k) (A := A) (B ⧸ I.asIdeal)
  letI : ∀ I : MaximalSpectrum B, IsNormalRing (A ⊗[k] (B ⧸ I.asIdeal)) := hEach
  letI : IsNormalRing (∀ I : MaximalSpectrum B, A ⊗[k] (B ⧸ I.asIdeal)) :=
    isNormalRing_pi
  -- Proof comment: a finite-dimensional normal algebra is a finite product of fields, and tensor
  -- products commute with this finite product.
  exact isNormalRing_of_ringEquiv (eTensorB.trans ePi).symm.toRingEquiv

omit [Algebra.IsSeparable k k'] in
/-- Helper for Lemma 10.165.6: every tensor in `L ⊗[k] k'` is already defined over a finite
separable adjoin stage of `k' / k`. -/
lemma exists_finite_adjoin_stage_leftTensor {L : Type*} [Field L] [Algebra k L]
    (z : L ⊗[k] k') :
    ∃ t : Finset k',
      ∃ zt : L ⊗[k] IntermediateField.adjoin k (t : Set k'),
        Algebra.TensorProduct.map
            (AlgHom.id k L)
            (IsScalarTower.toAlgHom k (IntermediateField.adjoin k (t : Set k')) k')
            zt = z := by
  classical
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · refine ⟨∅, 0, ?_⟩
    simp
  · intro x y
    let t : Finset k' := {y}
    let E := IntermediateField.adjoin k (t : Set k')
    let yE : E := ⟨y, IntermediateField.subset_adjoin k (t : Set k') (by simp [t])⟩
    refine ⟨t, x ⊗ₜ[k] yE, ?_⟩
    simp [t, E, yE]
  · intro x y hx hy
    rcases hx with ⟨tx, xt, hxt⟩
    rcases hy with ⟨ty, yt, hyt⟩
    let t : Finset k' := tx ∪ ty
    let E := IntermediateField.adjoin k (t : Set k')
    have hxle : IntermediateField.adjoin k (tx : Set k') ≤ E := by
      rw [IntermediateField.adjoin_le_iff]
      intro a ha
      exact IntermediateField.subset_adjoin k (t : Set k') (by
        exact Finset.mem_union.mpr <| Or.inl ha)
    have hyle : IntermediateField.adjoin k (ty : Set k') ≤ E := by
      rw [IntermediateField.adjoin_le_iff]
      intro a ha
      exact IntermediateField.subset_adjoin k (t : Set k') (by
        exact Finset.mem_union.mpr <| Or.inr ha)
    refine ⟨t,
      Algebra.TensorProduct.map (AlgHom.id k L) (IntermediateField.inclusion hxle) xt +
        Algebra.TensorProduct.map (AlgHom.id k L) (IntermediateField.inclusion hyle) yt,
      ?_⟩
    have hcompxt :
        (IsScalarTower.toAlgHom k E k').comp (IntermediateField.inclusion hxle) =
          IsScalarTower.toAlgHom k (IntermediateField.adjoin k (tx : Set k')) k' := by
      ext z
      rfl
    have hmapxt :
        (TensorProduct.map (AlgHom.id k L) (IsScalarTower.toAlgHom k E k')).comp
            (TensorProduct.map (AlgHom.id k L) (IntermediateField.inclusion hxle)) =
          TensorProduct.map (AlgHom.id k L)
            (IsScalarTower.toAlgHom k (IntermediateField.adjoin k (tx : Set k')) k') := by
      rw [← TensorProduct.map_id_comp]
      simpa [hcompxt]
    have hxt' :
        (TensorProduct.map (AlgHom.id k L) (IsScalarTower.toAlgHom k E k'))
            ((TensorProduct.map (AlgHom.id k L) (IntermediateField.inclusion hxle)) xt) = x := by
      have hxt'' := DFunLike.congr_fun hmapxt xt
      simpa [AlgHom.comp_apply] using hxt''.trans hxt
    have hcompty :
        (IsScalarTower.toAlgHom k E k').comp (IntermediateField.inclusion hyle) =
          IsScalarTower.toAlgHom k (IntermediateField.adjoin k (ty : Set k')) k' := by
      ext z
      rfl
    have hmapty :
        (TensorProduct.map (AlgHom.id k L) (IsScalarTower.toAlgHom k E k')).comp
            (TensorProduct.map (AlgHom.id k L) (IntermediateField.inclusion hyle)) =
          TensorProduct.map (AlgHom.id k L)
            (IsScalarTower.toAlgHom k (IntermediateField.adjoin k (ty : Set k')) k') := by
      rw [← TensorProduct.map_id_comp]
      simpa [hcompty]
    have hyt' :
        (TensorProduct.map (AlgHom.id k L) (IsScalarTower.toAlgHom k E k'))
            ((TensorProduct.map (AlgHom.id k L) (IntermediateField.inclusion hyle)) yt) = y := by
      have hyt'' := DFunLike.congr_fun hmapty yt
      simpa [AlgHom.comp_apply] using hyt''.trans hyt
    simpa [map_add] using congrArg₂ HAdd.hAdd hxt' hyt'

/-- Helper for Lemma 10.165.6: a finite purely inseparable extension tensored with a separable
algebraic field extension is reduced. -/
lemma isReduced_tensorProduct_of_finitePurelyInseparable_left_separable_right
    {L : Type*} [Field L] [Algebra k L] [FiniteDimensional k L] [IsPurelyInseparable k L] :
    IsReduced (L ⊗[k] k') := by
  refine ⟨fun z hz ↦ ?_⟩
  obtain ⟨t, zt, rfl⟩ :=
    exists_finite_adjoin_stage_leftTensor (k := k) (k' := k') (L := L) z
  let E := IntermediateField.adjoin k (t : Set k')
  have hEsep : Algebra.IsSeparable k E := by
    rw [IntermediateField.isSeparable_adjoin_iff_isSeparable]
    intro x _
    exact Algebra.IsSeparable.isSeparable k x
  have hEfin : FiniteDimensional k E := by
    exact IntermediateField.finiteDimensional_adjoin (S := (t : Set k')) fun x _ ↦
      (Algebra.IsSeparable.isIntegral k x)
  letI : Algebra.IsSeparable k E := hEsep
  letI : FiniteDimensional k E := hEfin
  letI : Algebra.FormallyEtale k E := Algebra.FormallyEtale.of_isSeparable k E
  letI : Algebra.FormallyEtale L (L ⊗[k] E) := inferInstance
  have hredStage : IsReduced (L ⊗[k] E) :=
    Algebra.FormallyUnramified.isReduced_of_field L (L ⊗[k] E)
  let f :
      L ⊗[k] E →ₐ[k] L ⊗[k] k' :=
    Algebra.TensorProduct.map (AlgHom.id k L) (IsScalarTower.toAlgHom k E k')
  have hf : Function.Injective f := by
    simpa using TensorProduct.map_injective_of_flat_flat
      (LinearMap.id : L →ₗ[k] L)
      (IsScalarTower.toAlgHom k E k').toLinearMap
      (fun _ _ h ↦ h)
      (IsScalarTower.toAlgHom k E k').injective
  have hztNil : IsNilpotent zt := by
    rcases hz with ⟨n, hn⟩
    refine IsNilpotent.mk zt n ?_
    -- Proof comment: nilpotence pulls back through the injective tensor map because the map
    -- preserves powers and zero.
    apply hf
    change
      (Algebra.TensorProduct.map (AlgHom.id k L) (IsScalarTower.toAlgHom k E k')) (zt ^ n) = 0
    rw [map_pow]
    exact hn
  simpa using congrArg f (isNilpotent_iff_eq_zero.mp hztNil)

/-- Helper for Lemma 10.165.6: a separable algebraic field extension is geometrically normal over
the base field. -/
lemma isGeometricallyNormal_field_of_isSeparable_local :
    IsGeometricallyNormal k k' := by
  refine ⟨?_⟩
  have hfinite :
      ∀ (L : Type u) [Field L] [Algebra k L] [FiniteDimensional k L]
        [IsPurelyInseparable k L],
        IsNormalRing (L ⊗[k] k') := by
    intro L _ _ _ _
    have hred : IsReduced (L ⊗[k] k') :=
      isReduced_tensorProduct_of_finitePurelyInseparable_left_separable_right
        (k := k) (k' := k') (L := L)
    let e : L ⊗[k] k' ≃ₐ[k] k' ⊗[k] L := Algebra.TensorProduct.comm k L k'
    letI : IsReduced (k' ⊗[k] L) := isReduced_of_injective e.symm.toRingHom e.symm.injective
    letI : IsArtinianRing (k' ⊗[k] L) := IsArtinianRing.of_finite k' (k' ⊗[k] L)
    letI :
        ∀ I : MaximalSpectrum (k' ⊗[k] L), IsNormalRing ((k' ⊗[k] L) ⧸ I.asIdeal) := by
      intro I
      letI : Field ((k' ⊗[k] L) ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
      infer_instance
    letI : IsNormalRing (∀ I : MaximalSpectrum (k' ⊗[k] L), (k' ⊗[k] L) ⧸ I.asIdeal) :=
      isNormalRing_pi
    letI : CommRing (∀ I : MaximalSpectrum (k' ⊗[k] L), (k' ⊗[k] L) ⧸ I.asIdeal) :=
      inferInstance
    let f : k' ⊗[k] L →+* ∀ I : MaximalSpectrum (k' ⊗[k] L), (k' ⊗[k] L) ⧸ I.asIdeal :=
      (IsArtinianRing.equivPi (k' ⊗[k] L)).toRingHom
    have hf : RingHom.FaithfullyFlat f := by
      exact RingHom.FaithfullyFlat.of_bijective (IsArtinianRing.equivPi (k' ⊗[k] L)).bijective
    letI : IsNormalRing (k' ⊗[k] L) := isNormalRing_of_faithfullyFlat f hf
    let f' : L ⊗[k] k' →+* k' ⊗[k] L := e.toRingHom
    have hf' : RingHom.FaithfullyFlat f' := by
      exact RingHom.FaithfullyFlat.of_bijective e.bijective
    exact isNormalRing_of_faithfullyFlat f' hf'
  exact (forall_isNormalRing_tensorProduct_iff_finitePurelyInseparable
    (k := k) (A := k')).2 hfinite

omit [Algebra.IsSeparable k k'] in
/-- Helper for Lemma 10.165.6: if the intermediate field extension `k' / k` is geometrically
normal and `A` is geometrically normal over `k'`, then `A` is geometrically normal over `k`. -/
lemma isGeometricallyNormal_restrictScalars_of_geometricallyNormal_base
    [IsGeometricallyNormal k k'] [IsGeometricallyNormal k' A] :
    IsGeometricallyNormal k A := by
  refine ⟨?_⟩
  -- Route correction: use the finite purely inseparable test from the source proof, then rewrite
  -- the test ring via the standard `commRight` plus `cancelBaseChange` tensor comparison.
  let hfinite :
      ∀ (L : Type (max u v)) [Field L] [Algebra k L] [FiniteDimensional k L]
        [IsPurelyInseparable k L], IsNormalRing (L ⊗[k] A) := by
    intro L _ _ _ _
    -- The intermediate tensor product `L ⊗[k] k'` is normal because `k'` is geometrically normal
    -- over `k`.
    letI : IsNormalRing (k' ⊗[k] L) := by
      have hsmall : Small.{u} L := Module.Finite.small (R := k) (M := L)
      letI : Small.{u} L := hsmall
      exact isNormalRing_tensorProduct_fieldRight_small_of_geometricallyNormal
        (k := k) (A := k') L
    -- Tensor this normal ring with the geometrically normal `k'`-algebra `A`.
    have hnormalTensor : IsNormalRing (A ⊗[k'] (k' ⊗[k] L)) := by
      letI : FiniteDimensional k' (k' ⊗[k] L) := inferInstance
      exact isNormalRing_tensorProduct_of_isGeometricallyNormal_finiteDimensional
        (k := k') (A := A) (B := k' ⊗[k] L)
    letI : IsNormalRing (A ⊗[k'] (k' ⊗[k] L)) := hnormalTensor
    let e : A ⊗[k'] (k' ⊗[k] L) ≃+* L ⊗[k] A :=
      ((Algebra.TensorProduct.cancelBaseChange k k' A A L).toRingEquiv).trans <|
        (Algebra.TensorProduct.comm k A L).toRingEquiv
    -- Transport normality across the comparison to recover the original test ring.
    exact isNormalRing_of_ringEquiv (R := A ⊗[k'] (k' ⊗[k] L)) (S := L ⊗[k] A) e
  -- The finite purely inseparable criterion is exactly Lemma `10.165.1`.
  exact (forall_isNormalRing_tensorProduct_iff_finitePurelyInseparable
    (k := k) (A := A)).2 hfinite

omit [Algebra k' A] [IsScalarTower k k' A] [Algebra.IsSeparable k k'] in
/-- Helper for Lemma 10.165.6: after base change from `k` to `k'`, the resulting algebra
`k' ⊗[k] A` is geometrically normal over `k'` whenever `A` is geometrically normal over `k`. -/
lemma isGeometricallyNormal_tensor_baseChange [IsGeometricallyNormal k A] :
    IsGeometricallyNormal k' (k' ⊗[k] A) := by
  refine { isNormalRing_baseChange := ?_ }
  intro K _ _
  -- Equip `K` with the composite `k`-algebra structure so the source proof can compare the two
  -- tensor products by the canonical base-change cancellation isomorphism.
  letI : Algebra k K := ((algebraMap k' K).comp (algebraMap k k')).toAlgebra
  letI : IsScalarTower k k' K := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsNormalRing (ULift.{u} K ⊗[k] A) :=
    isNormalRing_tensorProduct_of_geometricallyNormal (k := k) (A := A)
      (ULift.{u} K)
  let eLift : ULift.{u} K ⊗[k] A ≃+* K ⊗[k] A :=
    (Algebra.TensorProduct.congr (ULift.algEquiv (R := k) (A := K))
      (AlgEquiv.refl : A ≃ₐ[k] A)).toRingEquiv
  letI : IsNormalRing (K ⊗[k] A) := isNormalRing_of_ringEquiv eLift
  let e : K ⊗[k'] (k' ⊗[k] A) ≃+* K ⊗[k] A :=
    (Algebra.TensorProduct.cancelBaseChange k k' K K A).toRingEquiv
  -- The comparison isomorphism turns the base-changed test ring into the original one.
  exact isNormalRing_of_ringEquiv e.symm

omit [Algebra k' A] [IsScalarTower k k' A] [Algebra.IsSeparable k k'] in
/-- Helper for Lemma 10.165.6: the source proof uses the right-ordered base change
`A ⊗[k] k'`, so commute the standard base change once and transport geometric normality there. -/
lemma isGeometricallyNormal_tensor_baseChange_commRight [IsGeometricallyNormal k A] :
    letI : Algebra k' (A ⊗[k] k') := Algebra.TensorProduct.rightAlgebra
    IsGeometricallyNormal k' (A ⊗[k] k') := by
  letI : IsGeometricallyNormal k' (k' ⊗[k] A) :=
    isGeometricallyNormal_tensor_baseChange (k := k) (k' := k') (A := A)
  letI : Algebra k' (A ⊗[k] k') := Algebra.TensorProduct.rightAlgebra
  -- Proof comment: `commRight` rewrites the usual base change into the tensor order used by the
  -- source diagonal-localization argument.
  exact IsGeometricallyNormal.of_algEquiv
    (k := k') (A := k' ⊗[k] A) (B := A ⊗[k] k')
    (Algebra.TensorProduct.commRight k k' A)

/-- Helper for Lemma 10.165.6: geometric normality of `k' ⊗[k'] A` collapses back to `A` through
the standard left-unital tensor equivalence. -/
lemma isGeometricallyNormal_of_tensorProduct_lid :
    IsGeometricallyNormal k' (k' ⊗[k'] A) → IsGeometricallyNormal k' A := by
  intro h
  refine ⟨?_⟩
  intro K _ _
  letI : IsGeometricallyNormal k' (k' ⊗[k'] A) := h
  letI : IsNormalRing (K ⊗[k'] (k' ⊗[k'] A)) :=
    IsGeometricallyNormal.isNormalRing_baseChange (k := k') (R := k' ⊗[k'] A) K
  let e : K ⊗[k'] (k' ⊗[k'] A) ≃+* K ⊗[k'] A :=
    (Algebra.TensorProduct.cancelBaseChange k' k' K K A).toRingEquiv
  -- Proof comment: the base-change cancellation isomorphism removes the redundant `k'` factor.
  exact isNormalRing_of_ringEquiv e

omit [Algebra.IsSeparable k k'] in
/-- Helper for Lemma 10.165.6: diagonal multiplication on `k' ⊗[k] k'` is compatible with the
left-factor `k'`-algebra structure. -/
lemma separableDiagonal_lmul_left_commutes (x : k') :
    (TensorProduct.lmul' k : TensorProduct k k' k' →ₐ[k] k')
        (algebraMap k' (TensorProduct k k' k') x) =
      algebraMap k' k' x := by
  -- Proof comment: the left tensor inclusion is a section of tensor-product multiplication.
  change ((TensorProduct.lmul' k).comp Algebra.TensorProduct.includeLeft) x = x
  simpa using congr($(TensorProduct.lmul'_comp_includeLeft (R := k) (S := k')) x)

/-- Helper for Lemma 10.165.6: diagonal multiplication on `k' ⊗[k] k'` as a `k'`-algebra map
for the left tensor-factor algebra structure. -/
noncomputable def separableDiagonal_lmul_leftAlgHom :
    TensorProduct k k' k' →ₐ[k'] k' :=
  { __ := (TensorProduct.lmul' k : TensorProduct k k' k' →ₐ[k] k').toRingHom
    commutes' := separableDiagonal_lmul_left_commutes (k := k) (k' := k') }

/-- Helper for Chap10 Lemma 10 165 6: normality of `K ⊗[k] A` descends to
`K ⊗[k'] A` along the separable diagonal localization `K ⊗[k] k' → K`. -/
lemma isNormalRing_tensorProduct_over_separableExtension_of_isNormalRing_baseChange
    {K : Type*} [Field K] [Algebra k K] [Algebra k' K] [IsScalarTower k k' K]
    (hKA : IsNormalRing (K ⊗[k] A)) :
    IsNormalRing (K ⊗[k'] A) := by
  obtain ⟨M, hM⟩ :=
    exists_submonoid_tensorProduct_right_isLocalization (k := k) (k' := k') (K := K)
  let algRight : Algebra k' (K ⊗[k] k') := Algebra.TensorProduct.rightAlgebra
  letI : SMul k' (K ⊗[k] k') := algRight.toSMul
  letI : Algebra k' (K ⊗[k] k') := algRight
  letI : Module k' (K ⊗[k] k') := Algebra.toModule
  let φRing : (K ⊗[k] k') →+* K :=
    (Algebra.TensorProduct.productMap
      (AlgHom.id k K) (IsScalarTower.toAlgHom k k' K)).toRingHom
  let algToK : Algebra (K ⊗[k] k') K := φRing.toAlgebra
  letI : SMul (K ⊗[k] k') K := algToK.toSMul
  letI : Algebra (K ⊗[k] k') K := algToK
  have hScalarRight :
      algebraMap k' K =
        (algebraMap (K ⊗[k] k') K).comp (algebraMap k' (K ⊗[k] k')) := by
    ext x
    change algebraMap k' K x = φRing (algebraMap k' (K ⊗[k] k') x)
    symm
    simp [φRing, RingHom.algebraMap_toAlgebra]
  letI : IsScalarTower k' (K ⊗[k] k') K :=
    @IsScalarTower.of_algebraMap_eq' k' (K ⊗[k] k') K
      inferInstance inferInstance inferInstance algRight algToK inferInstance hScalarRight
  have hlocK : IsLocalization M K := by
    rw [isLocalization_iff_isLocalizationMap]
    simpa [φRing, RingHom.algebraMap_toAlgebra] using hM
  letI : IsLocalization M K := hlocK
  have hnormalSource : IsNormalRing ((K ⊗[k] k') ⊗[k'] A) := by
    let e := tensor_base_change_assoc_equiv (k := k) (k' := k') (K := K) (B := A)
    letI : IsNormalRing (K ⊗[k] A) := hKA
    exact isNormalRing_of_ringEquiv e.symm
  letI : IsNormalRing ((K ⊗[k] k') ⊗[k'] A) := hnormalSource
  let rightR₀ : Algebra A ((K ⊗[k] k') ⊗[k'] A) := Algebra.TensorProduct.rightAlgebra
  let rightK : Algebra A (K ⊗[k'] A) := Algebra.TensorProduct.rightAlgebra
  let leftR₀ : Algebra (K ⊗[k] k') ((K ⊗[k] k') ⊗[k'] A) :=
    Algebra.TensorProduct.leftAlgebra
  let leftK : Algebra (K ⊗[k] k') (K ⊗[k'] A) := Algebra.TensorProduct.leftAlgebra
  let tensorMap : Algebra ((K ⊗[k] k') ⊗[k'] A) (K ⊗[k'] A) :=
    (Algebra.tensor_right_map (R := k') (S := K) (Q := K ⊗[k] k') (T := A)).toAlgebra
  letI : Algebra A ((K ⊗[k] k') ⊗[k'] A) := rightR₀
  letI : Algebra A (K ⊗[k'] A) := rightK
  letI : Algebra (K ⊗[k] k') ((K ⊗[k] k') ⊗[k'] A) := leftR₀
  letI : Algebra (K ⊗[k] k') (K ⊗[k'] A) := leftK
  letI : Algebra ((K ⊗[k] k') ⊗[k'] A) (K ⊗[k'] A) := tensorMap
  have hR₀tower :
      (algebraMap ((K ⊗[k] k') ⊗[k'] A) (K ⊗[k'] A)).comp
          (algebraMap (K ⊗[k] k') ((K ⊗[k] k') ⊗[k'] A)) =
        algebraMap (K ⊗[k] k') (K ⊗[k'] A) := by
    exact Algebra.tensor_right_map_q_tower (R := k') (S := K) (Q := K ⊗[k] k') (T := A)
  let hR₀towerInst :
      IsScalarTower (K ⊗[k] k') ((K ⊗[k] k') ⊗[k'] A) (K ⊗[k'] A) :=
    @IsScalarTower.of_algebraMap_eq' (K ⊗[k] k') ((K ⊗[k] k') ⊗[k'] A) (K ⊗[k'] A)
      inferInstance inferInstance inferInstance leftR₀ tensorMap leftK
      hR₀tower.symm
  letI : IsScalarTower (K ⊗[k] k') ((K ⊗[k] k') ⊗[k'] A) (K ⊗[k'] A) :=
    hR₀towerInst
  have hcompat :
      (algebraMap ((K ⊗[k] k') ⊗[k'] A) (K ⊗[k'] A)).comp
          Algebra.TensorProduct.includeRight.toRingHom =
        Algebra.TensorProduct.includeRight.toRingHom := by
    exact Algebra.tensor_right_map_includeRight_comp (R := k') (S := K) (Q := K ⊗[k] k')
      (T := A)
  letI : IsLocalization (Algebra.algebraMapSubmonoid ((K ⊗[k] k') ⊗[k'] A) M)
      (K ⊗[k'] A) :=
    @Algebra.isLocalization_tensor_right_of_isLocalization k' K
      inferInstance inferInstance inferInstance (K ⊗[k] k') inferInstance inferInstance inferInstance
      inferInstance M A inferInstance inferInstance rightR₀ rightK tensorMap hR₀towerInst
      hlocK hcompat
  -- Proof comment: the target tensor product is a localization of the normal source tensor
  -- product, so normality passes to it.
  exact isNormalRing_of_isLocalization
    (Algebra.algebraMapSubmonoid ((K ⊗[k] k') ⊗[k'] A) M)

/- Domain triage:
- `source-facing`: invariance of geometric normality under a separable algebraic extension of the
  ground field.
- `core/canonical`: the owner abstraction is `Algebra.IsGeometricallyNormal`.
- `bridge/view`: the sampled owner-style declarations are:
  `Definition_10_165_2` for the owner predicate itself,
  the local localization bridge `IsGeometricallyNormal.of_isLocalization_local`,
  the local finite-dimensional tensor-product normality bridge,
  and the parallel owner-level separable-base-change theorem
  `isGeometricallyReduced_iff_of_isSeparable` from Lemma `10.43.9`.

Primitive data are only the field-extension hypotheses and the ambient `k'`-algebra `A`.
Geometric normality stays in the owner class, and the localization/tensor-product normality facts
remain derived API rather than primitive fields of a parallel wrapper.
-/
/-- Chap10 Lemma 10 165 6: for a separable algebraic field extension `k' / k`, a `k'`-algebra
`A` is geometrically normal over `k` if and only if it is geometrically normal over `k'`. -/
-- Proof sketch: for `→`, every field extension of `k'` is in particular a field extension of `k`,
-- so the required normality statement is immediate from the owner definition. For `←`, any field
-- extension of `k` can be tensored with `k'`; separability makes the intermediate tensor product
-- geometrically normal over the larger field, and Lemmas `10.165.5` and `10.165.3` provide the
-- tensor-product and localization steps needed to descend normality back to the original
-- base-changed ring.
@[stacks 0C31]
theorem isGeometricallyNormal_iff_of_isSeparable :
    IsGeometricallyNormal k A ↔ IsGeometricallyNormal k' A := by
  constructor
  · intro h
    letI : IsGeometricallyNormal k A := h
    refine ⟨?_⟩
    intro K _ _
    letI : Algebra k K := ((algebraMap k' K).comp (algebraMap k k')).toAlgebra
    letI : IsScalarTower k k' K := IsScalarTower.of_algebraMap_eq' rfl
    have hLift : IsNormalRing (ULift.{max u v} K ⊗[k] A) :=
      IsGeometricallyNormal.isNormalRing_baseChange (k := k) (R := A) (ULift.{max u v} K)
    have hKA : IsNormalRing (K ⊗[k] A) := by
      let eLift : ULift.{max u v} K ⊗[k] A ≃+* K ⊗[k] A :=
        (Algebra.TensorProduct.congr (ULift.algEquiv (R := k) (A := K))
          (AlgEquiv.refl : A ≃ₐ[k] A)).toRingEquiv
      letI : IsNormalRing (ULift.{max u v} K ⊗[k] A) := hLift
      exact isNormalRing_of_ringEquiv eLift
    -- Proof comment: the separable diagonal presents the desired `k'`-base change as a
    -- localization of the normal `k`-base change.
    exact isNormalRing_tensorProduct_over_separableExtension_of_isNormalRing_baseChange
      (k := k) (k' := k') (A := A) hKA
  · intro h
    letI : IsGeometricallyNormal k' A := h
    -- Proof comment: the reverse direction is the same canonical instance route after restricting
    -- scalars along `k → k'`.
    letI : IsGeometricallyNormal k k' :=
      isGeometricallyNormal_of_isSeparableOver_local (k := k) (K := k')
    exact isGeometricallyNormal_restrictScalars_of_geometricallyNormal_base
      (k := k) (k' := k') (A := A)

end

end Algebra
