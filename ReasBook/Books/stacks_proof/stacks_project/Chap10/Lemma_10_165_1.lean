import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_37_11
import stacks_proof.stacks_project.Chap10.Definition_10_42_1
import stacks_proof.stacks_project.Chap10.Definition_10_54_1
import stacks_proof.stacks_project.Chap10.Lemma_10_37_13
import stacks_proof.stacks_project.Chap10.Lemma_10_37_17
import stacks_proof.stacks_project.Chap10.Lemma_10_165_1.FiniteAdjoinTensor
import stacks_proof.stacks_project.Chap10.Lemma_10_42_4
import stacks_proof.stacks_project.Chap10.Lemma_10_44_3
import stacks_proof.stacks_project.Chap10.Lemma_10_140_9
import stacks_proof.stacks_project.Chap10.Lemma_10_163_9
import stacks_proof.stacks_project.Chap10.Lemma_10_164_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

variable {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]

/- Route correction: the original skeleton quantified the test fields in an unrelated universe
`w`, but the perfect closure has universe `u`. The TFAE can only connect these clauses after
testing field extensions in a universe large enough to contain both the base field and `A`; this
matches the universe used by downstream callers. -/

/-- Helper for Chap10 Lemma 10 165 1: normality of a tensor base change descends from a
universe-lifted copy of the field. -/
lemma isNormalRing_tensorProduct_of_ulift
    {K : Type u} [Field K] [Algebra k K]
    (h : IsNormalRing (ULift.{max u v, u} K ⊗[k] A)) :
    IsNormalRing (K ⊗[k] A) := by
  -- Transport the normal-ring structure across the tensor product of the `ULift` algebra
  -- equivalence with the identity on `A`.
  letI : IsNormalRing (ULift.{max u v, u} K ⊗[k] A) := h
  let eLift : ULift.{max u v, u} K ⊗[k] A ≃+* K ⊗[k] A :=
    (Algebra.TensorProduct.congr (ULift.algEquiv (R := k) (A := K))
      (AlgEquiv.refl : A ≃ₐ[k] A)).toRingEquiv
  exact isNormalRing_of_equiv eLift

/-- Helper for Chap10 Lemma 10 165 1: normality of a tensor base change ascends to a
universe-lifted copy of the field. -/
lemma isNormalRing_tensorProduct_to_ulift
    {K : Type u} [Field K] [Algebra k K]
    (h : IsNormalRing (K ⊗[k] A)) :
    IsNormalRing (ULift.{max u v, u} K ⊗[k] A) := by
  -- Transport the normal-ring structure across the inverse tensor product equivalence.
  letI : IsNormalRing (K ⊗[k] A) := h
  let eLift : K ⊗[k] A ≃+* ULift.{max u v, u} K ⊗[k] A :=
    (Algebra.TensorProduct.congr (ULift.algEquiv (R := k) (A := K)).symm
      (AlgEquiv.refl : A ≃ₐ[k] A)).toRingEquiv
  exact isNormalRing_of_equiv eLift

/-- Helper for Chap10 Lemma 10 165 1: normality is invariant under commuting the two tensor
factors over the base field. -/
lemma isNormalRing_tensorProduct_comm_iff
    {B : Type v} [CommRing B] [Algebra k B] :
    IsNormalRing (A ⊗[k] B) ↔ IsNormalRing (B ⊗[k] A) := by
  constructor
  · intro hAB
    -- Commute the tensor factors and transport the local normality property.
    letI : IsNormalRing (A ⊗[k] B) := hAB
    let e : A ⊗[k] B ≃ₐ[k] B ⊗[k] A := Algebra.TensorProduct.comm k A B
    exact isNormalRing_of_equiv e.toRingEquiv
  · intro hBA
    -- The reverse direction is the same transport after swapping the factors.
    letI : IsNormalRing (B ⊗[k] A) := hBA
    let e : B ⊗[k] A ≃ₐ[k] A ⊗[k] B := Algebra.TensorProduct.comm k B A
    exact isNormalRing_of_equiv e.toRingEquiv

/-- Helper for Chap10 Lemma 10 165 1: normality is invariant under tensor commutativity when the
second tensor factor lives in an arbitrary universe. -/
lemma isNormalRing_tensorProduct_comm_iff_univ
    {B : Type w} [CommRing B] [Algebra k B] :
    IsNormalRing (A ⊗[k] B) ↔ IsNormalRing (B ⊗[k] A) := by
  constructor
  · intro hAB
    -- Commute the tensor factors and transport normality across the algebra equivalence.
    letI : IsNormalRing (A ⊗[k] B) := hAB
    let e : A ⊗[k] B ≃ₐ[k] B ⊗[k] A := Algebra.TensorProduct.comm k A B
    exact isNormalRing_of_equiv e.toRingEquiv
  · intro hBA
    -- The reverse direction repeats the same transport after swapping the two factors.
    letI : IsNormalRing (B ⊗[k] A) := hBA
    let e : B ⊗[k] A ≃ₐ[k] A ⊗[k] B := Algebra.TensorProduct.comm k B A
    exact isNormalRing_of_equiv e.toRingEquiv

/-- Helper for Chap10 Lemma 10 165 1: tensor-product normality descends along a field extension
of the left tensor factor. -/
lemma isNormalRing_tensorProduct_descends_along_fieldAlgHom
    {E L : Type (max u v)} [Field E] [Field L] [Algebra k E] [Algebra k L]
    (i : E →ₐ[k] L) (hL : IsNormalRing (L ⊗[k] A)) :
    IsNormalRing (E ⊗[k] A) := by
  -- View `L` as an `E`-algebra through `i`, then base-change the faithfully flat field map
  -- along `E → E ⊗[k] A`.
  letI : Algebra E L := i.toRingHom.toAlgebra
  have hscalar : IsScalarTower k E L := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext x
    exact (i.commutes x).symm
  letI : IsScalarTower k E L := hscalar
  letI : Algebra E (E ⊗[k] A) := Algebra.TensorProduct.leftAlgebra
  letI : Algebra (E ⊗[k] A) (L ⊗[E] (E ⊗[k] A)) :=
    Algebra.TensorProduct.rightAlgebra
  letI : Algebra.IsPushout E L (E ⊗[k] A) (L ⊗[E] (E ⊗[k] A)) := by
    infer_instance
  have hff : (algebraMap E L).FaithfullyFlat := by
    letI : Module.FaithfullyFlat E L := Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  have hffBase :
      (algebraMap (E ⊗[k] A) (L ⊗[E] (E ⊗[k] A))).FaithfullyFlat := by
    exact RingHom.FaithfullyFlat.isStableUnderBaseChange (R := E) (S := L)
      (R' := E ⊗[k] A) (S' := L ⊗[E] (E ⊗[k] A)) hff
  let eCancel : (L ⊗[E] (E ⊗[k] A)) ≃+* (L ⊗[k] A) :=
    (Algebra.TensorProduct.cancelBaseChange k E L L A).toRingEquiv
  letI : IsNormalRing (L ⊗[E] (E ⊗[k] A)) := by
    letI : IsNormalRing (L ⊗[k] A) := hL
    -- The iterated tensor target is the usual tensor product after canceling the base change.
    exact isNormalRing_of_equiv eCancel.symm
  exact
    isNormalRing_of_faithfullyFlat
      (algebraMap (E ⊗[k] A) (L ⊗[E] (E ⊗[k] A))) hffBase

/-- Helper for Chap10 Lemma 10 165 1: a smooth subalgebra whose fraction field is `L` makes
`L ⊗[κ] T` normal after tensoring a normal `κ`-algebra `T`. -/
lemma normality_tensorProduct_of_smoothFractionFieldModel
    {κ : Type*} {L : Type*} {T : Type*}
    [Field κ] [Field L] [CommRing T]
    [Algebra κ L] [Algebra κ T] [IsNormalRing T]
    (B : Subalgebra κ L) [Algebra.Smooth κ B] [IsFractionRing B L] :
    IsNormalRing (L ⊗[κ] T) := by
  letI : IsNormalRing (T ⊗[κ] B) := by
    -- Smooth base change from `κ → B` to the normal ring `T` gives normality of `T ⊗ B`.
    letI : Algebra.Smooth T (T ⊗[κ] B) := inferInstance
    exact isNormalRing_of_smooth (R := T) (S := T ⊗[κ] B)
  letI : IsNormalRing (B ⊗[κ] T) :=
    -- Put the normal tensor product in the orientation used by the localization theorem.
    (isNormalRing_tensorProduct_comm_iff_univ (k := κ) (A := T) (B := B)).mp inferInstance
  letI : Algebra B L := B.toAlgebra
  letI : IsScalarTower κ B L := inferInstance
  let rightB : Algebra T (B ⊗[κ] T) :=
    Algebra.TensorProduct.rightAlgebra (R := κ) (A := B) (B := T)
  let rightL : Algebra T (L ⊗[κ] T) :=
    Algebra.TensorProduct.rightAlgebra (R := κ) (A := L) (B := T)
  let leftB : Algebra B (B ⊗[κ] T) := Algebra.TensorProduct.leftAlgebra
  let leftL : Algebra B (L ⊗[κ] T) := Algebra.TensorProduct.leftAlgebra
  let tensorBL : Algebra (B ⊗[κ] T) (L ⊗[κ] T) :=
    (Algebra.tensor_right_map (R := κ) (S := L) (Q := B) (T := T)).toAlgebra
  letI : Algebra T (B ⊗[κ] T) := rightB
  letI : Algebra T (L ⊗[κ] T) := rightL
  letI : Algebra B (B ⊗[κ] T) := leftB
  letI : Algebra B (L ⊗[κ] T) := leftL
  letI : Algebra (B ⊗[κ] T) (L ⊗[κ] T) := tensorBL
  have hBtower :
      (algebraMap (B ⊗[κ] T) (L ⊗[κ] T)).comp (algebraMap B (B ⊗[κ] T)) =
        algebraMap B (L ⊗[κ] T) := by
    exact Algebra.tensor_right_map_q_tower (R := κ) (S := L) (Q := B) (T := T)
  let hBtowerInst : IsScalarTower B (B ⊗[κ] T) (L ⊗[κ] T) :=
    @IsScalarTower.of_algebraMap_eq' B (B ⊗[κ] T) (L ⊗[κ] T)
      inferInstance inferInstance inferInstance leftB tensorBL leftL hBtower.symm
  letI : IsScalarTower B (B ⊗[κ] T) (L ⊗[κ] T) := hBtowerInst
  have hcompat :
      (algebraMap (B ⊗[κ] T) (L ⊗[κ] T)).comp
          Algebra.TensorProduct.includeRight.toRingHom =
        Algebra.TensorProduct.includeRight.toRingHom := by
    -- The tensor-localization map fixes the right tensor factor by construction.
    exact Algebra.tensor_right_map_includeRight_comp (R := κ) (S := L) (Q := B) (T := T)
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid (B ⊗[κ] T) (nonZeroDivisors B))
      (L ⊗[κ] T) :=
    @Algebra.isLocalization_tensor_right_of_isLocalization κ L
      inferInstance inferInstance inferInstance B inferInstance inferInstance B.toAlgebra
      inferInstance (nonZeroDivisors B) T inferInstance inferInstance rightB rightL tensorBL
      hBtowerInst inferInstance hcompat
  letI : IsLocalization (Algebra.algebraMapSubmonoid (B ⊗[κ] T) (nonZeroDivisors B))
      (L ⊗[κ] T) := hloc
  -- Localizing a normal ring is normal, so pass from `B ⊗ T` to `L ⊗ T`.
  exact isNormalRing_of_isLocalization
    (Algebra.algebraMapSubmonoid (B ⊗[κ] T) (nonZeroDivisors B))

/-- Helper for Chap10 Lemma 10 165 1: normality for all essentially finite type field
extensions implies normality for all field extensions. -/
lemma allField_tensorProduct_isNormalRing_of_essFiniteType_tests
    (hess :
      ∀ (k' : Type (max u v)) [Field k'] [Algebra k k'] [Algebra.EssFiniteType k k'],
        IsNormalRing (k' ⊗[k] A)) :
    ∀ (k' : Type (max u v)) [Field k'] [Algebra k k'], IsNormalRing (k' ⊗[k] A) := by
  intro K _ _
  -- Reduce the arbitrary field extension to the finite-adjoin tensor stages. Each stage is
  -- essentially finite type over `k`, so the hypothesis supplies its normality.
  refine isNormalRing_tensorProduct_of_finiteAdjoin_stage_tests (A := A) (K := K) ?_
  intro s
  letI : Algebra.EssFiniteType k (IntermediateField.adjoin k (s : Set K)) :=
    finiteAdjoin_stage_essFiniteType (k := k) (K := K) s
  exact hess (IntermediateField.adjoin k (s : Set K))

/-- Helper for Chap10 Lemma 10 165 1: the finite-type witness subalgebra of an essentially
finite type field extension has the ambient field as its fraction field. -/
lemma essFiniteTypeSubalgebra_isFractionRing_for_tensorNormality
    {κ : Type u} {K : Type (max u v)} [Field κ] [Field K] [Algebra κ K]
    [Algebra.EssFiniteType κ K] :
    IsFractionRing (Algebra.EssFiniteType.subalgebra κ K) K := by
  let B : Subalgebra κ K := Algebra.EssFiniteType.subalgebra κ K
  let S : Submonoid B := Algebra.EssFiniteType.submonoid κ K
  have hinj : Function.Injective (algebraMap B K) := by
    intro x y hxy
    exact Subtype.ext hxy
  have hfaith : FaithfulSMul B K :=
    (faithfulSMul_iff_algebraMap_injective B K).mpr hinj
  letI : FaithfulSMul B K := hfaith
  refine IsFractionRing.of_field B K ?_
  intro z
  obtain ⟨⟨x, s⟩, hz⟩ := IsLocalization.surj S z
  refine ⟨x, s, ?_⟩
  have hsunit : IsUnit (algebraMap B K s) := s.2
  have hsne : algebraMap B K s ≠ 0 := by
    intro hzero
    rw [hzero] at hsunit
    exact not_isUnit_zero hsunit
  -- The essential-finiteness localization writes every field element as a quotient from `B`.
  exact (eq_div_iff_mul_eq hsne).2 hz

/-- Helper for Chap10 Lemma 10 165 1: a smooth localization of a subalgebra remains smooth
after realizing it as a subalgebra of the ambient fraction field. -/
lemma smoothLocalizationSubalgebra_restrictScalars_for_tensorNormality
    {κ : Type u} {B : Type (max u v)} {K : Type (max u v)}
    [CommRing κ] [CommRing B] [Field K]
    [Algebra κ B] [Algebra B K] [Algebra κ K] [IsScalarTower κ B K]
    [IsFractionRing B K] (S : Submonoid B) (hS : S ≤ nonZeroDivisors B)
    [Algebra.Smooth κ (Localization S)] :
    Algebra.Smooth κ ((Localization.subalgebra.ofField K S hS).restrictScalars κ) := by
  let C : Subalgebra B K := Localization.subalgebra.ofField K S hS
  let e : Localization S ≃ₐ[B] C :=
    IsLocalization.algEquiv S (Localization S) C
  -- Transport smoothness across the canonical localization equivalence inside the fraction field.
  exact Algebra.Smooth.of_equiv (A := Localization S) (B := C) (R := κ) (e.restrictScalars κ)

/-- Helper for Chap10 Lemma 10 165 1: restricting scalars on a fraction-field subalgebra does
not change its fraction-field structure. -/
lemma isFractionRing_restrictScalars_for_tensorNormality
    {κ : Type u} {B : Type (max u v)} {K : Type (max u v)}
    [CommSemiring κ] [CommSemiring B] [Semifield K]
    [Algebra κ B] [Algebra B K] [Algebra κ K] [IsScalarTower κ B K]
    (C : Subalgebra B K) [IsFractionRing C K] :
    IsFractionRing (C.restrictScalars κ) K := by
  -- The carrier and its inclusion into `K` are unchanged; only the scalar ring is forgotten.
  convert (inferInstance : IsFractionRing C K)

/-- Helper for Chap10 Lemma 10 165 1: a separable essentially finite type field extension is the
fraction field of a smooth subalgebra. -/
lemma exists_smoothSubalgebra_fractionRing_of_isSeparableOver_for_tensorNormality
    {κ : Type u} {K : Type (max u v)} [Field κ] [Field K] [Algebra κ K]
    [Algebra.EssFiniteType κ K] (hsep : Algebra.IsSeparableOver κ K) :
    ∃ B : Subalgebra κ K, Algebra.Smooth κ B ∧ IsFractionRing B K := by
  let B : Subalgebra κ K := Algebra.EssFiniteType.subalgebra κ K
  have hfrac : IsFractionRing B K :=
    essFiniteTypeSubalgebra_isFractionRing_for_tensorNormality (κ := κ) (K := K)
  letI : IsFractionRing B K := hfrac
  letI : Algebra.IsSeparableOver κ K := hsep
  letI : Algebra.FormallySmooth κ K := Algebra.formallySmooth_of_isSeparableOver
  have hsmoothFrac : Algebra.FormallySmooth κ (FractionRing B) := by
    let e : FractionRing B ≃ₐ[κ] K :=
      (FractionRing.algEquiv B K).restrictScalars κ
    exact (Algebra.FormallySmooth.iff_of_equiv e).2 inferInstance
  have hsmoothAt : Algebra.IsSmoothAt κ (⊥ : Ideal B) := by
    exact (Algebra.isSmoothAt_bot_iff_formallySmooth_fractionRing (R := κ) (S := B)).2
      hsmoothFrac
  have hfinitePresentation : Algebra.FinitePresentation κ B :=
    (Algebra.FinitePresentation.of_finiteType (R := κ) (A := B)).1 inferInstance
  letI : Algebra.FinitePresentation κ B := hfinitePresentation
  obtain ⟨g, hg, hsm⟩ :=
    Algebra.IsSmoothAt.exists_notMem_smooth κ (A := B) (⊥ : Ideal B)
  let S : Submonoid B := Submonoid.powers g
  have hS : S ≤ nonZeroDivisors B := by
    intro s hs
    rw [mem_nonZeroDivisors_iff_ne_zero]
    obtain ⟨n, rfl⟩ := hs
    have hg0 : g ≠ 0 := by
      intro hgzero
      have hgmem : g ∈ (⊥ : Ideal B) := by
        simp [hgzero]
      exact hg hgmem
    exact pow_ne_zero n hg0
  let C : Subalgebra B K := Localization.subalgebra.ofField K S hS
  let A : Subalgebra κ K := C.restrictScalars κ
  refine ⟨A, ?_, ?_⟩
  · letI : Algebra.Smooth κ (Localization S) := hsm
    -- Replace the smooth basic open by its image subalgebra inside the fraction field.
    exact smoothLocalizationSubalgebra_restrictScalars_for_tensorNormality
      (κ := κ) (B := B) (K := K) S hS
  · dsimp [A, C]
    exact isFractionRing_restrictScalars_for_tensorNormality (κ := κ) (B := B) (K := K)
      (Localization.subalgebra.ofField K S hS)

/-- Helper for Chap10 Lemma 10 165 1: the source lift square transfers tensor normality from the
finite purely inseparable base field to the original essentially finite type field. -/
lemma isNormalRing_tensorProduct_of_purelyInseparable_lift
    {K : Type (max u v)} [Field K] [Algebra k K] [Algebra.EssFiniteType k K]
    {k' : Type (max u v)} [Field k'] [Algebra k k']
    {K' : Type (max u v)} [Field K'] [Algebra k K'] [Algebra K K'] [Algebra k' K']
    [IsScalarTower k K K'] [IsScalarTower k k' K']
    (hlift : IsPurelyInseparableLiftWithSeparablyGenerated k K k' K')
    (hbase : IsNormalRing (k' ⊗[k] A)) :
    IsNormalRing (K ⊗[k] A) := by
  letI : FiniteDimensional K K' := hlift.finiteDimensional_top
  letI : IsPurelyInseparable K K' := hlift.purelyInseparable_top
  letI : FiniteDimensional k k' := hlift.finiteDimensional_base
  letI : IsPurelyInseparable k k' := hlift.purelyInseparable_base
  letI : Algebra.IsSeparablyGenerated k' K' := hlift.separablyGenerated_top
  letI : Algebra.IsAlgebraic k k' := IsPurelyInseparable.isAlgebraic k k'
  letI : Algebra.EssFiniteType K K' := inferInstance
  letI : Algebra.EssFiniteType k K' := Algebra.EssFiniteType.comp k K K'
  letI : Algebra.EssFiniteType k' K' := Algebra.EssFiniteType.of_comp k k' K'
  have hsep : Algebra.IsSeparableOver k' K' := Algebra.Lemma_10_44_3 hlift.separablyGenerated_top
  obtain ⟨B, hSmooth, hFraction⟩ :=
    exists_smoothSubalgebra_fractionRing_of_isSeparableOver_for_tensorNormality
      (κ := k') (K := K') hsep
  have hLiftedNormal : IsNormalRing (K' ⊗[k'] (k' ⊗[k] A)) := by
    -- The lifted top field has a smooth fraction-field model over the lifted base field.
    letI : IsNormalRing (k' ⊗[k] A) := hbase
    letI : Algebra.Smooth k' B := hSmooth
    letI : IsFractionRing B K' := hFraction
    exact normality_tensorProduct_of_smoothFractionFieldModel
      (κ := k') (L := K') (T := k' ⊗[k] A) B
  let eCancel : K' ⊗[k'] (k' ⊗[k] A) ≃+* K' ⊗[k] A :=
    (Algebra.TensorProduct.cancelBaseChange k k' K' K' A).toRingEquiv
  have hK'TensorNormal : IsNormalRing (K' ⊗[k] A) := by
    -- Cancel the iterated base change before descending along the finite top extension.
    letI : IsNormalRing (K' ⊗[k'] (k' ⊗[k] A)) := hLiftedNormal
    exact isNormalRing_of_equiv eCancel
  -- Finally descend normality from the finite purely inseparable top field back to `K`.
  exact
    isNormalRing_tensorProduct_descends_along_fieldAlgHom (A := A)
      (IsScalarTower.toAlgHom k K K') hK'TensorNormal

/-- Helper for Chap10 Lemma 10 165 1: a separably generated field extension in the project
owner sense is formally smooth over its base field. -/
lemma formallySmooth_of_isSeparablyGenerated_fieldExtension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsSeparablyGenerated K L] :
    Algebra.FormallySmooth K L := by
  -- Unpack the source-facing separably generated witness and feed the separating
  -- transcendence basis to mathlib's formally smooth field-extension theorem.
  rcases (inferInstance : Algebra.IsSeparablyGenerated K L) with ⟨s, hs, hsep⟩
  have hsRange : Set.range ((↑) : s → L) = s := by
    ext x
    simp
  letI : Algebra.IsSeparable (IntermediateField.adjoin K (Set.range ((↑) : s → L))) L := by
    rw [hsRange]
    exact hsep
  exact Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1

/-- Helper for Chap10 Lemma 10 165 1: finite purely inseparable tensor-normality tests imply the
same tests for essentially finite type field extensions. -/
lemma essFiniteType_tensorProduct_isNormalRing_of_finitePurelyInseparable_tests
    (hfinite :
      ∀ (k' : Type (max u v)) [Field k'] [Algebra k k'] [FiniteDimensional k k']
        [IsPurelyInseparable k k'],
        IsNormalRing (k' ⊗[k] A)) :
    ∀ (k' : Type (max u v)) [Field k'] [Algebra k k'] [Algebra.EssFiniteType k k'],
      IsNormalRing (k' ⊗[k] A) := by
  intro K _ _ _
  obtain ⟨k', hk'Field, hk'Alg, K', hK'Field, hkK', hKK', hk'K', hkKK', hkk'K',
    hlift⟩ :
      ∃ (k' : Type (max u v)) (_ : Field k') (_ : Algebra k k')
        (K' : Type (max (max u v) (max u v))) (_ : Field K') (_ : Algebra k K')
        (_ : Algebra K K') (_ : Algebra k' K')
        (_ : IsScalarTower k K K') (_ : IsScalarTower k k' K'),
          IsPurelyInseparableLiftWithSeparablyGenerated k K k' K' :=
    exists_purelyInseparable_lift_with_separablyGenerated (k := k) (K := K)
  letI : Field k' := hk'Field
  letI : Algebra k k' := hk'Alg
  letI : Field K' := hK'Field
  letI : Algebra k K' := hkK'
  letI : Algebra K K' := hKK'
  letI : Algebra k' K' := hk'K'
  letI : IsScalarTower k K K' := hkKK'
  letI : IsScalarTower k k' K' := hkk'K'
  letI : FiniteDimensional k k' := hlift.finiteDimensional_base
  letI : IsPurelyInseparable k k' := hlift.purelyInseparable_base
  have hbase : IsNormalRing (k' ⊗[k] A) := hfinite k'
  -- Apply the source lift bridge: finite purely inseparable normality on the base, smooth
  -- normality on the separably generated top, cancellation, then faithful-flat descent.
  exact
    isNormalRing_tensorProduct_of_purelyInseparable_lift
      (k := k) (A := A) (K := K) (k' := k') (K' := K') hlift hbase

/-- Helper for Chap10 Lemma 10 165 1: a purely inseparable extension of `k` embeds into the
chosen relative perfect closure inside `AlgebraicClosure k`. -/
lemma exists_algHom_to_perfectClosure_of_purelyInseparable_for_normality
    (k' : Type (max u v)) [Field k'] [Algebra k k'] [IsPurelyInseparable k k'] :
    ∃ f : k' →ₐ[k] perfectClosure k (AlgebraicClosure k), Function.Injective f := by
  -- Lift the field to the algebraic closure, identify it with its field range, and use the
  -- defining property of the perfect closure for purely inseparable subextensions.
  let f₀ : k' →ₐ[k] AlgebraicClosure k := IsAlgClosed.lift
  let e : k' ≃ₐ[k] f₀.fieldRange := AlgEquiv.ofInjectiveField f₀
  letI : IsPurelyInseparable k f₀.fieldRange := e.isPurelyInseparable
  have hle : f₀.fieldRange ≤ perfectClosure k (AlgebraicClosure k) :=
    le_perfectClosure k (AlgebraicClosure k) f₀.fieldRange
  refine ⟨(IntermediateField.inclusion hle).comp e.toAlgHom, ?_⟩
  exact (IntermediateField.inclusion hle).injective.comp e.injective

/-- Helper for Chap10 Lemma 10 165 1: normality after base change to the perfect closure implies
normality after every finite purely inseparable field extension. -/
lemma finitePurelyInseparable_tensorProduct_isNormalRing_of_perfectClosure
    (hperf : IsNormalRing (perfectClosure k (AlgebraicClosure k) ⊗[k] A)) :
    ∀ (k' : Type (max u v)) [Field k'] [Algebra k k'] [FiniteDimensional k k']
      [IsPurelyInseparable k k'],
      IsNormalRing (k' ⊗[k] A) := by
  intro k' _ _ _ _
  -- Embed the purely inseparable test field into the perfect closure and then into its universe
  -- lift, so the descent bridge has the expected field universe.
  obtain ⟨f, _hf⟩ :=
    exists_algHom_to_perfectClosure_of_purelyInseparable_for_normality (k := k) (k' := k')
  let P := perfectClosure k (AlgebraicClosure k)
  let i : k' →ₐ[k] ULift.{max u v, u} P :=
    (ULift.algEquiv (R := k) (A := P)).symm.toAlgHom.comp f
  exact
    isNormalRing_tensorProduct_descends_along_fieldAlgHom (A := A) i
      (isNormalRing_tensorProduct_to_ulift (A := A) (K := P) hperf)

/- Domain triage:
- `source-facing`: the four-way field-extension criterion for normality in Lemma `10.165.1`;
- `core/canonical`: the ring-level owner `IsNormalRing` together with the tensor base-change
  objects `k' ⊗[k] A`;
- `bridge/view`: the pairwise clause projections extracted from the `List.TFAE`.

The theorem below should remain the source-facing TFAE. The individual implications among its
clauses are derived API and should be named once here, then reused downstream instead of rebuilding
the same proposition list locally.
-/
-- Proof sketch: `(1) → (2) → (3)` and `(1) → (4)` are immediate. For `(4) → (3)`, embed any
-- finite purely inseparable extension into the chosen perfect closure and descend normality along
-- the induced faithfully flat base-change map. For `(2) → (1)`, write an arbitrary field
-- extension as a directed colimit of finitely generated subextensions and apply stability of
-- normality under filtered colimits. For `(3) → (2)`, replace a finitely generated extension by a
-- finite purely inseparable extension that becomes separable over a finite purely inseparable
-- extension of the base, then use ascent along smooth algebras, localization, and faithful-flat
-- descent.
/-- Chap10 Lemma 10 165 1: for a commutative `k`-algebra `A`, the following are equivalent:
every base change `k' ⊗[k] A` to a field extension `k' / k` is a normal ring, it suffices to check
this for finitely generated field extensions, it suffices to check this for finite purely
inseparable field extensions, and it suffices to check it after base change to the chosen model
`perfectClosure k (AlgebraicClosure k)` of `k^{perf}`. -/
@[stacks 037Z]
theorem isNormalRing_tensorProduct_tfae_essFiniteType_finitePurelyInseparable_perfectClosure :
    List.TFAE [
      ∀ (k' : Type (max u v)) [Field k'] [Algebra k k'], IsNormalRing (k' ⊗[k] A),
      ∀ (k' : Type (max u v)) [Field k'] [Algebra k k'] [Algebra.EssFiniteType k k'],
        IsNormalRing (k' ⊗[k] A),
      ∀ (k' : Type (max u v)) [Field k'] [Algebra k k'] [FiniteDimensional k k']
        [IsPurelyInseparable k k'],
        IsNormalRing (k' ⊗[k] A),
      IsNormalRing (perfectClosure k (AlgebraicClosure k) ⊗[k] A)
    ] := by
  tfae_have 1 → 2 := by
    intro hall k' _ _ _
    -- The unrestricted test immediately specializes to essentially finite type extensions.
    exact hall k'
  tfae_have 2 → 3 := by
    intro hess k' _ _ _ _
    -- A finite-dimensional field extension is essentially finite type, so this is another
    -- specialization of the second clause.
    exact hess k'
  tfae_have 1 → 4 := by
    intro hall
    -- Test the universe-lifted perfect closure, then transport normality back down.
    exact isNormalRing_tensorProduct_of_ulift (K := perfectClosure k (AlgebraicClosure k))
      (hall (ULift.{max u v, u} (perfectClosure k (AlgebraicClosure k))))
  tfae_have 2 → 1 := by
    intro hess
    -- The filtered-colimit helper upgrades essentially finite type tests to all fields.
    exact allField_tensorProduct_isNormalRing_of_essFiniteType_tests hess
  tfae_have 3 → 2 := by
    intro hfinite
    -- The finite purely inseparable helper is the source proof's reduction of finitely generated
    -- field extensions to finite purely inseparable base changes.
    exact essFiniteType_tensorProduct_isNormalRing_of_finitePurelyInseparable_tests hfinite
  tfae_have 4 → 3 := by
    intro hperf
    -- Perfect-closure normality descends to every finite purely inseparable test field.
    exact finitePurelyInseparable_tensorProduct_isNormalRing_of_perfectClosure hperf
  tfae_finish

/-- Lemma 10.165.1, clauses `(1) ↔ (3)`: it is enough to test normality of all tensor base
changes `k' ⊗[k] A` on finite purely inseparable field extensions `k' / k`. -/
@[stacks 037Z]
theorem forall_isNormalRing_tensorProduct_iff_finitePurelyInseparable :
    (∀ (k' : Type (max u v)) [Field k'] [Algebra k k'], IsNormalRing (k' ⊗[k] A)) ↔
      ∀ (k' : Type (max u v)) [Field k'] [Algebra k k'] [FiniteDimensional k k']
        [IsPurelyInseparable k k'],
        IsNormalRing (k' ⊗[k] A) := by
  let l : List Prop := [
    ∀ (k' : Type (max u v)) [Field k'] [Algebra k k'], IsNormalRing (k' ⊗[k] A),
    ∀ (k' : Type (max u v)) [Field k'] [Algebra k k'] [Algebra.EssFiniteType k k'],
      IsNormalRing (k' ⊗[k] A),
    ∀ (k' : Type (max u v)) [Field k'] [Algebra k k'] [FiniteDimensional k k']
      [IsPurelyInseparable k k'],
      IsNormalRing (k' ⊗[k] A),
    IsNormalRing (perfectClosure k (AlgebraicClosure k) ⊗[k] A)
  ]
  have htfae : List.TFAE l := by
    -- Reuse the main TFAE with the proposition list named for stable projection.
    simpa [l] using
      isNormalRing_tensorProduct_tfae_essFiniteType_finitePurelyInseparable_perfectClosure
  -- Project clauses `(1)` and `(3)` from the already-assembled TFAE.
  simpa [l] using htfae.out 0 2 (by simp [l]) (by simp [l])

end
