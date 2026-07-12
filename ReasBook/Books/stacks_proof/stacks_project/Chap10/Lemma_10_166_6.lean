import Mathlib
import StacksProject_2024.Chap10.Lemma_10_43_9
import StacksProject_2024.Chap10.Lemma_10_46_8
import StacksProject_2024.Chap10.Lemma_10_166_1
import StacksProject_2024.Chap10.Lemma_10_166_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

namespace Algebra

section

variable {k : Type u} {k' : Type u} {A : Type w}
variable [Field k] [Field k'] [CommRing A]
variable [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
variable [Algebra.IsSeparable k k']

/-- Helper for Chap10 Lemma 10 166 6: a localization of a regular ring is regular. -/
private lemma isRegularRingOfLocalization
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] [IsRegularRing R] :
    IsRegularRing S := by
  -- Proof comment: compare local rings at corresponding primes and transport regular locality
  -- across the canonical localization equivalence.
  letI : IsNoetherianRing S := IsLocalization.isNoetherianRing M S inferInstance
  refine ⟨fun q ↦ ?_⟩
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  letI : IsRegularLocalRing (Localization.AtPrime p.asIdeal) :=
    IsRegularRing.isRegularLocalRing_atPrime p
  letI : IsLocalization.AtPrime (Localization.AtPrime q.asIdeal) p.asIdeal := by
    simpa [p, PrimeSpectrum.comap_asIdeal] using
      (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        M
        (Localization.AtPrime q.asIdeal)
        q.asIdeal)
  let e : Localization.AtPrime p.asIdeal ≃ₐ[R] Localization.AtPrime q.asIdeal :=
    IsLocalization.algEquiv p.asIdeal.primeCompl
      (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal)
  exact IsRegularLocalRing.of_ringEquiv (R := Localization.AtPrime p.asIdeal) e.toRingEquiv

/-- Helper for Chap10 Lemma 10 166 6: regularity of `K ⊗[k] A` descends to
`K ⊗[k'] A` along the separable diagonal localization `K ⊗[k] k' → K`. -/
private lemma isRegularRing_tensorProduct_over_separableExtension_of_isRegularRing_baseChange
    {K : Type (max u w)} [Field K] [Algebra k K] [Algebra k' K] [IsScalarTower k k' K]
    (hKA : IsRegularRing (K ⊗[k] A)) :
    IsRegularRing (K ⊗[k'] A) := by
  -- Route correction: the blocked route is closed by the same normal form as the normality
  -- sibling proof: first use the imported diagonal localization for `K ⊗[k] k' → K`, then tensor
  -- that localization on the right by `A`.
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
  letI : CommRing ((K ⊗[k] k') ⊗[k'] A) := inferInstance
  have hregularSource : IsRegularRing ((K ⊗[k] k') ⊗[k'] A) := by
    let e := tensor_base_change_assoc_equiv (k := k) (k' := k') (K := K) (B := A)
    letI : IsRegularRing (K ⊗[k] A) := hKA
    exact
      @isRegularRing_of_ringEquiv (K ⊗[k] A) ((K ⊗[k] k') ⊗[k'] A)
        inferInstance inferInstance e.symm inferInstance
  letI : IsRegularRing ((K ⊗[k] k') ⊗[k'] A) := hregularSource
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
  -- Proof comment: the target tensor product is now a localization of the regular source tensor
  -- product, so regularity passes to it.
  exact isRegularRingOfLocalization
    (Algebra.algebraMapSubmonoid ((K ⊗[k] k') ⊗[k'] A) M)

/-- Helper for Chap10 Lemma 10 166 6: geometric regularity ascends over a finite separable base
field extension. -/
private lemma isGeometricallyRegular_of_finiteSeparable_base
    {k F : Type u} {A : Type w} [Field k] [Field F] [CommRing A]
    [Algebra k F] [Algebra k A] [Algebra F A] [IsScalarTower k F A]
    [FiniteDimensional k F] [Algebra.IsSeparable k F]
    (h : IsGeometricallyRegular k A) :
    IsGeometricallyRegular F A := by
  -- Proof comment: use the essentially finite type criterion over `F`; after restricting scalars
  -- to `k`, the same test field is essentially finite type over `k`.
  rw [isGeometricallyRegular_iff_forall_essFiniteType_fieldExtension_tensorBaseChange_isRegularRing]
  intro L _ _ _
  letI : Algebra k L := ((algebraMap F L).comp (algebraMap k F)).toAlgebra
  letI : IsScalarTower k F L := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.EssFiniteType k L := Algebra.EssFiniteType.comp k F L
  have hBaseRegular : IsRegularRing (L ⊗[k] A) := by
    exact
      (isGeometricallyRegular_iff_forall_essFiniteType_fieldExtension_tensorBaseChange_isRegularRing
        (k := k) (A := A)).1 h L
  -- Proof comment: the diagonal-localization bridge now converts that regularity into the
  -- required `F`-tensor product.
  exact
    isRegularRing_tensorProduct_over_separableExtension_of_isRegularRing_baseChange
      (k := k) (k' := F) (A := A) (K := L) hBaseRegular

/-- Helper for Chap10 Lemma 10 166 6: finite-dimensional intermediate fields of a separable
extension are nonempty. -/
private lemma finiteDimensionalIntermediateField_nonempty
    {k : Type u} {k' : Type v} [Field k] [Field k'] [Algebra k k'] :
    Nonempty {F : IntermediateField k k' // FiniteDimensional k F} := by
  -- Proof comment: the bottom intermediate field is just the base field.
  refine ⟨⟨⊥, ?_⟩⟩
  infer_instance

/-- Helper for Chap10 Lemma 10 166 6: finite-dimensional intermediate fields are directed by
compositum. -/
private lemma finiteDimensionalIntermediateField_directed
    {k : Type u} {k' : Type v} [Field k] [Field k'] [Algebra k k'] :
    Directed (· ≤ ·)
      (fun F : {F : IntermediateField k k' // FiniteDimensional k F} ↦ F.1.toSubfield) := by
  -- Proof comment: the supremum of two finite-dimensional intermediate fields is
  -- finite-dimensional and contains both fields.
  intro F G
  letI : FiniteDimensional k F.1 := F.2
  letI : FiniteDimensional k G.1 := G.2
  refine ⟨⟨F.1 ⊔ G.1, ?_⟩, ?_, ?_⟩
  · exact IntermediateField.finiteDimensional_sup F.1 G.1
  · intro x hx
    exact
      (show x ∈ (F.1 ⊔ G.1 : IntermediateField k k') from
        (le_sup_left : F.1 ≤ F.1 ⊔ G.1) hx)
  · intro x hx
    exact
      (show x ∈ (F.1 ⊔ G.1 : IntermediateField k k') from
        (le_sup_right : G.1 ≤ F.1 ⊔ G.1) hx)

/-- Helper for Chap10 Lemma 10 166 6: finite-dimensional intermediate fields cover a separable
extension. -/
private lemma finiteDimensionalIntermediateField_iSup_eq_top :
    iSup (fun F : {F : IntermediateField k k' // FiniteDimensional k F} ↦ F.1.toSubfield) = ⊤ := by
  -- Proof comment: each element lies in the simple intermediate field it generates; separability
  -- makes that simple field finite-dimensional over the base.
  letI : Nonempty {F : IntermediateField k k' // FiniteDimensional k F} :=
    finiteDimensionalIntermediateField_nonempty (k := k) (k' := k')
  apply top_unique
  intro x _
  rw [Subfield.mem_iSup_of_directed (finiteDimensionalIntermediateField_directed (k := k) (k' := k'))]
  let F : IntermediateField k k' := IntermediateField.adjoin k ({x} : Set k')
  have hfin : FiniteDimensional k F := by
    simpa [F] using IntermediateField.adjoin.finiteDimensional (Algebra.IsSeparable.isIntegral k x)
  refine ⟨⟨F, hfin⟩, ?_⟩
  exact IntermediateField.mem_adjoin_of_mem k (by simp)

/-- Helper for Chap10 Lemma 10 166 6: geometric regularity over `k` ascends to each
finite-dimensional intermediate subfield of `k' / k`. -/
private lemma isGeometricallyRegular_of_finiteDimensionalIntermediateField
    (F : {F : IntermediateField k k' // FiniteDimensional k F})
    (h : IsGeometricallyRegular k A) :
    IsGeometricallyRegular (F.1.toSubfield) A := by
  -- Proof comment: combine finite separable base ascent with the canonical algebra structure on
  -- the intermediate subfield carrier.
  letI : FiniteDimensional k F.1 := F.2
  -- Proof comment: the finite intermediate field is separable because it sits inside the
  -- separable extension `k' / k`, so the finite-separable ascent helper applies.
  simpa using
    (isGeometricallyRegular_of_finiteSeparable_base (k := k) (F := F.1) (A := A) h)

/-- Helper for Chap10 Lemma 10 166 6: a purely inseparable field extension is linearly disjoint
from a separable field extension, so their tensor product is a field. -/
private lemma tensorProduct_isField_of_purelyInseparable_left_separable_right
    {K : Type (max u w)} [Field K] [Algebra k K] [IsPurelyInseparable k K] :
    IsField (K ⊗[k] k') := by
  -- Proof comment: use the field criterion for tensor products and reduce every comparison in a
  -- common field to the standard linear-disjointness theorem for pure/separable subfields.
  refine IntermediateField.LinearDisjoint.isField_of_forall k K k' ?_
  intro Ω _ _ fK fk'
  have hpure : IsPurelyInseparable k fK.fieldRange := by
    let e : K ≃ₐ[k] fK.fieldRange := by
      simpa [AlgHom.fieldRange] using (AlgEquiv.ofInjectiveField fK)
    exact e.isPurelyInseparable
  have hsep : Algebra.IsSeparable k fk'.fieldRange := by
    let e : k' ≃ₐ[k] fk'.fieldRange := by
      simpa [AlgHom.fieldRange] using (AlgEquiv.ofInjectiveField fk')
    exact Algebra.IsSeparable.of_algHom k k' e.symm
  letI : IsPurelyInseparable k fK.fieldRange := hpure
  letI : Algebra.IsSeparable k fk'.fieldRange := hsep
  have hld : fk'.fieldRange.LinearDisjoint fK.fieldRange := by
    exact
      IntermediateField.linearDisjoint_of_isPurelyInseparable_of_isSeparable
        fK.fieldRange fk'.fieldRange
  exact hld.symm

/-- Helper for Chap10 Lemma 10 166 6: regularity over `k'` should descend to the finite purely
inseparable tests over `k` after tensoring with the separable extension `k' / k`. -/
private lemma regularTensor_restrictScalars_of_geometricallyRegular_separable
    {K : Type (max u w)} [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsPurelyInseparable k K]
    (h : IsGeometricallyRegular k' A) :
    IsRegularRing (K ⊗[k] A) := by
  -- Proof comment: the tensor product with the separable extension is the finite purely
  -- inseparable test field over `k'` required by geometric regularity over `k'`.
  letI : Algebra k' (K ⊗[k] k') :=
    Algebra.TensorProduct.rightAlgebra (R := k) (A := K) (B := k')
  have hTensorField : IsField (K ⊗[k] k') :=
    tensorProduct_isField_of_purelyInseparable_left_separable_right
      (k := k) (k' := k') (K := K)
  letI : Field (K ⊗[k] k') := IsField.toField hTensorField
  have hTensorFinite : FiniteDimensional k' (K ⊗[k] k') := by
    have hleft : FiniteDimensional k' (k' ⊗[k] K) := by
      infer_instance
    letI : FiniteDimensional k' (k' ⊗[k] K) := hleft
    let e : (k' ⊗[k] K) ≃ₗ[k'] (K ⊗[k] k') :=
      (Algebra.TensorProduct.commRight k k' K).toLinearEquiv
    exact e.finiteDimensional
  have hTensorPure : IsPurelyInseparable k' (K ⊗[k] k') := by
    have hfieldLeft : IsField (k' ⊗[k] K) := by
      exact (Algebra.TensorProduct.commRight k k' K).toMulEquiv.isField hTensorField
    letI : Field (k' ⊗[k] K) := IsField.toField hfieldLeft
    have hpureResidue :
        IsPurelyInseparable k' ((⊥ : Ideal (k' ⊗[k] K)).ResidueField) := by
      exact
        tensor_prime_residueField_isPurelyInseparable
          (k := k) (K := K) (L := k')
          (q := (⟨⊥, inferInstance⟩ : PrimeSpectrum (k' ⊗[k] K)))
    letI : IsPurelyInseparable k' ((⊥ : Ideal (k' ⊗[k] K)).ResidueField) :=
      hpureResidue
    have hpureLeft : IsPurelyInseparable k' (k' ⊗[k] K) := by
      let eBot : ((⊥ : Ideal (k' ⊗[k] K)).ResidueField) ≃ₐ[k'] (k' ⊗[k] K) :=
        (bot_residueField_algEquiv (k' ⊗[k] K)).restrictScalars k'
      exact eBot.isPurelyInseparable
    letI : IsPurelyInseparable k' (k' ⊗[k] K) := hpureLeft
    let eComm : (k' ⊗[k] K) ≃ₐ[k'] (K ⊗[k] k') :=
      Algebra.TensorProduct.commRight k k' K
    exact eComm.isPurelyInseparable
  letI : FiniteDimensional k' (K ⊗[k] k') := hTensorFinite
  letI : IsPurelyInseparable k' (K ⊗[k] k') := hTensorPure
  letI : IsGeometricallyRegular k' A := h
  have hiter : IsRegularRing ((K ⊗[k] k') ⊗[k'] A) := by
    infer_instance
  -- Proof comment: reassociate the iterated tensor product back to the direct `k`-base change.
  let e : ((K ⊗[k] k') ⊗[k'] A) ≃+* (K ⊗[k] A) :=
    tensor_base_change_assoc_equiv (k := k) (k' := k') (K := K) (B := A)
  letI : IsRegularRing ((K ⊗[k] k') ⊗[k'] A) := hiter
  exact isRegularRing_of_ringEquiv e

/- Domain triage:
- `source-facing`: invariance of geometric regularity under a separable algebraic extension of the
  ground field.
- `core/canonical`: the owner abstraction is `IsGeometricallyRegular`.
- `bridge/view`: the sampled owner-style declarations are
  `IsGeometricallyRegular`,
  `isGeometricallyRegular_iff_forall_finite_purelyInseparable_tensorBaseChange_isRegularRing`,
  `isGeometricallyRegular_of_directed_iSup_subfields`,
  and the parallel owner-level separable-base-change theorems
  `isGeometricallyReduced_iff_of_isSeparable` and
  `isGeometricallyNormal_iff_of_isSeparable`.

Primitive data are only the field-extension hypotheses and the ambient `k'`-algebra `A`.
Geometric regularity stays in the owner class, while the tensor-product regularity tests, the
finite-stage reduction from Lemma `10.166.5`, and the smoothness step through the multiplication
map remain derived API rather than primitive fields of a local wrapper.
-/
-- Proof sketch: if `A` is geometrically regular over `k'`, then for any finite purely
-- inseparable extension `K / k`, the tensor product `K ⊗[k] k'` is a field and
-- `K ⊗[k] A ≃ (K ⊗[k] k') ⊗[k'] A`, so regularity over `k'` implies regularity over `k`.
-- Conversely, write the separable algebraic extension `k' / k` as a filtered colimit of finite
-- separable subextensions, reduce to the finite separable case by Lemma `10.166.5`, note that
-- `A ⊗[k] k'` is geometrically regular over `k'`, and then apply Lemma `10.166.4` to the smooth
-- map `A ⊗[k] k' → A` induced by the étale multiplication map `k' ⊗[k] k' → k'`.
/-- Chap10 Lemma 10 166 6: for a separable algebraic field extension `k' / k`, a `k'`-algebra
`A` is geometrically regular over `k` if and only if it is geometrically regular over `k'`. -/
@[stacks 07QH]
theorem isGeometricallyRegular_iff_of_isSeparable :
    IsGeometricallyRegular k A ↔ IsGeometricallyRegular k' A := by
  constructor
  · intro h
    -- Proof comment: write `k'` as the directed union of its finite-dimensional intermediate
    -- fields over `k`, and ascend geometric regularity over each finite separable stage.
    let ι := {F : IntermediateField k k' // FiniteDimensional k F}
    letI : Nonempty ι := finiteDimensionalIntermediateField_nonempty (k := k) (k' := k')
    apply isGeometricallyRegular_of_directed_iSup_subfields
      (kᵢ := fun F : ι ↦ F.1.toSubfield)
    · exact finiteDimensionalIntermediateField_directed (k := k) (k' := k')
    · exact finiteDimensionalIntermediateField_iSup_eq_top (k := k) (k' := k')
    · intro F
      exact isGeometricallyRegular_of_finiteDimensionalIntermediateField
        (k := k) (k' := k') (A := A) F h
  · intro h
    -- Proof comment: reduce the reverse implication to the defining finite purely inseparable
    -- tensor tests over `k`.
    rw [isGeometricallyRegular_iff_forall_finite_purelyInseparable_tensorBaseChange_isRegularRing]
    intro K _ _ _ _
    exact regularTensor_restrictScalars_of_geometricallyRegular_separable
      (k := k) (k' := k') (A := A) (K := K) h

end

end Algebra
