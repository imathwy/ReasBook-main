import Mathlib
import StacksProject_2024.Chap10.Definition_10_54_1
import StacksProject_2024.Chap10.Definition_10_166_2
import StacksProject_2024.Chap10.Lemma_10_45_3
import StacksProject_2024.Chap10.Lemma_10_112_8
import StacksProject_2024.Chap10.Lemma_10_140_3
import StacksProject_2024.Chap10.Lemma_10_158_10
import StacksProject_2024.Chap15.Lemma_15_42_3

open scoped TensorProduct

namespace Algebra

universe u v

open IsLocalRing

section

variable {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]

/-- Helper for Chap10 Lemma 10 166 1: regularity transports across a ring equivalence. -/
private lemma regularRingOfRingEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    (hR : IsRegularRing R) :
    IsRegularRing S := by
  -- Proof comment: an isomorphism is faithfully flat, so descend regularity along the inverse
  -- equivalence instead of unfolding the prime-local definition.
  exact _root_.isRegularRing_of_faithfullyFlat e.symm.toRingHom
    (RingHom.FaithfullyFlat.of_bijective e.symm.bijective)

/-- Helper for Chap10 Lemma 10 166 1: a smooth algebra over a field is a regular ring. -/
private lemma isRegularRingOfSmoothOverField
    {K : Type u} {S : Type v} [Field K] [CommRing S] [Algebra K S] [Algebra.Smooth K S] :
    IsRegularRing S := by
  -- Proof comment: smoothness over a field puts every prime in the smooth locus; the chapter
  -- smooth-point theorem turns each localization into a regular local ring.
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing K S
  let _ : Algebra.FinitePresentation K S := inferInstance
  let _ : Algebra.FiniteType K S := inferInstance
  refine ⟨fun q ↦ ?_⟩
  have hsmoothLocus : Algebra.smoothLocus K S = Set.univ := Algebra.smoothLocus_eq_univ
  have hqSmooth : Algebra.IsSmoothAt K q.asIdeal := by
    simpa [Algebra.smoothLocus] using (Set.eq_univ_iff_forall.mp hsmoothLocus) q
  simpa using Algebra.isRegularLocalRing_of_isSmoothAt (k := K) (S := S) q.asIdeal hqSmooth

/-- Helper for Chap10 Lemma 10 166 1: a smooth algebra over a field is geometrically regular. -/
private lemma isGeometricallyRegularOfSmoothOverField
    {K : Type u} {S : Type v} [Field K] [CommRing S] [Algebra K S] [Algebra.Smooth K S] :
    IsGeometricallyRegular K S := by
  -- Proof comment: after any finite purely inseparable field extension, smoothness base-changes
  -- to a smooth algebra over a field, hence to a regular ring.
  refine ⟨fun L _ _ _ _ ↦ ?_⟩
  letI : Algebra.Smooth L (L ⊗[K] S) := inferInstance
  exact isRegularRingOfSmoothOverField (K := L) (S := L ⊗[K] S)

/-- Helper for Chap10 Lemma 10 166 1: regularity ascends along a smooth algebra map. -/
private lemma isRegularRingOfSmoothOfIsRegularRing
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] [IsRegularRing R] :
    IsRegularRing S := by
  -- Proof comment: package smoothness as a regular ring map; the fiber geometric regularity is
  -- the field-smooth helper above.
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  let hSmooth : (algebraMap R S).Smooth := (RingHom.smooth_algebraMap).2 inferInstance
  let _ : (algebraMap R S).IsRegularRingMap := by
    exact
      { toFlat := RingHom.flat_algebraMap_iff.mpr inferInstance
        isGeometricallyRegular_fiber := fun p ↦ by
          letI : Algebra R S := (algebraMap R S).toAlgebra
          letI : Algebra.Smooth R S := (RingHom.smooth_algebraMap).1 hSmooth
          letI : Algebra.Smooth p.asIdeal.ResidueField (p.asIdeal.Fiber S) := inferInstance
          exact isGeometricallyRegularOfSmoothOverField
            (K := p.asIdeal.ResidueField) (S := p.asIdeal.Fiber S) }
  exact Algebra.isRegularRing_of_regularRingMap R

/-- Helper for Chap10 Lemma 10 166 1: tensor-product regularity descends along a field extension
of the left tensor factor. -/
private lemma isRegularRingTensorProductDescendsAlongFieldAlgHom
    {E L : Type (max u v)} [Field E] [Field L] [Algebra k E] [Algebra k L]
    (i : E →ₐ[k] L) (hL : IsRegularRing (L ⊗[k] A)) :
    IsRegularRing (E ⊗[k] A) := by
  -- Proof comment: view `L` as an `E`-algebra, base-change the faithfully flat field extension
  -- along `E → E ⊗[k] A`, identify the base-changed target with `L ⊗[k] A`, and descend.
  letI : Algebra E L := i.toRingHom.toAlgebra
  letI : IsScalarTower k E L := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext x
    exact (i.commutes x).symm
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
  letI : IsRegularRing (L ⊗[E] (E ⊗[k] A)) := regularRingOfRingEquiv eCancel.symm hL
  exact
    _root_.isRegularRing_of_faithfullyFlat
      (algebraMap (E ⊗[k] A) (L ⊗[E] (E ⊗[k] A))) hffBase

/-- Helper for Chap10 Lemma 10 166 1: a localization of a regular ring is regular. -/
private lemma isRegularRingOfLocalization
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] [IsRegularRing R] :
    IsRegularRing S := by
  -- Proof comment: at each prime of the localized ring, compare its local ring with the
  -- localization of the source at the contracted prime and transport regular locality.
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

/-- Helper for Chap10 Lemma 10 166 1: a smooth fraction-field model preserves tensor-product
regularity after passing to the fraction field. -/
private lemma regularTensorOfSmoothFractionFieldModel
    {κ L T : Type*} [Field κ] [Field L] [CommRing T]
    [Algebra κ L] [Algebra κ T]
    (B : Subalgebra κ L) [Algebra.Smooth κ B] [IsFractionRing B L]
    (hT : IsRegularRing T) :
    IsRegularRing (L ⊗[κ] T) := by
  -- Proof comment: first use smooth ascent from the regular base `T` to `T ⊗ B`, then commute
  -- tensor factors into the orientation used by the tensor-localization theorem.
  letI : IsRegularRing T := hT
  letI : IsRegularRing (T ⊗[κ] B) := by
    letI : Algebra.Smooth T (T ⊗[κ] B) := inferInstance
    exact isRegularRingOfSmoothOfIsRegularRing (R := T) (S := T ⊗[κ] B)
  letI : IsRegularRing (B ⊗[κ] T) :=
    regularRingOfRingEquiv (Algebra.TensorProduct.comm κ T B).toRingEquiv inferInstance
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
    -- Proof comment: the localization map acts only on the left tensor factor, so the canonical
    -- right tensor inclusion is fixed.
    exact Algebra.tensor_right_map_includeRight_comp (R := κ) (S := L) (Q := B) (T := T)
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid (B ⊗[κ] T) (nonZeroDivisors B))
      (L ⊗[κ] T) :=
    @Algebra.isLocalization_tensor_right_of_isLocalization κ L
      inferInstance inferInstance inferInstance B inferInstance inferInstance B.toAlgebra
      inferInstance (nonZeroDivisors B) T inferInstance inferInstance rightB rightL tensorBL
      hBtowerInst inferInstance hcompat
  letI : IsLocalization (Algebra.algebraMapSubmonoid (B ⊗[κ] T) (nonZeroDivisors B))
      (L ⊗[κ] T) := hloc
  -- Proof comment: the fraction-field tensor product is a localization of the regular tensor
  -- product `B ⊗ T`.
  exact isRegularRingOfLocalization
    (Algebra.algebraMapSubmonoid (B ⊗[κ] T) (nonZeroDivisors B))

/-- Helper for Chap10 Lemma 10 166 1: the smooth fraction-field tensor bridge after cancelling an
iterated base change. -/
private lemma regularTensorOfSmoothFractionFieldModelBaseChange
    {k κ L A : Type*} [Field k] [Field κ] [Field L] [CommRing A]
    [Algebra k κ] [Algebra k A] [Algebra κ L] [Algebra k L] [IsScalarTower k κ L]
    (B : Subalgebra κ L) [Algebra.Smooth κ B] [IsFractionRing B L]
    (hbase : IsRegularRing (κ ⊗[k] A)) :
    IsRegularRing (L ⊗[k] A) := by
  -- Proof comment: apply the fraction-field model to the already regular base tensor product,
  -- then identify the iterated tensor with the direct base change.
  have hLifted : IsRegularRing (L ⊗[κ] (κ ⊗[k] A)) :=
    regularTensorOfSmoothFractionFieldModel
      (κ := κ) (L := L) (T := κ ⊗[k] A) B hbase
  let eCancel : L ⊗[κ] (κ ⊗[k] A) ≃+* L ⊗[k] A :=
    (Algebra.TensorProduct.cancelBaseChange k κ L L A).toRingEquiv
  exact regularRingOfRingEquiv eCancel hLifted

/-- Helper for Chap10 Lemma 10 166 1: geometric regularity implies regularity after tensoring
with every essentially finite type field extension. -/
private lemma regularTensorOfEssFiniteTypeFieldExtension
    (hgeom : IsGeometricallyRegular k A)
    (K : Type (max u v)) [Field K] [Algebra k K] [Algebra.EssFiniteType k K] :
    IsRegularRing (K ⊗[k] A) := by
  -- Proof comment: start with the source lift. It replaces the essentially finite type field
  -- `K` by a purely inseparable top extension `K'` over a finite purely inseparable base `k'`
  -- where the top extension is separable over `k'`.
  obtain ⟨k', hk'Field, hk'Alg, K', hK'Field, hkK'Alg, hKK'Alg, hk'K'Alg, hkKK',
      hkk'K', hfinTop, hpureTop, hfinBase, hpureBase, hsep⟩ :=
    exists_purelyInseparable_lift_with_separable_over (k := k) (K := K)
  letI : Field k' := hk'Field
  letI : Algebra k k' := hk'Alg
  letI : Field K' := hK'Field
  letI : Algebra k K' := hkK'Alg
  letI : Algebra K K' := hKK'Alg
  letI : Algebra k' K' := hk'K'Alg
  letI : IsScalarTower k K K' := hkKK'
  letI : IsScalarTower k k' K' := hkk'K'
  letI : FiniteDimensional K K' := hfinTop
  letI : IsPurelyInseparable K K' := hpureTop
  letI : FiniteDimensional k k' := hfinBase
  letI : IsPurelyInseparable k k' := hpureBase
  have hbase : IsRegularRing (k' ⊗[k] A) := by
    -- Proof comment: the lifted base is one of the finite purely inseparable test fields in the
    -- definition of geometric regularity.
    exact IsGeometricallyRegular.isRegularRing_baseChange (k := k) (A := A) k'
  letI : Algebra.IsAlgebraic k k' := IsPurelyInseparable.isAlgebraic k k'
  letI : Algebra.EssFiniteType K K' := inferInstance
  letI : Algebra.EssFiniteType k K' := Algebra.EssFiniteType.comp k K K'
  letI : Algebra.EssFiniteType k' K' := Algebra.EssFiniteType.of_comp k k' K'
  obtain ⟨B, hSmooth, hFraction⟩ :=
    (Algebra.isSeparableOver_iff_exists_smooth_domain_with_fractionRing
      (k := k') (K := K')).1 hsep
  have hK'Tensor : IsRegularRing (K' ⊗[k] A) := by
    -- Proof comment: the smooth fraction-field model of `K' / k'` promotes regularity from
    -- `k' ⊗[k] A` to `K' ⊗[k] A` after cancelling the iterated base change.
    letI : Algebra.Smooth k' B := hSmooth
    letI : IsFractionRing B K' := hFraction
    exact regularTensorOfSmoothFractionFieldModelBaseChange
      (k := k) (κ := k') (L := K') (A := A) B hbase
  -- Proof comment: finally descend regularity from the finite top extension `K'` back to `K`
  -- using faithful-flat descent along the induced tensor-product map.
  exact isRegularRingTensorProductDescendsAlongFieldAlgHom
    (IsScalarTower.toAlgHom k K K') hK'Tensor

/- Domain-style sampling:
* primary domain: geometric regularity of algebras over a field, detected by regularity of tensor
  base changes along field extensions;
* sampled owner declarations:
  `IsGeometricallyRegular`,
  `isGeometricallyRegular_iff_forall_finite_purelyInseparable_tensorBaseChange_isRegularRing`,
  `Algebra.EssFiniteType`,
  `IsPurelyInseparable`;
* best owner abstraction: `IsGeometricallyRegular k A` is the canonical owner for this
  regularity notion; the finitely generated field-extension test in Lemma `10.166.1` is bridge
  data, not a second owner;
* primitive data vs. derived API: the primitive owner data are exactly the regularity statements
  for finite purely inseparable tensor base changes. The finitely generated field-extension test is
  a derived equivalent criterion. No separate `IsNoetherianRing A` hypothesis belongs in the
  public API, since regularity of the displayed tensor base changes already implies it.

Source/core/bridge triage:
* `source-facing`: the equivalence between the finitely generated field-extension test and the
  textbook finite purely inseparable test;
* `core/canonical`: `IsGeometricallyRegular k A`;
* `bridge/view`: the reformulation of Lemma `10.166.1` as an owner-level equivalence.
-/

-- Proof sketch: the reverse implication is immediate because finite purely inseparable extensions
-- are finitely generated. For the forward implication, start with a finitely generated field
-- extension `K / k`. By Lemma `10.45.3`, after a finite purely inseparable extension `K' / K` and
-- a finite purely inseparable extension `k' / k`, the field `K'` becomes separable over `k'`.
-- Lemma `10.158.10` realizes `K'` as the fraction field of a smooth `k'`-algebra `B`. Then
-- `k' ⊗[k] A` is regular by geometric regularity, smooth ascent gives regularity of
-- `B ⊗[k'] (k' ⊗[k] A)`, localization yields regularity of `K' ⊗[k] A`, and faithful flat
-- descent along `K ⊗[k] A → K' ⊗[k] A` gives regularity of `K ⊗[k] A`.
/-- Chap10 Lemma 10 166 1: canonical owner form. For a `k`-algebra `A`, geometric regularity
over `k` is equivalent to requiring `K ⊗[k] A` to be regular for every finitely generated field
extension `K / k`, recorded canonically by `Algebra.EssFiniteType`; no extra Noetherian
hypothesis is needed in this criterion. -/
@[stacks 0381]
theorem isGeometricallyRegular_iff_forall_essFiniteType_fieldExtension_tensorBaseChange_isRegularRing
    :
    IsGeometricallyRegular k A ↔
      ∀ (K : Type (max u v)) [Field K] [Algebra k K] [Algebra.EssFiniteType k K],
        IsRegularRing (K ⊗[k] A) := by
  constructor
  · intro hgeom K _ _ _
    -- Proof comment: the remaining forward direction is isolated in the source-facing helper.
    exact regularTensorOfEssFiniteTypeFieldExtension hgeom K
  · intro htest
    -- Proof comment: the finite purely inseparable test fields are among the essentially finite
    -- type field extensions, so they satisfy the required regularity condition.
    rw [isGeometricallyRegular_iff_forall_finite_purelyInseparable_tensorBaseChange_isRegularRing]
    intro K _ _ _ _
    let _ : Algebra.EssFiniteType k K := inferInstance
    exact htest K

/-- Lemma 10.166.1, unpacked source-facing form: for a `k`-algebra `A`, the base
change `K ⊗[k] A` is a regular ring for every finitely generated field extension `K / k` if and
only if it is regular for every finite purely inseparable field extension `K / k`; again, no
separate Noetherian assumption is part of the statement. -/
@[stacks 0381]
theorem forall_essFiniteType_fieldExtension_tensorBaseChange_isRegularRing_iff_forall_finite_purelyInseparable
    :
    (∀ (K : Type (max u v)) [Field K] [Algebra k K] [Algebra.EssFiniteType k K],
      IsRegularRing (K ⊗[k] A)) ↔
      (∀ (K : Type (max u v)) [Field K] [Algebra k K] [FiniteDimensional k K]
        [IsPurelyInseparable k K],
        IsRegularRing (K ⊗[k] A)) := by
  rw [
    ← isGeometricallyRegular_iff_forall_essFiniteType_fieldExtension_tensorBaseChange_isRegularRing,
    isGeometricallyRegular_iff_forall_finite_purelyInseparable_tensorBaseChange_isRegularRing
  ]

end

end Algebra
