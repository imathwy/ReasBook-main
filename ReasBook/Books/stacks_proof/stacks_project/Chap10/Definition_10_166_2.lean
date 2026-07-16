import stacks_proof.stacks_project.Chap10.Lemma_10_164_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

namespace Algebra

universe u v w

/- Domain-style sampling:
* primary domain: geometric regularity of field algebras via regularity of tensor-product base
  changes;
* sampled owner declarations:
  `Algebra.IsGeometricallyReduced`,
  `Algebra.IsGeometricallyNormal`,
  `AlgebraicGeometry.geometrically`,
  `IsRegularRingMap`;
* best owner abstraction: the chapter's field-algebra owner
  `IsGeometricallyRegular k A`; the scheme-level `geometrically` API is a more general
  ambient owner, but using it directly here would force every downstream algebra lemma through an
  affine bridge;
* primitive data vs. derived API:
  the primitive owner data are exactly the regularity statements for tensor base changes along
  finite purely inseparable field extensions;
  regularity and Noetherianity of the underlying ring are derived consequences. The regular-ring
  bridge must keep `k` explicit, because `IsRegularRing A` alone does not determine the ambient
  field algebra structure.

Source/core/bridge triage:
* `source-facing`: `IsGeometricallyRegular k A`;
* `core/canonical`: `IsRegularRing`;
* `bridge/view`: the tensor-base-change test against finite purely inseparable field extensions.
-/

/-- Definition data for Chap10 Definition 10 166 2: a commutative `k`-algebra is geometrically
regular over `k` if every finite purely inseparable field extension of `k` yields a regular tensor
base-change ring. -/
@[stacks 0382, mk_iff isGeometricallyRegular_iff_forall_finite_purelyInseparable_tensorBaseChange_isRegularRing]
class IsGeometricallyRegular (k : Type u) (A : Type v) [Field k] [CommRing A]
    [Algebra k A] :
    Prop where
  isRegularRing_baseChange (K : Type (max u v)) [Field K] [Algebra k K]
      [FiniteDimensional k K] [IsPurelyInseparable k K] :
    IsRegularRing (K ⊗[k] A)

attribute [instance] IsGeometricallyRegular.isRegularRing_baseChange

/-- Helper for Chap10 Definition 10 166 2: regularity transports across a ring equivalence. -/
private lemma regularRingOfRingEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    (hR : IsRegularRing R) :
    IsRegularRing S := by
  -- Proof comment: view the inverse equivalence as a faithfully flat map and descend
  -- regularity along it, avoiding the expensive prime-localization transport.
  exact _root_.isRegularRing_of_faithfullyFlat e.symm.toRingHom
    (RingHom.FaithfullyFlat.of_bijective e.symm.bijective)

/-- Helper for Chap10 Definition 10 166 2: tensoring a field extension with the base field gives
a regular ring. -/
private lemma regularRingTensorBaseSelf {k K : Type*} [Field k] [Field K] [Algebra k K]
    (hK : IsRegularRing K) :
    IsRegularRing (K ⊗[k] k) := by
  -- Proof comment: collapse the right tensor factor and transport regularity along the unit
  -- isomorphism.
  exact regularRingOfRingEquiv (Algebra.TensorProduct.rid k k K).symm.toRingEquiv hK

/-- Helper for Chap10 Definition 10 166 2: the universe-lifted ground field gives the same
tensor base-change ring as the ordinary ground field. -/
private noncomputable def groundFieldLiftTensorRingEquiv
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A] :
    (ULift.{max u v, u} k ⊗[k] A) ≃+* (k ⊗[k] A) :=
  (Algebra.TensorProduct.congr
    (ULift.algEquiv (R := k) (A := k) : ULift.{max u v, u} k ≃ₐ[k] k)
    (AlgEquiv.refl : A ≃ₐ[k] A)).toRingEquiv

/-- Helper for Chap10 Definition 10 166 2: geometric regularity gives regularity of tensoring
with the ground field, after lifting the test field to the universe required by the definition. -/
private lemma regularRingTensorBaseOfGeometricallyRegular
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    (hA : IsGeometricallyRegular k A) :
    IsRegularRing (k ⊗[k] A) := by
  -- Proof comment: use a universe-lifted copy of the ground field as the test extension in the
  -- definition of geometric regularity.
  let K := ULift.{max u v, u} k
  let _ : Field K := inferInstance
  let _ : Algebra k K := ULift.algebra
  let _ : FiniteDimensional k K := inferInstance
  let _ : IsPurelyInseparable k K :=
    (ULift.algEquiv (R := k) (A := k) : K ≃ₐ[k] k).symm.isPurelyInseparable
  let hLift : IsRegularRing (K ⊗[k] A) :=
    IsGeometricallyRegular.isRegularRing_baseChange (k := k) (A := A) K
  let eLift : (K ⊗[k] A) ≃+* (k ⊗[k] A) :=
    groundFieldLiftTensorRingEquiv k A
  -- Proof comment: the tensor congruence identifies the lifted test ring with the ordinary
  -- ground-field tensor product, so regularity transports across that ring isomorphism.
  exact regularRingOfRingEquiv eLift hLift

/-- Helper for Chap10 Definition 10 166 2: regularity descends along the left tensor-unit
identification `k ⊗[k] A ≃ A`. -/
private lemma regularRingOfTensorBaseLeft
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    (h : IsRegularRing (k ⊗[k] A)) :
    IsRegularRing A := by
  -- Proof comment: collapse the base tensor product to `A` and transport regularity across the
  -- canonical algebra equivalence.
  exact regularRingOfRingEquiv (Algebra.TensorProduct.lid k A).toRingEquiv h

section

variable {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]

/-- Helper for Chap10 Definition 10 166 2: a field is geometrically regular over itself. -/
instance : IsGeometricallyRegular k k := by
  -- Proof comment: every defining test ring is the test field itself after the right tensor-unit
  -- isomorphism, hence is regular.
  constructor
  intro K _ _ _ _
  exact regularRingTensorBaseSelf (k := k) (K := K) inferInstance

/-- Chap10 Definition 10 166 2: a geometrically regular algebra over a field is a regular ring. -/
theorem isRegularRing_of_isGeometricallyRegular
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    [IsGeometricallyRegular k A] :
    IsRegularRing A := by
  -- Proof comment: first get regularity of the base tensor product from geometric regularity,
  -- then collapse `k ⊗[k] A` by the left tensor-unit isomorphism.
  let hTensor : IsRegularRing (k ⊗[k] A) :=
    regularRingTensorBaseOfGeometricallyRegular k A inferInstance
  exact regularRingOfTensorBaseLeft k A hTensor

end

end Algebra
