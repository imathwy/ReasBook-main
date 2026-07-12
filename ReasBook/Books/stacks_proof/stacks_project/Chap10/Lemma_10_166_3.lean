import Mathlib
import StacksProject_2024.Chap10.Definition_10_166_2
import StacksProject_2024.Chap10.Lemma_10_164_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace Algebra

universe u v

section

variable {k : Type u} {A : Type (max u v)} {B : Type (max u v)}
variable [Field k] [CommRing A] [CommRing B]
variable [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]

/- Domain-style sampling:
* primary domain: geometric regularity of algebras over a field and faithfully flat descent;
* sampled owner declarations:
  `IsGeometricallyRegular`,
  `IsGeometricallyRegular.isRegularRing_baseChange`,
  `RingHom.FaithfullyFlat.isStableUnderBaseChange`,
  `isRegularRing_of_faithfullyFlat`;
* best owner abstraction: the source-facing property is the owner class
  `IsGeometricallyRegular`; regularity after tensor base change and faithful flatness after
  base change are derived API and should not be repackaged locally;
* primitive data vs. derived API:
  the primitive inputs are only `hff` and `[IsGeometricallyRegular k B]`;
  the tensor-product algebra structures, the base-changed faithfully flat map, and the regularity
  of the base-changed target are canonical derived data.

Source/core/bridge triage:
* `source-facing`: faithful-flat descent of `IsGeometricallyRegular`;
* `core/canonical`: `IsGeometricallyRegular`, `RingHom.FaithfullyFlat`, and
  `IsRegularRing`;
* `bridge/view`: tensor-product base change of `A → B` along `k → K`.
-/

-- Proof sketch: for any finite purely inseparable extension `K/k`, the base-changed map
-- `K ⊗[k] A → K ⊗[k] B` is faithfully flat by base change. Since `B` is geometrically regular
-- over `k`, the ring `K ⊗[k] B` is regular; regularity then descends along faithfully flat maps,
-- giving regularity of `K ⊗[k] A`. This verifies the defining conditions of geometric regularity
-- for `A`.
/-- Helper for Lemma 10.166.3: regularity descends across a ring equivalence. -/
lemma isRegularRing_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    [IsRegularRing R] :
    IsRegularRing S := by
  -- Proof comment: an isomorphism is faithfully flat, so the regularity descent theorem applies
  -- to the inverse map.
  let f : S →+* R := e.symm.toRingHom
  have hf : RingHom.FaithfullyFlat f := by
    exact RingHom.FaithfullyFlat.of_bijective e.symm.bijective
  exact isRegularRing_of_faithfullyFlat f hf

/-- Helper for Lemma 10.166.3: geometric regularity of `B` gives regularity of the tensor target
`B ⊗[k] K` for the current test field `K`. -/
lemma tensor_target_regular_of_geometricallyRegular
    (K : Type (max u v)) [Field K] [Algebra k K] [FiniteDimensional k K]
    [IsPurelyInseparable k K] [IsGeometricallyRegular k B] :
    IsRegularRing (B ⊗[k] K) := by
  let _ : IsRegularRing (K ⊗[k] B) :=
    IsGeometricallyRegular.isRegularRing_baseChange (k := k) (A := B) K
  -- Proof comment: the definition gives regularity for `K ⊗[k] B`, and tensor commutativity
  -- transports that regularity to the order `B ⊗[k] K` used in the base-change descent step.
  exact isRegularRing_of_ringEquiv (Algebra.TensorProduct.comm k K B).toRingEquiv

/-- Lemma 10.166.3: if `A → B` is a faithfully flat `k`-algebra map and `B` is geometrically
regular over `k`, then `A` is geometrically regular over `k`. -/
@[stacks 07NH]
theorem isGeometricallyRegular_of_faithfullyFlat
    (hff : (algebraMap A B).FaithfullyFlat) [IsGeometricallyRegular k B] :
    IsGeometricallyRegular k A := by
  -- Route correction: align the algebra universes so the owner-level base-change theorem applies
  -- to `A`, `B`, the test field `K`, and the tensor pushouts in one universe.
  -- Proof comment: geometric regularity is tested after tensoring with each finite purely
  -- inseparable extension. For a fixed test field `K`, we base change the faithfully flat map to
  -- `A ⊗[k] K → B ⊗[A] (A ⊗[k] K)`, identify the target with `K ⊗[k] B`, descend regularity, and
  -- finally commute tensor factors back to the requested `K ⊗[k] A`.
  rw [isGeometricallyRegular_iff_forall_finite_purelyInseparable_tensorBaseChange_isRegularRing]
  intro K _ _ _ _
  let _ : Algebra A (A ⊗[k] K) := Algebra.TensorProduct.leftAlgebra
  let _ : CommRing (A ⊗[k] K) := inferInstance
  let _ : CommRing (B ⊗[A] (A ⊗[k] K)) := inferInstance
  let _ : Algebra.IsPushout A B (A ⊗[k] K) (B ⊗[A] (A ⊗[k] K)) := by
    infer_instance
  have hff_base :
      (algebraMap (A ⊗[k] K) (B ⊗[A] (A ⊗[k] K))).FaithfullyFlat := by
    exact RingHom.FaithfullyFlat.isStableUnderBaseChange (R := A) (S := B) (R' := A ⊗[k] K)
      (S' := B ⊗[A] (A ⊗[k] K)) hff
  let _ : IsRegularRing (K ⊗[k] B) :=
    IsGeometricallyRegular.isRegularRing_baseChange (k := k) (A := B) K
  let eComm : (B ⊗[A] (A ⊗[k] K)) ≃+* ((A ⊗[k] K) ⊗[A] B) :=
    (Algebra.TensorProduct.comm A B (A ⊗[k] K)).toRingEquiv
  let eCancel : ((A ⊗[k] K) ⊗[A] B) ≃+* (K ⊗[k] B) :=
    (Algebra.IsPushout.cancelBaseChangeAlg (R := k) (S := K) (A := A)
      (B := A ⊗[k] K) (C := B)).toRingEquiv
  let _ : IsRegularRing (B ⊗[A] (A ⊗[k] K)) :=
    isRegularRing_of_ringEquiv (eComm.trans eCancel).symm
  have hRegular_source : IsRegularRing (A ⊗[k] K) :=
    isRegularRing_of_faithfullyFlat (algebraMap (A ⊗[k] K) (B ⊗[A] (A ⊗[k] K))) hff_base
  -- Proof comment: after descending regularity on `A ⊗[k] K`, commute tensor factors to obtain
  -- the exact tensor order appearing in the definition of geometric regularity.
  exact isRegularRing_of_ringEquiv (Algebra.TensorProduct.comm k A K).toRingEquiv

end

end Algebra
