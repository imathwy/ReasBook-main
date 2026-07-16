import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_154_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MorphismProperty
open CommRingCat
open scoped TensorProduct

universe u

namespace RingHom

section

variable {R : Type u} {A : Type u} {R' : Type u}
variable [CommRing R] [CommRing A] [CommRing R']
variable [Algebra R A] [Algebra R R']

/- Domain-style sampling for Lemma 10.154.1:
* primary domain: filtered-colimit closure of étale morphisms in `CommRingCat`;
* sampled owner declarations:
  - `CommRingCat.etale`, the chapter owner for étale morphisms in `CommRingCat`;
  - `CategoryTheory.MorphismProperty.ind`, the canonical filtered-colimit owner;
  - `RingHom.IsFilteredColimitOfEtale`, the chapter source-facing owner that hides the
    same-universe `ULift` presentation;
  - `RingHom.Etale.isStableUnderBaseChange`, the ring-hom base-change theorem for étaleness;
  - `CommRingCat.isPushout_tensorProduct`, the canonical tensor-product pushout square.
* best owner abstraction: `RingHom.IsFilteredColimitOfEtale` as a ring-hom property, with its
  base-change witness `RingHom.IsFilteredColimitOfEtale.isStableUnderBaseChange`;
* primitive data: the owner-level filtered-colimit-of-étale hypothesis on the structural map;
* derived API: the tensor-product corollary `filteredColimitOfEtale_baseChange`.

Source/core/bridge triage:
* `source-facing`: the tensor-product base-change corollary
  `filteredColimitOfEtale_baseChange`;
* `core/canonical`: `CategoryTheory.MorphismProperty.ind CommRingCat.etale`;
* `bridge/view`: the hidden same-universe `ULift` presentation used by
  `RingHom.IsFilteredColimitOfEtale`.
-/

private instance etale_isStableUnderCobaseChange : CommRingCat.etale.IsStableUnderCobaseChange := by
  simpa [CommRingCat.etale, RingHom.toMorphismProperty] using
    (RingHom.isStableUnderCobaseChange_toMorphismProperty_iff).2
      RingHom.Etale.isStableUnderBaseChange

namespace IsFilteredColimitOfEtale

-- Proof sketch: unfold the chapter owner into the categorical owner
-- `ind CommRingCat.etale` on the `ULift`ed same-universe presentation of the map, lift the given
-- pushout square through the canonical `ULift` ring isomorphisms, and apply cobase-change
-- stability of `ind CommRingCat.etale`.
/-- Filtered colimits of étale ring maps are stable under base change. -/
theorem isStableUnderBaseChange : RingHom.IsStableUnderBaseChange RingHom.IsFilteredColimitOfEtale := by
  intro R S R' S' _ _ _ _ _ _ _ _ _ _ _ _ hRS
  let _ : Algebra R (ULift S) := ULift.algebra
  let _ : Algebra (ULift R) (ULift S) := ULift.algebra' R (ULift S)
  let _ : Algebra R (ULift R') := ULift.algebra
  let _ : Algebra (ULift R) (ULift R') := ULift.algebra' R (ULift R')
  let _ : Algebra S (ULift S') := ULift.algebra
  let _ : Algebra (ULift S) (ULift S') := ULift.algebra' S (ULift S')
  let _ : Algebra R' (ULift S') := ULift.algebra
  let _ : Algebra (ULift R') (ULift S') := ULift.algebra' R' (ULift S')
  dsimp [RingHom.IsFilteredColimitOfEtale] at hRS ⊢
  let sq₀ : IsPushout
      (CommRingCat.ofHom (algebraMap R S))
      (CommRingCat.ofHom (algebraMap R R'))
      (CommRingCat.ofHom (algebraMap S S'))
      (CommRingCat.ofHom (algebraMap R' S')) :=
    CommRingCat.isPushout_of_isPushout R S R' S'
  let eR : CommRingCat.of R ≅ CommRingCat.of (ULift R) :=
    RingEquiv.toCommRingCatIso (ULift.ringEquiv.symm : R ≃+* ULift R)
  let eS : CommRingCat.of S ≅ CommRingCat.of (ULift S) :=
    RingEquiv.toCommRingCatIso (ULift.ringEquiv.symm : S ≃+* ULift S)
  let eR' : CommRingCat.of R' ≅ CommRingCat.of (ULift R') :=
    RingEquiv.toCommRingCatIso (ULift.ringEquiv.symm : R' ≃+* ULift R')
  let eS' : CommRingCat.of S' ≅ CommRingCat.of (ULift S') :=
    RingEquiv.toCommRingCatIso (ULift.ringEquiv.symm : S' ≃+* ULift S')
  let sq : IsPushout
      (CommRingCat.ofHom (algebraMap (ULift R) (ULift S)))
      (CommRingCat.ofHom (algebraMap (ULift R) (ULift R')))
      (CommRingCat.ofHom (algebraMap (ULift S) (ULift S')))
      (CommRingCat.ofHom (algebraMap (ULift R') (ULift S'))) :=
    sq₀.of_iso eR eS eR' eS'
      (by ext x; rfl) (by ext x; rfl) (by ext x; rfl) (by ext x; rfl)
  exact of_isPushout sq.flip hRS

end IsFilteredColimitOfEtale

-- Proof sketch: equip `R' ⊗[R] A` with the canonical tensor-product pushout data and specialize
-- the owner-level base-change theorem above.
/-- Lemma 10.154.1: if `A` is a filtered colimit of étale `R`-algebras, then after any base
change `R → R'`, the canonical map `R' → R' ⊗[R] A` is again a filtered colimit of étale ring
maps. -/
theorem filteredColimitOfEtale_baseChange
    (hA : (algebraMap R A).IsFilteredColimitOfEtale) :
    (algebraMap R' (R' ⊗[R] A)).IsFilteredColimitOfEtale := by
  let _ : Algebra A (R' ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  let _ : Algebra R' (R' ⊗[R] A) := Algebra.TensorProduct.leftAlgebra
  let _ : IsScalarTower R A (R' ⊗[R] A) := by infer_instance
  let _ : IsScalarTower R R' (R' ⊗[R] A) := by infer_instance
  let _ : Algebra.IsPushout R A R' (R' ⊗[R] A) := by infer_instance
  exact IsFilteredColimitOfEtale.isStableUnderBaseChange R A R' (R' ⊗[R] A) hA

end

end RingHom
