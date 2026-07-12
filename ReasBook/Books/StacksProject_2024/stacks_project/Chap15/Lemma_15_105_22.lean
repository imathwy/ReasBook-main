import Mathlib
import StacksProject_2024.Chap10.Lemma_10_107_3
import StacksProject_2024.Chap15.Definition_15_105_1
import StacksProject_2024.Chap15.Lemma_15_105_4
import StacksProject_2024.Chap15.Lemma_15_105_7
import StacksProject_2024.Chap15.Lemma_15_105_20
import StacksProject_2024.Chap15.Lemma_15_105_21

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CommRingCat
open scoped TensorProduct

universe u

section

variable {A : Type u} {B : Type u} {K : Type u}
variable [CommRing A] [CommRing B] [Field K]
variable [Algebra A B] [Algebra A K] [IsFractionRing A K]
variable [IsIntegrallyClosed A] [Algebra.IsWeaklyEtale A B]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/- Domain-style sampling:
- primary domain: commutative algebra of normal domains, weakly étale base change, and integral
  closedness in tensor-product overrings of the fraction field;
- sampled owner declarations:
  `IsIntegrallyClosedIn`,
  `Algebra.IsWeaklyEtale`,
  `hasWeakDimensionLE_of_isWeaklyEtale`,
  `isIntegrallyClosedIn_of_hasWeakDimensionLEOne_of_flat_of_injective_of_epi`;
- best owner abstraction: this theorem is `source-facing`, but its public statement should remain
  the canonical owner predicate `IsIntegrallyClosedIn B (B ⊗[A] K)`. The weak-dimension transfer,
  weakly étale base change, and flat-epimorphism integrally closedness results already have owner
  declarations upstream, so the cartesian square from Lemma `15.105.20` is only bridge data and
  should not be repackaged locally;
- primitive data: the normal domain `A`, its fraction field `K`, and the weakly étale owner
  `Algebra.IsWeaklyEtale A B`;
- derived API: the weak-dimension and epimorphism facts after tensor base change, and the final
  `IsIntegrallyClosedIn` conclusion.

Source/core/bridge triage:
- `source-facing`: `isIntegrallyClosedIn_tensorProduct_fractionField_of_isWeaklyEtale`;
- `core/canonical`: `IsIntegrallyClosedIn`, `Algebra.IsWeaklyEtale`, `HasWeakDimensionLE`,
  `Algebra.IsEpi`;
- `bridge/view`: the cartesian-square witness from Lemma `15.105.20`, together with the tensor
  base-change bridge from Lemma `10.107.3` and the weakly étale base-change theorem
  `Algebra.IsWeaklyEtale.baseChange`.
-/

-- Proof sketch: choose the cartesian square `A → K`, `V → L` from Lemma `15.105.20`. Base change
-- the weakly étale map `A → B` along `A → V`; by `Algebra.IsWeaklyEtale.baseChange`, the map
-- `V → B ⊗[A] V` is weakly étale, so `hasWeakDimensionLE_of_isWeaklyEtale` upgrades the weak
-- dimension bound on `V` to one on `B ⊗[A] V`. The bottom map `B ⊗[A] V → B ⊗[A] L` remains a
-- flat, injective epimorphism after tensor base change, using the canonical epimorphism base
-- change theorem `algebra_isEpi_tensorProduct_of_isEpi`; then Lemma `15.105.21` gives
-- `IsIntegrallyClosedIn (B ⊗[A] V) (B ⊗[A] L)`. The original cartesian square is bridge data used
-- only to descend this owner statement to `IsIntegrallyClosedIn B (B ⊗[A] K)`.
/-- Helper for Lemma 15.105.22: replacing the overring by an algebra-equivalent one does not
change the predicate `IsIntegrallyClosedIn`. -/
theorem isIntegrallyClosedIn_of_algEquiv
    {R : Type*} {S : Type*} {T : Type*}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    (e : S ≃ₐ[R] T) [h : IsIntegrallyClosedIn R S] :
    IsIntegrallyClosedIn R T := by
  -- Unfold the owner predicate so both the injectivity and the integral-descent clauses can be
  -- transported explicitly across the algebra equivalence.
  rw [isIntegrallyClosedIn_iff] at h ⊢
  constructor
  · -- Injectivity is transported by comparing both algebra maps through `e`.
    intro x y hxy
    apply h.1
    apply e.injective
    simpa using hxy
  · -- Integral elements are pulled back through `e.symm`, descended in `S`, and pushed forward.
    intro x hx
    have hx' : IsIntegral R (e.symm x) :=
      IsIntegral.map e.symm.toAlgHom hx
    obtain ⟨r, hr⟩ := h.2 hx'
    refine ⟨r, ?_⟩
    simpa using congrArg e hr

/-- Helper for Lemma 15.105.22: the iterated base change
`(V ⊗[A] B) ⊗[V] L` is canonically the direct tensor product `L ⊗[A] B`. -/
noncomputable def tensorBaseChangeRightAlgEquiv
    {V : Type u} {L : Type u}
    [CommRing V] [CommRing L]
    [Algebra A V] [Algebra A L] [Algebra V L] [IsScalarTower A V L] :
    ((V ⊗[A] B) ⊗[V] L) ≃ₐ[V ⊗[A] B] L ⊗[A] B :=
  Algebra.IsPushout.cancelBaseChangeAlg A V B (V ⊗[A] B) L

/-- Helper for Lemma 15.105.22: the direct base-change ring `L ⊗[A] B` carries the canonical
`V ⊗[A] B`-algebra structure induced from `V → L`. -/
noncomputable def tensorBaseChangeRightAlgHom
    {V : Type u} {L : Type u}
    [CommRing V] [CommRing L]
    [Algebra A V] [Algebra A L] [Algebra V L] [IsScalarTower A V L] :
    (V ⊗[A] B) →ₐ[A] L ⊗[A] B :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom A V L) (AlgHom.id A B)

/-- Helper for Lemma 15.105.22: the target tensor product `L ⊗[A] B` is canonically an algebra
over the source tensor product `V ⊗[A] B`. -/
noncomputable instance tensorBaseChangeRightAlgebra
    {V : Type u} {L : Type u}
    [CommRing V] [CommRing L]
    [Algebra A V] [Algebra A L] [Algebra V L] [IsScalarTower A V L] :
    Algebra (V ⊗[A] B) (L ⊗[A] B) :=
  (tensorBaseChangeRightAlgHom (A := A) (B := B) (V := V) (L := L)).toAlgebra

/-- Helper for Lemma 15.105.22: pushing an `A`-algebra forward along `A → B` identifies the
resulting under-category pushout object with the tensor product over `A`. -/
noncomputable def pushout_obj_iso_tensorProduct
    {X : Type u} [CommRing X] [Algebra A X] :
    ((Under.pushout (ofHom (algebraMap A B))).obj (Under.mk (ofHom (algebraMap A X)))) ≅
      Under.mk (ofHom (algebraMap B (X ⊗[A] B))) := by
  -- Rewrite the pushed-out object as the categorical pushout under-object.
  rw [Under.pushout_obj]
  let hpush :
      IsPushout (ofHom (algebraMap A X)) (ofHom (algebraMap A B))
        (ofHom (algebraMap X (X ⊗[A] B))) (ofHom (algebraMap B (X ⊗[A] B))) :=
    CommRingCat.isPushout_of_isPushout A X B (X ⊗[A] B)
  -- The universal pushout is canonically isomorphic to the tensor-product pushout ring.
  refine Under.isoMk hpush.isoPushout.symm ?_
  simp

/-- Helper for Lemma 15.105.22: after identifying the pushed-out object with `X ⊗[A] B`, the
left pushout generator becomes the canonical map from `X`. -/
@[reassoc (attr := simp)]
lemma pushout_inl_pushout_obj_iso_tensorProduct_hom
    {X : Type u} [CommRing X] [Algebra A X] :
    pushout.inl (ofHom (algebraMap A X)) (ofHom (algebraMap A B)) ≫
      ((pushout_obj_iso_tensorProduct (A := A) (B := B) (X := X)).hom).right =
        ofHom (algebraMap X (X ⊗[A] B)) := by
  let hpush :
      IsPushout (ofHom (algebraMap A X)) (ofHom (algebraMap A B))
        (ofHom (algebraMap X (X ⊗[A] B))) (ofHom (algebraMap B (X ⊗[A] B))) :=
    CommRingCat.isPushout_of_isPushout A X B (X ⊗[A] B)
  -- The left comparison is exactly the universal `inl` map of the tensor-product pushout.
  simpa [pushout_obj_iso_tensorProduct, hpush] using hpush.inl_isoPushout_inv

/-- Helper for Lemma 15.105.22: after identifying the pushed-out object with `X ⊗[A] B`, the
right pushout generator becomes the canonical map from `B`. -/
@[reassoc (attr := simp)]
lemma pushout_inr_pushout_obj_iso_tensorProduct_hom
    {X : Type u} [CommRing X] [Algebra A X] :
    pushout.inr (ofHom (algebraMap A X)) (ofHom (algebraMap A B)) ≫
      ((pushout_obj_iso_tensorProduct (A := A) (B := B) (X := X)).hom).right =
        ofHom (algebraMap B (X ⊗[A] B)) := by
  let hpush :
      IsPushout (ofHom (algebraMap A X)) (ofHom (algebraMap A B))
        (ofHom (algebraMap X (X ⊗[A] B))) (ofHom (algebraMap B (X ⊗[A] B))) :=
    CommRingCat.isPushout_of_isPushout A X B (X ⊗[A] B)
  -- The right comparison is exactly the universal `inr` map of the tensor-product pushout.
  simpa [pushout_obj_iso_tensorProduct, hpush] using hpush.inr_isoPushout_inv

/-- Helper for Lemma 15.105.22: a pullback square of rings written with algebra maps is again the
corresponding pullback square in the under-category of `A`. -/
lemma under_pullback_of_ring_pullback
    {V : Type u} {L : Type u}
    [CommRing V] [CommRing L]
    [Algebra A V] [Algebra A L] [Algebra K L] [Algebra V L]
    [IsScalarTower A K L] [IsScalarTower A V L]
    (hsq : IsPullback (ofHom (algebraMap A K)) (ofHom (algebraMap A V))
      (ofHom (algebraMap K L)) (ofHom (algebraMap V L))) :
    let U₀ : Under (of A) := Under.mk (ofHom (algebraMap A A))
    let U₁ : Under (of A) := Under.mk (ofHom (algebraMap A K))
    let U₂ : Under (of A) := Under.mk (ofHom (algebraMap A V))
    let U₃ : Under (of A) := Under.mk (ofHom (algebraMap A L))
    let f : U₀ ⟶ U₁ := Under.homMk (ofHom (algebraMap A K)) (by
      dsimp
      simp [CommRingCat.hom_comp, RingHom.algebraMap_self])
    let g : U₀ ⟶ U₂ := Under.homMk (ofHom (algebraMap A V)) (by
      dsimp
      simp [CommRingCat.hom_comp, RingHom.algebraMap_self])
    let p : U₁ ⟶ U₃ := Under.homMk (ofHom (algebraMap K L)) (by
      dsimp
      simpa [CommRingCat.hom_comp] using (IsScalarTower.algebraMap_eq A K L).symm)
    let q : U₂ ⟶ U₃ := Under.homMk (ofHom (algebraMap V L)) (by
      dsimp
      simpa [CommRingCat.hom_comp] using (IsScalarTower.algebraMap_eq A V L).symm)
    IsPullback f g p q := by
  dsimp
  -- Reflect the pullback through the forgetful functor from `Under (of A)`.
  refine IsPullback.of_map (CategoryTheory.Under.forget (of A)) ?_ ?_
  · -- The square commutes in the under-category because it already commutes in rings.
    ext x
    simpa [CommRingCat.hom_comp, RingHom.comp_apply] using congr(($hsq.w) x)
  · -- Forgetting the under-structure recovers the original pullback square.
    simpa using hsq

/-- Helper for Lemma 15.105.22: transporting a pushed-out morphism in the under-category agrees
with the concrete tensor-product map induced by the original algebra map. -/
lemma pushout_map_eq_tensorProduct_map
    {X : Type u} {Y : Type u}
    [CommRing X] [CommRing Y]
    [Algebra A X] [Algebra A Y] [Algebra X Y] [IsScalarTower A X Y] :
    let eX : (Under.forget (of B)).obj
        ((Under.pushout (ofHom (algebraMap A B))).obj (Under.mk (ofHom (algebraMap A X)))) ≅
          of (X ⊗[A] B) :=
      (Under.forget (of B)).mapIso
        (pushout_obj_iso_tensorProduct (A := A) (B := B) (X := X))
    let eY : (Under.forget (of B)).obj
        ((Under.pushout (ofHom (algebraMap A B))).obj (Under.mk (ofHom (algebraMap A Y)))) ≅
          of (Y ⊗[A] B) :=
      (Under.forget (of B)).mapIso
        (pushout_obj_iso_tensorProduct (A := A) (B := B) (X := Y))
    (Under.forget (of B)).map
        ((Under.pushout (ofHom (algebraMap A B))).map
          (Under.homMk (ofHom (algebraMap X Y)) (by
            dsimp
            simpa [CommRingCat.hom_comp] using (IsScalarTower.algebraMap_eq A X Y).symm))) ≫
      eY.hom =
        eX.hom ≫
          ofHom (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A X Y) (AlgHom.id A B)) := by
  have hsq_pushout :
      ofHom (algebraMap A X) ≫ ofHom (algebraMap X Y) ≫
          pushout.inl (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)) =
        ofHom (algebraMap A B) ≫
          pushout.inr (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)) := by
    calc
      ofHom (algebraMap A X) ≫ ofHom (algebraMap X Y) ≫
          pushout.inl (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)) =
        ofHom (algebraMap A Y) ≫
          pushout.inl (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)) := by
          simpa [Category.assoc, CommRingCat.hom_comp] using
            congrArg
              (fun k ↦ k ≫ pushout.inl (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)))
              (show ofHom (algebraMap A X) ≫ ofHom (algebraMap X Y) =
                  ofHom (algebraMap A Y) by
                simpa [CommRingCat.hom_comp] using (IsScalarTower.algebraMap_eq A X Y).symm)
      _ = ofHom (algebraMap A B) ≫
          pushout.inr (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)) := by
          simpa using
            (pushout.condition (f := ofHom (algebraMap A Y)) (g := ofHom (algebraMap A B)))
  -- Compare the transported morphisms on the two pushout generators.
  dsimp
  apply pushout.hom_ext
  · have hdesc :
        pushout.inl (ofHom (algebraMap A X)) (ofHom (algebraMap A B)) ≫
            pushout.desc
              (ofHom (algebraMap X Y) ≫
                pushout.inl (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)))
              (pushout.inr (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)))
              (by
                simpa [CommRingCat.hom_comp] using hsq_pushout) ≫
            ((pushout_obj_iso_tensorProduct (A := A) (B := B) (X := Y)).hom).right =
          ofHom (algebraMap X Y) ≫
            pushout.inl (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)) ≫
              ((pushout_obj_iso_tensorProduct (A := A) (B := B) (X := Y)).hom).right := by
      simpa using
        (pushout.inl_desc_assoc
          (ofHom (algebraMap X Y) ≫
            pushout.inl (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)))
          (pushout.inr (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)))
          (by
            simpa [CommRingCat.hom_comp] using hsq_pushout)
          (((pushout_obj_iso_tensorProduct (A := A) (B := B) (X := Y)).hom).right))
    calc
      pushout.inl (ofHom (algebraMap A X)) (ofHom (algebraMap A B)) ≫
          pushout.desc
            (ofHom (algebraMap X Y) ≫
              pushout.inl (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)))
            (pushout.inr (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)))
            (by
              simpa [CommRingCat.hom_comp] using hsq_pushout) ≫
          ((pushout_obj_iso_tensorProduct (A := A) (B := B) (X := Y)).hom).right
          = ofHom (algebraMap X Y) ≫
              pushout.inl (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)) ≫
                ((pushout_obj_iso_tensorProduct (A := A) (B := B) (X := Y)).hom).right := hdesc
      _ = ofHom (algebraMap X Y) ≫ ofHom (algebraMap Y (Y ⊗[A] B)) := by
        exact congrArg (fun k ↦ ofHom (algebraMap X Y) ≫ k) <| by
          simpa [CommRingCat.hom_comp] using
            (pushout_inl_pushout_obj_iso_tensorProduct_hom (A := A) (B := B) (X := Y))
      _ = pushout.inl (ofHom (algebraMap A X)) (ofHom (algebraMap A B)) ≫
            ((pushout_obj_iso_tensorProduct (A := A) (B := B) (X := X)).hom).right ≫
            ofHom
              (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A X Y) (AlgHom.id A B)) := by
        rw [pushout_inl_pushout_obj_iso_tensorProduct_hom_assoc]
        apply CommRingCat.hom_ext
        ext x
        simp [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  · have hdesc :
        pushout.inr (ofHom (algebraMap A X)) (ofHom (algebraMap A B)) ≫
            pushout.desc
              (ofHom (algebraMap X Y) ≫
                pushout.inl (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)))
              (pushout.inr (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)))
              (by
                simpa [CommRingCat.hom_comp] using hsq_pushout) ≫
            ((pushout_obj_iso_tensorProduct (A := A) (B := B) (X := Y)).hom).right =
          pushout.inr (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)) ≫
            ((pushout_obj_iso_tensorProduct (A := A) (B := B) (X := Y)).hom).right := by
      simpa using
        (pushout.inr_desc_assoc
          (ofHom (algebraMap X Y) ≫
            pushout.inl (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)))
          (pushout.inr (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)))
          (by
            simpa [CommRingCat.hom_comp] using hsq_pushout)
          (((pushout_obj_iso_tensorProduct (A := A) (B := B) (X := Y)).hom).right))
    calc
      pushout.inr (ofHom (algebraMap A X)) (ofHom (algebraMap A B)) ≫
          pushout.desc
            (ofHom (algebraMap X Y) ≫
              pushout.inl (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)))
            (pushout.inr (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)))
            (by
              simpa [CommRingCat.hom_comp] using hsq_pushout) ≫
          ((pushout_obj_iso_tensorProduct (A := A) (B := B) (X := Y)).hom).right
          = pushout.inr (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)) ≫
              ((pushout_obj_iso_tensorProduct (A := A) (B := B) (X := Y)).hom).right := hdesc
      _ = ofHom (algebraMap B (Y ⊗[A] B)) := by
        simpa [CommRingCat.hom_comp] using
          (pushout_inr_pushout_obj_iso_tensorProduct_hom (A := A) (B := B) (X := Y))
      _ = pushout.inr (ofHom (algebraMap A X)) (ofHom (algebraMap A B)) ≫
            ((pushout_obj_iso_tensorProduct (A := A) (B := B) (X := X)).hom).right ≫
            ofHom
              (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A X Y) (AlgHom.id A B)) := by
        rw [pushout_inr_pushout_obj_iso_tensorProduct_hom_assoc]
        apply CommRingCat.hom_ext
        ext x
        simp [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

/-- Helper for Lemma 15.105.22: after collapsing `A ⊗[A] B` to `B` by the left unitor, the
tensor-product map coming from `A → X` becomes the ordinary algebra map `B → X ⊗[A] B`. -/
lemma tensorProduct_map_id_eq_algebraMap
    {X : Type u} [CommRing X] [Algebra A X] :
    ofHom (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A A X) (AlgHom.id A B)) =
      ((Algebra.TensorProduct.lid A B).toRingEquiv.toCommRingCatIso).hom ≫
        ofHom (algebraMap B (X ⊗[A] B)) := by
  -- Compare the two algebra maps on the left and right tensor generators separately.
  apply CommRingCat.hom_ext
  change
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A A X) (AlgHom.id A B)) =
      (IsScalarTower.toAlgHom A B (X ⊗[A] B)).comp (Algebra.TensorProduct.lid A B).toAlgHom
  exact congrArg AlgHom.toRingHom <| by
    apply Algebra.TensorProduct.ext
    · ext a
      simp [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.one_def]
    · ext b
      simp [Algebra.TensorProduct.includeRight_apply]

/-- Helper for Lemma 15.105.22: after transporting the pushed-out initial object `A ⊗[A] B` to
`B`, the pushed-out map from the initial object becomes the canonical algebra map from `B`. -/
lemma pushout_id_map_eq_algebraMap
    {X : Type u} [CommRing X] [Algebra A X] :
    let e₀ : (Under.forget (of B)).obj
        ((Under.pushout (ofHom (algebraMap A B))).obj (Under.mk (ofHom (algebraMap A A)))) ≅
          of B :=
      (Under.forget (of B)).mapIso
        (pushout_obj_iso_tensorProduct (A := A) (B := B) (X := A)) ≪≫
          (Algebra.TensorProduct.lid A B).toRingEquiv.toCommRingCatIso
    let eX : (Under.forget (of B)).obj
        ((Under.pushout (ofHom (algebraMap A B))).obj (Under.mk (ofHom (algebraMap A X)))) ≅
          of (X ⊗[A] B) :=
      (Under.forget (of B)).mapIso
        (pushout_obj_iso_tensorProduct (A := A) (B := B) (X := X))
    (Under.forget (of B)).map
        ((Under.pushout (ofHom (algebraMap A B))).map
          (Under.homMk (ofHom (algebraMap A X)) (by
            dsimp
            simp [CommRingCat.hom_comp, RingHom.algebraMap_self]))) ≫
      eX.hom =
        e₀.hom ≫ ofHom (algebraMap B (X ⊗[A] B)) := by
  let eA : (Under.forget (of B)).obj
      ((Under.pushout (ofHom (algebraMap A B))).obj (Under.mk (ofHom (algebraMap A A)))) ≅
        of (A ⊗[A] B) :=
    (Under.forget (of B)).mapIso
      (pushout_obj_iso_tensorProduct (A := A) (B := B) (X := A))
  -- First identify the pushed-out map with the tensor-product map from `A ⊗[A] B`.
  have hmap :
      (Under.forget (of B)).map
          ((Under.pushout (ofHom (algebraMap A B))).map
            (Under.homMk (ofHom (algebraMap A X)) (by
              dsimp
              simp [CommRingCat.hom_comp, RingHom.algebraMap_self]))) ≫
        ((Under.forget (of B)).mapIso
          (pushout_obj_iso_tensorProduct (A := A) (B := B) (X := X))).hom =
      eA.hom ≫
        ofHom (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A A X) (AlgHom.id A B)) := by
    simpa [eA] using
      (pushout_map_eq_tensorProduct_map (A := A) (B := B) (X := A) (Y := X))
  -- Then collapse the source corner `A ⊗[A] B` to `B` using the tensor-product left unitor.
  dsimp
  calc
    (Under.forget (of B)).map
        ((Under.pushout (ofHom (algebraMap A B))).map
          (Under.homMk (ofHom (algebraMap A X)) (by
            dsimp
            simp [CommRingCat.hom_comp, RingHom.algebraMap_self]))) ≫
      ((Under.forget (of B)).mapIso
        (pushout_obj_iso_tensorProduct (A := A) (B := B) (X := X))).hom
        = eA.hom ≫
            ofHom (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A A X) (AlgHom.id A B)) := hmap
    _ = eA.hom ≫
          ((Algebra.TensorProduct.lid A B).toRingEquiv.toCommRingCatIso).hom ≫
            ofHom (algebraMap B (X ⊗[A] B)) := by
          rw [tensorProduct_map_id_eq_algebraMap (A := A) (B := B) (X := X), Category.assoc]
    _ = (eA ≪≫ (Algebra.TensorProduct.lid A B).toRingEquiv.toCommRingCatIso).hom ≫
          ofHom (algebraMap B (X ⊗[A] B)) := by
          rfl

/-- Helper for Lemma 15.105.22: base changing the source pullback square along the flat map
`A → B` gives the concrete tensor-product pullback square used in the Stacks argument. -/
theorem tensor_basechange_square_isPullback
    {V : Type u} {L : Type u}
    [CommRing V] [CommRing L]
    [Algebra A V] [Algebra A L] [Algebra K L] [Algebra V L]
    [IsScalarTower A K L] [IsScalarTower A V L] :
    IsPullback (ofHom (algebraMap A K)) (ofHom (algebraMap A V))
      (ofHom (algebraMap K L)) (ofHom (algebraMap V L)) →
    IsPullback
      (ofHom (algebraMap B (K ⊗[A] B)))
      (ofHom (algebraMap B (V ⊗[A] B)))
      (ofHom (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A K L) (AlgHom.id A B)))
      (ofHom (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A V L) (AlgHom.id A B))) := by
  intro hsq
  let base : of A ⟶ of B := ofHom (algebraMap A B)
  let baseChange : Under (of A) ⥤ Under (of B) := Under.pushout base
  have hflat : RingHom.Flat (algebraMap A B) :=
    Algebra.IsWeaklyEtale.flat (A := A) (B := B) inferInstance
  let _ : PreservesFiniteLimits baseChange :=
    CommRingCat.Under.preservesFiniteLimits_of_flat base hflat
  let U₀ : Under (of A) := Under.mk (ofHom (algebraMap A A))
  let U₁ : Under (of A) := Under.mk (ofHom (algebraMap A K))
  let U₂ : Under (of A) := Under.mk (ofHom (algebraMap A V))
  let U₃ : Under (of A) := Under.mk (ofHom (algebraMap A L))
  let f : U₀ ⟶ U₁ := Under.homMk (ofHom (algebraMap A K)) (by
    dsimp [U₀, U₁]
    simp [CommRingCat.hom_comp, RingHom.algebraMap_self])
  let g : U₀ ⟶ U₂ := Under.homMk (ofHom (algebraMap A V)) (by
    dsimp [U₀, U₂]
    simp [CommRingCat.hom_comp, RingHom.algebraMap_self])
  let p : U₁ ⟶ U₃ := Under.homMk (ofHom (algebraMap K L)) (by
    dsimp [U₁, U₃]
    simpa [CommRingCat.hom_comp] using (IsScalarTower.algebraMap_eq A K L).symm)
  let q : U₂ ⟶ U₃ := Under.homMk (ofHom (algebraMap V L)) (by
    dsimp [U₂, U₃]
    simpa [CommRingCat.hom_comp] using (IsScalarTower.algebraMap_eq A V L).symm)
  have hunder :
      IsPullback f g p q := by
    simpa [U₀, U₁, U₂, U₃, f, g, p, q] using
      (under_pullback_of_ring_pullback (A := A) (K := K) hsq)
  have hbase :
      IsPullback
        (baseChange.map f)
        (baseChange.map g)
        (baseChange.map p)
        (baseChange.map q) :=
    IsPullback.map baseChange hunder
  have hforget :
      IsPullback
        ((Under.forget (of B)).map (baseChange.map f))
        ((Under.forget (of B)).map (baseChange.map g))
        ((Under.forget (of B)).map (baseChange.map p))
        ((Under.forget (of B)).map (baseChange.map q)) :=
    IsPullback.map (Under.forget (of B)) hbase
  let e₁A : (Under.forget (of B)).obj (baseChange.obj U₀) ≅ of (A ⊗[A] B) :=
    (Under.forget (of B)).mapIso
      (pushout_obj_iso_tensorProduct (A := A) (B := B) (X := A))
  let e₁ : (Under.forget (of B)).obj (baseChange.obj U₀) ≅ of B :=
    e₁A ≪≫ (Algebra.TensorProduct.lid A B).toRingEquiv.toCommRingCatIso
  let e₂ : (Under.forget (of B)).obj (baseChange.obj U₁) ≅ of (K ⊗[A] B) :=
    (Under.forget (of B)).mapIso
      (pushout_obj_iso_tensorProduct (A := A) (B := B) (X := K))
  let e₃ : (Under.forget (of B)).obj (baseChange.obj U₂) ≅ of (V ⊗[A] B) :=
    (Under.forget (of B)).mapIso
      (pushout_obj_iso_tensorProduct (A := A) (B := B) (X := V))
  let e₄ : (Under.forget (of B)).obj (baseChange.obj U₃) ≅ of (L ⊗[A] B) :=
    (Under.forget (of B)).mapIso
      (pushout_obj_iso_tensorProduct (A := A) (B := B) (X := L))
  -- Route correction: the pullback square is already preserved by base change; the remaining work
  -- is to identify each pushed-out edge with the concrete tensor-product maps from the source.
  refine IsPullback.of_iso hforget e₁ e₂ e₃ e₄ ?_ ?_ ?_ ?_
  · -- The top edge is the canonical algebra map `B → K ⊗[A] B`.
    simpa [baseChange, base, U₀, U₁, f, e₁, e₂] using
      (pushout_id_map_eq_algebraMap (A := A) (B := B) (X := K))
  · -- The left edge is the canonical algebra map `B → V ⊗[A] B`.
    simpa [baseChange, base, U₀, U₂, g, e₁, e₃] using
      (pushout_id_map_eq_algebraMap (A := A) (B := B) (X := V))
  · -- The upper-right edge is the tensor-product map induced by `K → L`.
    simpa [baseChange, base, U₁, U₃, p, e₂, e₄] using
      (pushout_map_eq_tensorProduct_map (A := A) (B := B) (X := K) (Y := L))
  · -- The lower-left edge is the tensor-product map induced by `V → L`.
    simpa [baseChange, base, U₂, U₃, q, e₃, e₄] using
      (pushout_map_eq_tensorProduct_map (A := A) (B := B) (X := V) (Y := L))

/-- Helper for Lemma 15.105.22: after base change to the weak-dimension-one ring `V`, the weakly
étale map `A → B` gives an integrally closed extension on the lower row. -/
theorem isIntegrallyClosedIn_tensor_basechange_of_weaklyEtale
    {V : Type u} {L : Type u}
    [CommRing V] [CommRing L]
    [Algebra A V] [Algebra A L] [Algebra V L] [IsScalarTower A V L]
    [HasWeakDimensionLE V 1]
    (hkflat : (algebraMap V L).Flat)
    (hkinj : Function.Injective (algebraMap V L))
    [Algebra.IsEpi V L] :
    IsIntegrallyClosedIn (V ⊗[A] B) (L ⊗[A] B) := by
  letI : Module.Flat V L := RingHom.flat_algebraMap_iff.mp hkflat
  letI : Algebra.IsWeaklyEtale V (V ⊗[A] B) :=
    Algebra.IsWeaklyEtale.baseChange (A := A) (A' := V) (B := B) inferInstance
  have hwd : HasWeakDimensionLE (V ⊗[A] B) 1 :=
    hasWeakDimensionLE_of_isWeaklyEtale V (V ⊗[A] B) 1 inferInstance
  let D : Type _ := (V ⊗[A] B) ⊗[V] L
  letI : CommRing D := inferInstance
  letI : Algebra (V ⊗[A] B) D := inferInstance
  have hflatD : Module.Flat (V ⊗[A] B) D := by
    -- The lower-right corner is obtained by flat base change of `V → L` along `V → V ⊗[A] B`.
    simpa [D] using
      (Module.Flat.baseChange (R := V) (S := V ⊗[A] B) (M := L))
  have hsourceFlat : Module.Flat V (V ⊗[A] B) := by
    -- The source tensor algebra is the base change of the flat weakly étale algebra `B`.
    simpa using
      (Module.Flat.baseChange (R := A) (S := V) (M := B))
  have hleftInj :
      Function.Injective (algebraMap (V ⊗[A] B) D) := by
    letI : Module.Flat V (V ⊗[A] B) := hsourceFlat
    -- The lower algebra map is the canonical left inclusion into the tensor product over `V`.
    simpa [D] using
      (Algebra.TensorProduct.includeLeft_injective
        (R := V) (S := V ⊗[A] B) (A := V ⊗[A] B) (B := L) hkinj)
  letI : Algebra.IsEpi (V ⊗[A] B) D :=
    algebra_isEpi_tensorProduct_of_isEpi
      (R := V) (S := L) (R' := V ⊗[A] B)
  have hclosedD : IsIntegrallyClosedIn (V ⊗[A] B) D :=
    isIntegrallyClosedIn_of_hasWeakDimensionLEOne_of_flat_of_injective_of_epi
      (A := V ⊗[A] B) (B := D) hleftInj
  let e : D ≃ₐ[V ⊗[A] B] L ⊗[A] B :=
    tensorBaseChangeRightAlgEquiv (A := A) (B := B) (V := V) (L := L)
  -- Transport the closedness statement across the canonical pushout equivalence.
  exact isIntegrallyClosedIn_of_algEquiv e

/-- Helper for Lemma 15.105.22: if the lower row of a pullback square is integrally closed in the
lower-right ring, then the upper row is integrally closed in the upper-right ring. -/
theorem isIntegrallyClosedIn_of_pullback_descent
    {R : Type*} {S : Type*} {T : Type*} {U : Type*}
    [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    [Algebra R S] [Algebra R T] [Algebra R U] [Algebra S U] [Algebra T U]
    [IsScalarTower R S U] [IsScalarTower R T U]
    (sq : IsPullback (ofHom (algebraMap R S)) (ofHom (algebraMap R T))
      (ofHom (algebraMap S U)) (ofHom (algebraMap T U)))
    [IsIntegrallyClosedIn T U] :
    IsIntegrallyClosedIn R S := by
  rw [isIntegrallyClosedIn_iff]
  constructor
  · intro x y hxy
    have hTUinj : Function.Injective (algebraMap T U) :=
      (isIntegrallyClosedIn_iff.mp ‹IsIntegrallyClosedIn T U›).1
    have hxyU : algebraMap R U x = algebraMap R U y := by
      -- Push the top-row equality into `U` using the scalar-tower comparison.
      simpa [IsScalarTower.algebraMap_eq R S U] using congrArg (algebraMap S U) hxy
    have hxyT : algebraMap R T x = algebraMap R T y := by
      -- Injectivity on the lower row recovers equality in `T`.
      apply hTUinj
      simpa [IsScalarTower.algebraMap_eq R T U] using hxyU
    let φx : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of R :=
      ofHom (Polynomial.aeval x).toRingHom
    let φy : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of R :=
      ofHom (Polynomial.aeval y).toRingHom
    have hcompS :
        φx ≫ ofHom (algebraMap R S) = φy ≫ ofHom (algebraMap R S) := by
      -- The two polynomial maps agree after passing to `S` because they send `X` to the same
      -- element there.
      apply CommRingCat.hom_ext
      apply Polynomial.ringHom_ext
      · intro n
        simp [φx, φy, CommRingCat.hom_comp]
      · simpa [φx, φy, CommRingCat.hom_comp] using hxy
    have hcompT :
        φx ≫ ofHom (algebraMap R T) = φy ≫ ofHom (algebraMap R T) := by
      -- The same argument applies on the lower row after recovering equality in `T`.
      apply CommRingCat.hom_ext
      apply Polynomial.ringHom_ext
      · intro n
        simp [φx, φy, CommRingCat.hom_comp]
      · simpa [φx, φy, CommRingCat.hom_comp] using hxyT
    have hφ : φx = φy := sq.hom_ext hcompS hcompT
    -- Evaluating the equal lifted polynomial maps at `X` recovers the original elements of `R`.
    have hX :=
      congrArg
        (fun f : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of R ↦ f.hom Polynomial.X) hφ
    simpa [φx, φy] using hX
  · intro x hx
    have hxU : IsIntegral R (algebraMap S U x) :=
      IsIntegral.map (IsScalarTower.toAlgHom R S U) hx
    have hxUT : IsIntegral T (algebraMap S U x) :=
      IsIntegral.tower_top hxU
    obtain ⟨t, ht⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral hxUT
    let φS : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of S :=
      ofHom (Polynomial.aeval x).toRingHom
    let φT : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of T :=
      ofHom (Polynomial.aeval t).toRingHom
    have hcompat :
        φS ≫ ofHom (algebraMap S U) = φT ≫ ofHom (algebraMap T U) := by
      -- The descended lower-row element `t` is chosen so that both polynomial maps agree in `U`.
      apply CommRingCat.hom_ext
      apply Polynomial.ringHom_ext
      · intro n
        simp [φS, φT, CommRingCat.hom_comp]
        rw [← IsScalarTower.algebraMap_apply R S U n, ← IsScalarTower.algebraMap_apply R T U n]
      · simpa [φS, φT, CommRingCat.hom_comp] using ht.symm
    obtain ⟨l, hlS, _hlT⟩ := sq.exists_lift φS φT hcompat
    refine ⟨l.hom Polynomial.X, ?_⟩
    -- Evaluating the lifted polynomial map at `X` gives the desired element of `R`.
    have hX :=
      congrArg
        (fun f : CommRingCat.of (Polynomial R) ⟶ CommRingCat.of S ↦ f.hom Polynomial.X) hlS
    simpa [φS] using hX

/-- Lemma 15.105.22: if `A` is a normal domain with fraction field `K` and `A → B` is weakly
étale, then `B` is integrally closed in `B ⊗[A] K`. -/
theorem isIntegrallyClosedIn_tensorProduct_fractionField_of_isWeaklyEtale :
    IsIntegrallyClosedIn B (B ⊗[A] K) := by
  letI : IsDomain A :=
    Function.Injective.isDomain (algebraMap A K) (IsFractionRing.injective A K)
  obtain ⟨V, L, i, k, j, hsq, hwdV, hkflat, hkinj, hkepi⟩ :=
    exists_cartesian_square_over_fractionField_with_weakDimensionLEOne_and_flat_injective_epi
      (A := A) (K := K)
  letI : Algebra A V := i.hom.toAlgebra
  letI : Algebra A L := (k.hom.comp i.hom).toAlgebra
  letI : Algebra V L := k.hom.toAlgebra
  letI : Algebra K L := j.hom.toAlgebra
  letI : IsScalarTower A V L := by infer_instance
  letI : IsScalarTower A K L := by
    change j.hom.comp (algebraMap A K) = algebraMap A L
    simpa [RingHom.algebraMap_toAlgebra, CommRingCat.hom_comp] using hsq.w.symm
  letI : HasWeakDimensionLE V 1 := hwdV
  letI : Epi k := hkepi
  letI : Algebra.IsEpi V L := by
    simpa [RingHom.algebraMap_toAlgebra] using (CommRingCat.epi_iff_epi).1 hkepi
  have hlower : IsIntegrallyClosedIn (V ⊗[A] B) (L ⊗[A] B) :=
    isIntegrallyClosedIn_tensor_basechange_of_weaklyEtale
      (A := A) (V := V) (L := L)
      (by simpa [RingHom.algebraMap_toAlgebra] using hkflat)
      (by simpa [RingHom.algebraMap_toAlgebra] using hkinj)
  have hsqAlg :
      IsPullback (ofHom (algebraMap A K)) (ofHom (algebraMap A V))
        (ofHom (algebraMap K L)) (ofHom (algebraMap V L)) := by
    -- Rewrite the source pullback square in the algebra-map form expected by the tensor bridge.
    simpa [RingHom.algebraMap_toAlgebra] using hsq.flip
  have htensor :
      IsPullback
        (ofHom (algebraMap B (K ⊗[A] B)))
        (ofHom (algebraMap B (V ⊗[A] B)))
        (ofHom (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A K L) (AlgHom.id A B)))
        (ofHom (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A V L) (AlgHom.id A B))) :=
    tensor_basechange_square_isPullback (A := A) (B := B) (K := K) hsqAlg
  letI : Algebra (K ⊗[A] B) (L ⊗[A] B) :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A K L) (AlgHom.id A B)).toAlgebra
  letI : Algebra (V ⊗[A] B) (L ⊗[A] B) :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A V L) (AlgHom.id A B)).toAlgebra
  letI : IsScalarTower B (K ⊗[A] B) (L ⊗[A] B) := by infer_instance
  letI : IsScalarTower B (V ⊗[A] B) (L ⊗[A] B) := by infer_instance
  letI : IsIntegrallyClosedIn (V ⊗[A] B) (L ⊗[A] B) := hlower
  have hclosedK : IsIntegrallyClosedIn B (K ⊗[A] B) :=
    isIntegrallyClosedIn_of_pullback_descent
      (R := B) (S := K ⊗[A] B) (T := V ⊗[A] B) (U := L ⊗[A] B) htensor
  letI : IsIntegrallyClosedIn B (K ⊗[A] B) := hclosedK
  let e : K ⊗[A] B ≃ₐ[B] B ⊗[A] K := by
    simpa using (Algebra.TensorProduct.commRight A B K).symm
  -- Transport the upper-row closedness statement back to the textbook tensor order.
  exact isIntegrallyClosedIn_of_algEquiv e

end
