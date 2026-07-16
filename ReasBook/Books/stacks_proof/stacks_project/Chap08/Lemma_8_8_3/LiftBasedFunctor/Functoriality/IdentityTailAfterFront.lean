import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.Functoriality.IdentityFrontRaw
import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.Functoriality.IdentityTail

universe u v uS vS w wD vD

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- Identity-tail cancellation when the first base arrow is only propositionally the identity.

The descent expansion produces the literal third argument
`q.op.toLoc ≫ f.op.toLoc` in `mapComp'`.  When `q = 𝟙 U`, this reduces to the same chosen
identity-pullback cancellation as `IdentityTail`, but it is useful to keep this small transport
separate from the dependent stackification calculation. -/
theorem canonicalFiberPseudofunctor_mapComp_eq_id_hom_app_comp_identityCart
    (p : X.S ⥤ C) [p.IsFibered]
    {U V : C} {q : U ⟶ U} (hq : q = 𝟙 U) (f : V ⟶ U) (z : p.Fiber U) :
    let cart : q ^*[canonicalPullbackChoice p] z ⟶ z :=
      ⟨(canonicalPullbackChoice p).map q z, by
        subst q
        exact ((canonicalPullbackChoice p).isStronglyCartesian (𝟙 U) z).toIsHomLift⟩
    (eqToHom (by simp [hq]) ≫
        ((canonicalFiberPseudofunctor p).mapComp'
          q.op.toLoc f.op.toLoc
          (q.op.toLoc ≫ f.op.toLoc) rfl).hom.toNatTrans.app z) ≫
    ((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map cart =
    ((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map (𝟙 z) := by
  subst q
  intro cart
  rw [Pseudofunctor.mapComp'_eq_mapComp]
  simp only [op_id, Quiver.Hom.id_toLoc]
  rw [Pseudofunctor.mapComp_id_left_hom_app]
  simp only [Bicategory.Strict.leftUnitor_eqToIso, eqToIso.hom,
    PrelaxFunctor.map₂_eqToHom]
  simp only [Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app]
  simp only [Category.assoc, eqToHom_trans_assoc]
  rw [← Category.assoc]
  simp only [Cat.Hom.comp_toFunctor, Functor.comp_obj, Cat.Hom.id_toFunctor, Functor.id_obj]
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have hunit :
      ((canonicalFiberPseudofunctor p).mapId (LocallyDiscrete.mk (op U))).inv.toNatTrans.app z ≫
        (⟨(canonicalPullbackChoice p).map (𝟙 U) z, by
          exact ((canonicalPullbackChoice p).isStronglyCartesian (𝟙 U) z).toIsHomLift⟩ :
          (𝟙 U) ^*[canonicalPullbackChoice p] z ⟶ z) =
        𝟙 z := by
    apply Functor.Fiber.hom_ext
    simpa [canonicalFiberPseudofunctor, PullbackChoice.fiberPseudofunctor,
      PullbackChoice.pullbackIdIso, Category.assoc] using
      (canonicalPullbackChoice p).pullbackIdComponentIso_fac U z
  dsimp only [cart]
  rw [← ((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map_comp]
  change ((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map
      ((((canonicalFiberPseudofunctor p).mapId (LocallyDiscrete.mk (op U))).inv.toNatTrans.app z) ≫
        (⟨(canonicalPullbackChoice p).map (𝟙 U) z, by
          exact ((canonicalPullbackChoice p).isStronglyCartesian (𝟙 U) z).toIsHomLift⟩ :
          (𝟙 U) ^*[canonicalPullbackChoice p] z ⟶ z)) =
    ((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map (𝟙 z)
  rw [hunit]
  simp

/-- After the front identity-overlap transition has been identified, the remaining local
identity expression is the canonical pseudofunctor identity tail. -/
theorem stackificationLiftBasedFunctorIdentity_tail_after_front
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    (T : S'.S)
    (I : (stackificationLiftPulledObjectCover (J := J) G hG
      (S'.p.map (𝟙 T))
      (Functor.Fiber.mk (p := S'.p) (a := T) rfl)).Arrow) :
    let y : S'.p.Fiber (S'.p.obj T) :=
      Functor.Fiber.mk (p := S'.p) (a := T) rfl
    let z : X.p.Fiber (S'.p.obj T) := stackificationLiftObjectGlued X G hG F y
    let cart : (S'.p.map (𝟙 T)) ^*[canonicalPullbackChoice X.p] z ⟶ z :=
      ⟨(canonicalPullbackChoice X.p).map (S'.p.map (𝟙 T)) z, by
        have hcart :
            X.p.IsHomLift (S'.p.map (𝟙 T))
              ((canonicalPullbackChoice X.p).map (S'.p.map (𝟙 T)) z) :=
          ((canonicalPullbackChoice X.p).isStronglyCartesian (S'.p.map (𝟙 T)) z).toIsHomLift
        simpa using hcart⟩
    let M := ((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor
    let Ic := stackificationLiftBasedFunctorIdentityCommonCoverArrow (J := J) G hG T I
    let pb : S'.p.Fiber (S'.p.obj T) :=
      stackificationLiftArrowPullbackTarget (S' := S') (𝟙 T)
    let Iz := stackificationLiftPulledToObjectCover (J := J) G hG (S'.p.map (𝟙 T)) y I
    let Il := stackificationLiftVerticalCommonCover_left (J := J) G hG y pb Ic
    let A := (stackificationLiftObjectGluedLocalIso X G hG F y Il).hom
    let BE := stackificationLiftHomExtensionFiberMap X G hG F
      (stackificationLiftObjectModel (J := J) G hG y Il).1
      (stackificationLiftPulledObjectCoverModel (J := J) G hG (S'.p.map (𝟙 T)) y I).1
      (((stackificationLiftObjectModel (J := J) G hG y Il).2.hom ≫
        ((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.map
          (stackificationLiftArrowVerticalFactor (S' := S') (𝟙 T)) ≫
        (stackificationLiftObjectModel (J := J) G hG pb Iz).2.inv) ≫
        ((stackificationLiftObjectModel (J := J) G hG pb Iz).2.hom ≫
          (stackificationLiftPulledObjectCoverModel (J := J) G hG
            (S'.p.map (𝟙 T)) y I).2.inv))
    let F0 := ((Cat.Hom.toNatIso ((canonicalFiberPseudofunctor X.p).mapId
        (LocallyDiscrete.mk (op I.Y)))).app
      ((FibredCategoryMor.fiberFunctor F I.Y).obj
        (stackificationLiftPulledObjectCoverModel (J := J) G hG
          (S'.p.map (𝟙 T)) y I).1)).symm.hom
    let Gtail := (stackificationLiftPulledGluedObjectDescentIso X G hG F
      (S'.p.map (𝟙 T)) y).inv.hom I
    let H := M.map cart
    A ≫ BE ≫ F0 ≫ Gtail ≫ H = M.map (𝟙 z) := by
  intro y z cart M Ic pb Iz Il A BE F0 Gtail H
  have hfront := stackificationLiftBasedFunctorIdentity_front_raw X G hG F T I
  dsimp [F0, Gtail, H, stackificationLiftPulledGluedObjectDescentIso,
    stackificationLiftPulledObjectDescentData,
    stackificationLiftPulledObjectDescentPullFunctor,
    Pseudofunctor.DescentData.pullFunctor,
    Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso]
  rw [Pseudofunctor.isoMapOfCommSq_eq
    (F := canonicalFiberPseudofunctor X.p)
    (φ := (S'.p.map (𝟙 T)).op.toLoc ≫ I.f.op.toLoc)
    (hφ := rfl)]
  simp only [Iso.trans_inv, Iso.symm_inv]
  rw [CategoryTheory.Cat.Hom₂.comp_app]
  dsimp [Ic, Il, pb, Iz, stackificationLiftBasedFunctorIdentityCommonCoverArrow,
    stackificationLiftVerticalCommonCover_left, stackificationLiftVerticalCommonCover,
    stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base,
    stackificationLiftPulledObjectCoverModel]
  rw [Pseudofunctor.mapComp'_comp_id_inv_app]
  let y0 : S'.p.Fiber (S'.p.obj T) :=
    Functor.Fiber.mk (p := S'.p) (a := T) rfl
  let z0 : X.p.Fiber (S'.p.obj T) := stackificationLiftObjectGlued X G hG F y0
  let Ibase : (stackificationLiftObjectCover (J := J) G hG y0).Arrow := I.base
  let midBase :=
    (FibredCategoryMor.fiberFunctor F I.Y).obj
      (stackificationLiftObjectModel (J := J) G hG y0 Ibase).1
  let eInv := (stackificationLiftObjectGluedIso X G hG F y0).inv.hom Ibase
  let idIso := (canonicalFiberPseudofunctor X.p).mapId (LocallyDiscrete.mk (op I.Y))
  let targetObj :=
    (((canonicalFiberPseudofunctor X.p).toDescentData
      (fun I : (stackificationLiftObjectCover (J := J) G hG y0).Arrow => I.f)).obj z0).obj
        Ibase
  have hnat :
      idIso.inv.toNatTrans.app midBase ≫
          ((canonicalFiberPseudofunctor X.p).map (𝟙 (LocallyDiscrete.mk (op I.Y)))).toFunctor.map eInv ≫
            idIso.hom.toNatTrans.app targetObj
        = eInv := by
    change idIso.inv.toNatTrans.app
        ((stackificationLiftObjectDescentData X G hG F y0).obj Ibase) ≫
          ((canonicalFiberPseudofunctor X.p).map (𝟙 (LocallyDiscrete.mk (op I.Y)))).toFunctor.map eInv ≫
            idIso.hom.toNatTrans.app targetObj
        = eInv
    rw [← (idIso.inv.toNatTrans.naturality_assoc eInv
      (idIso.hom.toNatTrans.app targetObj))]
    have hpair :
        idIso.inv.toNatTrans.app targetObj ≫
            idIso.hom.toNatTrans.app targetObj =
          𝟙 _ := by
      exact Cat.Hom.inv_hom_id_toNatTrans_app idIso targetObj
    calc
      eInv ≫ idIso.inv.toNatTrans.app targetObj ≫
          idIso.hom.toNatTrans.app targetObj =
        eInv ≫ (idIso.inv.toNatTrans.app targetObj ≫
          idIso.hom.toNatTrans.app targetObj) := by
          rfl
      _ = eInv ≫ 𝟙 _ := by
          exact congrArg (fun t => eInv ≫ t) hpair
      _ = eInv := by
          simp only [Category.comp_id]
  have hnatPost {W : ↑((canonicalFiberPseudofunctor X.p).obj (LocallyDiscrete.mk (op I.Y)))}
      (k : (𝟭 ↑((canonicalFiberPseudofunctor X.p).obj (LocallyDiscrete.mk (op I.Y)))).obj
        (((canonicalFiberPseudofunctor X.p).map
          ((S'.p.map (𝟙 T)).op.toLoc ≫ I.f.op.toLoc)).toFunctor.obj z0) ⟶ W) :
      idIso.inv.toNatTrans.app midBase ≫
          (((canonicalFiberPseudofunctor X.p).map (𝟙 (LocallyDiscrete.mk (op I.Y)))).toFunctor.map eInv ≫
            idIso.hom.toNatTrans.app
              (((canonicalFiberPseudofunctor X.p).map
                ((S'.p.map (𝟙 T)).op.toLoc ≫ I.f.op.toLoc)).toFunctor.obj z0) ≫ k)
        = eInv ≫ k := by
    simpa [Category.assoc, targetObj, Ibase, z0] using congrArg (fun t => t ≫ k) hnat
  let kEq :
      (𝟭 ↑((canonicalFiberPseudofunctor X.p).obj (LocallyDiscrete.mk (op I.Y)))).obj
          (((canonicalFiberPseudofunctor X.p).map
            ((S'.p.map (𝟙 T)).op.toLoc ≫ I.f.op.toLoc)).toFunctor.obj z0) ⟶
        ((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor.obj
          ((S'.p.map (𝟙 T)) ^*[canonicalPullbackChoice X.p] z) :=
    eqToHom (by simp [y0, z0]) ≫
      ((canonicalFiberPseudofunctor X.p).mapComp'
        (S'.p.map (𝟙 T)).op.toLoc I.f.op.toLoc
        ((S'.p.map (𝟙 T)).op.toLoc ≫ I.f.op.toLoc) rfl).hom.toNatTrans.app
          z0
  have hnatSlice := hnatPost kEq
  dsimp [kEq, midBase, eInv, idIso, targetObj, y0, z0, Ibase, M,
    stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base] at hnatSlice
  dsimp [y, z, M] at hnatSlice ⊢
  simp only [Category.id_comp, Category.comp_id] at hnatSlice ⊢
  have hnatSlicePost :=
    congrArg (fun t => t ≫
      ((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor.map cart) hnatSlice
  dsimp only at hnatSlicePost
  slice_lhs 3 5 =>
    exact (Category.assoc _ _ _).symm.trans hnatSlicePost
  dsimp [y, Ic, pb, Iz, Il, y0, z0, Ibase, stackificationLiftPulledObjectCover,
    GrothendieckTopology.Cover.Arrow.base] at hfront
  let eFront :=
    (stackificationLiftObjectGluedIso X G hG F
      (Functor.Fiber.mk (p := S'.p) (a := T) rfl)).inv.hom I.base
  change A ≫ BE ≫ eFront = _ at hfront
  let tailComp :=
    ((canonicalFiberPseudofunctor X.p).mapComp'
      (S'.p.map (𝟙 T)).op.toLoc I.f.op.toLoc
      ((S'.p.map (𝟙 T)).op.toLoc ≫ I.f.op.toLoc) rfl).hom.toNatTrans.app
        (stackificationLiftObjectGlued X G hG F
          (Functor.Fiber.mk (p := S'.p) (a := T) rfl))
  let mapCart :=
    ((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor.map cart
  change A ≫ BE ≫ (eFront ≫ tailComp) ≫ mapCart = M.map (𝟙 z)
  calc
    A ≫ BE ≫ (eFront ≫ tailComp) ≫ mapCart =
        A ≫ BE ≫ eFront ≫ (tailComp ≫ mapCart) := by
      simp only [Category.assoc]
    _ = M.map (𝟙 z) := by
      rw [reassoc_of% hfront]
      have htail := canonicalFiberPseudofunctor_mapComp_eq_id_hom_app_comp_identityCart
        (p := X.p) (q := S'.p.map (𝟙 T)) (by simp) I.f
        (stackificationLiftObjectGlued X G hG F
          (Functor.Fiber.mk (p := S'.p) (a := T) rfl))
      dsimp only at htail
      simpa only [tailComp, mapCart, M, y, z, cart, Functor.map_id, S'.p.map_id,
        op_id, Quiver.Hom.id_toLoc, Category.id_comp, Category.assoc] using htail

end

end CategoryTheory
