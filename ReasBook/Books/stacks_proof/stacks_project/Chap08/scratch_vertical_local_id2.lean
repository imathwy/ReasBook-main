import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.Vertical.LocalMap

universe u v uS vS w wD vD

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

theorem scratch_vertical_local_id2
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} (y : S'.p.Fiber U)
    (I : (stackificationLiftVerticalCommonCover (J := J) G hG y y).Arrow) :
    stackificationLiftVerticalLocalMap X G hG F (𝟙 y) I =
      𝟙 (((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor.obj
        (stackificationLiftObjectGlued X G hG F y)) := by
  let IyL := stackificationLiftVerticalCommonCover_left (J := J) G hG y y I
  let IyR := stackificationLiftVerticalCommonCover_right (J := J) G hG y y I
  have hL : (𝟙 I.Y) ≫ IyL.f = I.f := by
    dsimp [IyL, stackificationLiftVerticalCommonCover_left,
      stackificationLiftVerticalCommonCover]
    simp
  have hR : (𝟙 I.Y) ≫ IyR.f = I.f := by
    dsimp [IyR, stackificationLiftVerticalCommonCover_right,
      stackificationLiftVerticalCommonCover]
    simp
  have hIy : IyL = IyR := by
    dsimp [IyL, IyR, stackificationLiftVerticalCommonCover_left,
      stackificationLiftVerticalCommonCover_right, stackificationLiftVerticalCommonCover]
  have hIf : IyL.f = I.f := by
    simpa using hL
  dsimp only [stackificationLiftVerticalLocalMap]
  change
    (stackificationLiftObjectGluedLocalIso X G hG F y IyL).hom ≫
        stackificationLiftHomExtensionFiberMap X G hG F
          (stackificationLiftObjectModel (J := J) G hG y IyL).1
          (stackificationLiftObjectModel (J := J) G hG y IyR).1
          ((stackificationLiftObjectModel (J := J) G hG y IyL).2.hom ≫
            ((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.map (𝟙 y) ≫
              (stackificationLiftObjectModel (J := J) G hG y IyR).2.inv) ≫
        (stackificationLiftObjectGluedLocalIso X G hG F y IyR).inv =
      𝟙 (((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor.obj
        (stackificationLiftObjectGlued X G hG F y))
  have hself :
      (stackificationLiftObjectGluedLocalIso X G hG F y IyL).hom ≫
          stackificationLiftHomExtensionFiberMap X G hG F
            (stackificationLiftObjectModel (J := J) G hG y IyL).1
            (stackificationLiftObjectModel (J := J) G hG y IyL).1
            ((stackificationLiftObjectModel (J := J) G hG y IyL).2.hom ≫
              ((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.map (𝟙 y) ≫
                (stackificationLiftObjectModel (J := J) G hG y IyL).2.inv) ≫
          (stackificationLiftObjectGluedLocalIso X G hG F y IyL).inv =
        𝟙 (((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor.obj
          (stackificationLiftObjectGlued X G hG F y)) := by
    have hmap_id :
        ((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.map (𝟙 y) =
          𝟙 (((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.obj y) :=
      ((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.map_id y
    rw [hmap_id]
    erw [Category.id_comp]
    rw [(stackificationLiftObjectModel (J := J) G hG y IyL).2.hom_inv_id]
    rw [stackificationLiftHomExtensionFiberMap_id]
    calc
      (stackificationLiftObjectGluedLocalIso X G hG F y IyL).hom ≫
          𝟙 ((FibredCategoryMor.fiberFunctor F IyL.Y).obj
            (stackificationLiftObjectModel (J := J) G hG y IyL).1) ≫
            (stackificationLiftObjectGluedLocalIso X G hG F y IyL).inv =
        (stackificationLiftObjectGluedLocalIso X G hG F y IyL).hom ≫
            (stackificationLiftObjectGluedLocalIso X G hG F y IyL).inv := by
          erw [Category.id_comp]
      _ = 𝟙 (((canonicalFiberPseudofunctor X.p).map IyL.f.op.toLoc).toFunctor.obj
          (stackificationLiftObjectGlued X G hG F y)) :=
          (stackificationLiftObjectGluedLocalIso X G hG F y IyL).hom_inv_id
  simpa [hIy] using hself

end

end CategoryTheory
