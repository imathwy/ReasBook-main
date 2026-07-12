import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.Vertical.Basic

universe u v uS vS w wD vD

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- Helper for Chap08 Lemma 8 8 3: the coverwise formula for the vertical part of the descended
based functor. This is the local component that remains to be proved compatible with descent data
before it can be glued to a global fiber morphism. -/
noncomputable def stackificationLiftVerticalLocalMap
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} {y y' : S'.p.Fiber U} (d : y ⟶ y')
    (I : (stackificationLiftVerticalCommonCover (J := J) G hG y y').Arrow) :
    ((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor.obj
        (stackificationLiftObjectGlued X G hG F y) ⟶
      ((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor.obj
        (stackificationLiftObjectGlued X G hG F y') :=
  let Iy := stackificationLiftVerticalCommonCover_left (J := J) G hG y y' I
  let Iy' := stackificationLiftVerticalCommonCover_right (J := J) G hG y y' I
  let x := (stackificationLiftObjectModel (J := J) G hG y Iy).1
  let x' := (stackificationLiftObjectModel (J := J) G hG y' Iy').1
  let cy := (stackificationLiftObjectModel (J := J) G hG y Iy).2
  let cy' := (stackificationLiftObjectModel (J := J) G hG y' Iy').2
  let dI := ((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.map d
  let α : ((FibredCategoryMor.fiberFunctor G I.Y).obj x) ⟶
      ((FibredCategoryMor.fiberFunctor G I.Y).obj x') :=
    cy.hom ≫ dI ≫ cy'.inv
  (stackificationLiftObjectGluedLocalIso X G hG F y Iy).hom ≫
    stackificationLiftHomExtensionFiberMap X G hG F x x' α ≫
      (stackificationLiftObjectGluedLocalIso X G hG F y' Iy').inv

end

end CategoryTheory
