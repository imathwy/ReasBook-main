import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.Vertical.Global

universe u v uS vS w wD vD

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

theorem scratch_vertical_local_id
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
  let lyL := stackificationLiftObjectGluedLocalIso X G hG F y IyL
  let lyR := stackificationLiftObjectGluedLocalIso X G hG F y IyR
  let Ty := stackificationLiftObjectTransition X G hG F y
    (stackificationLiftObjectCover (J := J) G hG y)
    (stackificationLiftObjectModel (J := J) G hG y)
    I.f (I₁ := IyL) (I₂ := IyR) (𝟙 I.Y) (𝟙 I.Y) hL hR
  have hsource := stackificationLiftObjectGluedLocalIso_comm X G hG F y I.f
    (I₁ := IyL) (I₂ := IyR) (𝟙 I.Y) (𝟙 I.Y) hL hR
  have hlocal_eq :
      stackificationLiftVerticalLocalMap X G hG F (𝟙 y) I =
        lyL.hom ≫ Ty ≫ lyR.inv := by
    dsimp [stackificationLiftVerticalLocalMap, Ty, lyL, lyR,
      stackificationLiftObjectTransition]
    simp
  trace_state
  sorry

end

end CategoryTheory
