import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.Arrows

universe u v uS vS w wD vD

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- Helper for Chap08 Lemma 8 8 3: a fixed common cover on which two objects in the same target
fiber both have chosen source models. -/
noncomputable def stackificationLiftVerticalCommonCover
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    {U : C} (y y' : S'.p.Fiber U) :
    J.Cover U :=
  stackificationLiftObjectCover (J := J) G hG y ⊓
    stackificationLiftObjectCover (J := J) G hG y'

/-- Helper for Chap08 Lemma 8 8 3: the `y`-branch of the common vertical cover. -/
noncomputable def stackificationLiftVerticalCommonCover_left
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    {U : C} (y y' : S'.p.Fiber U)
    (I : (stackificationLiftVerticalCommonCover (J := J) G hG y y').Arrow) :
    (stackificationLiftObjectCover (J := J) G hG y).Arrow :=
  I.map (homOfLE inf_le_left)

/-- Helper for Chap08 Lemma 8 8 3: the `y'`-branch of the common vertical cover. -/
noncomputable def stackificationLiftVerticalCommonCover_right
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    {U : C} (y y' : S'.p.Fiber U)
    (I : (stackificationLiftVerticalCommonCover (J := J) G hG y y').Arrow) :
    (stackificationLiftObjectCover (J := J) G hG y').Arrow :=
  I.map (homOfLE inf_le_right)

end

end CategoryTheory
