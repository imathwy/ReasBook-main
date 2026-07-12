import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.Vertical.LocalCompatibility

universe u v uS vS w wD vD

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- Helper for Chap08 Lemma 8 8 3: the compatible coverwise vertical maps as a morphism of
descent data on the common local source-image cover. -/
noncomputable def stackificationLiftVerticalDescentDataHom
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} {y y' : S'.p.Fiber U} (d : y ⟶ y') :
    (((canonicalFiberPseudofunctor X.p).toDescentData
        (fun I : (stackificationLiftVerticalCommonCover (J := J) G hG y y').Arrow ↦ I.f)).obj
      (stackificationLiftObjectGlued X G hG F y)) ⟶
    (((canonicalFiberPseudofunctor X.p).toDescentData
        (fun I : (stackificationLiftVerticalCommonCover (J := J) G hG y y').Arrow ↦ I.f)).obj
      (stackificationLiftObjectGlued X G hG F y')) where
  hom I := stackificationLiftVerticalLocalMap X G hG F d I
  comm := by
    intro V q I₁ I₂ f₁ f₂ hf₁ hf₂
    exact stackificationLiftVerticalLocalMap_comm X G hG F d q f₁ f₂ hf₁ hf₂

/-- Helper for Chap08 Lemma 8 8 3: the componentwise local specification for a glued vertical
map. -/
abbrev stackificationLiftVerticalMapLocalSpec
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} {y y' : S'.p.Fiber U} (d : y ⟶ y')
    (f : stackificationLiftObjectGlued X G hG F y ⟶
        stackificationLiftObjectGlued X G hG F y') : Prop :=
  ∀ I : (stackificationLiftVerticalCommonCover (J := J) G hG y y').Arrow,
    ((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor.map f =
      stackificationLiftVerticalLocalMap X G hG F d I

/-- Helper for Chap08 Lemma 8 8 3: the fixed-cover gluing witness for the vertical map. -/
theorem stackificationLiftVerticalMap_existsUnique
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} {y y' : S'.p.Fiber U} (d : y ⟶ y') :
    ∃! f : stackificationLiftObjectGlued X G hG F y ⟶
        stackificationLiftObjectGlued X G hG F y',
      stackificationLiftVerticalMapLocalSpec X G hG F d f :=
  stack_cover_hom_glue_existsUnique_componentwise X
    (stackificationLiftVerticalCommonCover (J := J) G hG y y')
    (stackificationLiftVerticalDescentDataHom X G hG F d)

/-- Helper for Chap08 Lemma 8 8 3: the global fiber morphism obtained by gluing the local
vertical formula. -/
noncomputable def stackificationLiftVerticalMap
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} {y y' : S'.p.Fiber U} (d : y ⟶ y') :
    stackificationLiftObjectGlued X G hG F y ⟶
      stackificationLiftObjectGlued X G hG F y' :=
  Classical.choose
    (stackificationLiftVerticalMap_existsUnique X G hG F d)

/-- Helper for Chap08 Lemma 8 8 3: the glued vertical map satisfies its componentwise local
specification. -/
theorem stackificationLiftVerticalMap_local_spec
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} {y y' : S'.p.Fiber U} (d : y ⟶ y') :
    stackificationLiftVerticalMapLocalSpec X G hG F d
      (stackificationLiftVerticalMap X G hG F d) :=
  (Classical.choose_spec
    (stackificationLiftVerticalMap_existsUnique X G hG F d)).1

/-- Helper for Chap08 Lemma 8 8 3: the glued vertical map restricts to the prescribed local
formula on each member of the common cover. -/
theorem stackificationLiftVerticalMap_local
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} {y y' : S'.p.Fiber U} (d : y ⟶ y')
    (I : (stackificationLiftVerticalCommonCover (J := J) G hG y y').Arrow) :
    ((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor.map
        (stackificationLiftVerticalMap X G hG F d) =
      stackificationLiftVerticalLocalMap X G hG F d I :=
  stackificationLiftVerticalMap_local_spec X G hG F d I

end

end CategoryTheory
