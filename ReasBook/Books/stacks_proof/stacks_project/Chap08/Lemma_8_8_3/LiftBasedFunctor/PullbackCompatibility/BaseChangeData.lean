import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.Arrows

universe u v uS vS

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- Helper for Chap08 Lemma 8 8 3: the base-changed cover used to compare object gluing with
pullback in the target stack. -/
noncomputable def stackificationLiftPulledObjectCover
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    {U V : C} (f : V ⟶ U) (y : S'.p.Fiber U) :
    J.Cover V :=
  (stackificationLiftObjectCover (J := J) G hG y).pullback f

/-- Helper for Chap08 Lemma 8 8 3: a source model on a branch of the pulled cover, obtained by
pulling back the source model on the corresponding branch of the original cover. -/
noncomputable def stackificationLiftPulledObjectCoverModel
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    {U V : C} (f : V ⟶ U) (y : S'.p.Fiber U)
    (I : (stackificationLiftPulledObjectCover (J := J) G hG f y).Arrow) :
    Σ' xI : S.p.Fiber I.Y,
      ((FibredCategoryMor.fiberFunctor G I.Y).obj xI) ≅
        I.f ^*[canonicalPullbackChoice S'.p]
          (f ^*[canonicalPullbackChoice S'.p] y) :=
  let baseI : (stackificationLiftObjectCover (J := J) G hG y).Arrow := I.base
  ⟨(stackificationLiftObjectModel (J := J) G hG y baseI).1,
    (stackificationLiftObjectModel (J := J) G hG y baseI).2 ≪≫
      mapCompAppIso S'.p f I.f (I.f ≫ f)
        (FibredCategoryMor.comp_toLoc_eq f I.f (I.f ≫ f) rfl) y⟩

/-- Helper for Chap08 Lemma 8 8 3: the descent-data pullback functor attached to the pulled
object cover. -/
noncomputable def stackificationLiftPulledObjectDescentPullFunctor
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    {U V : C} (f : V ⟶ U) (y : S'.p.Fiber U) :
    (canonicalFiberPseudofunctor X.p).DescentData
        (fun I : (stackificationLiftObjectCover (J := J) G hG y).Arrow ↦ I.f) ⥤
      (canonicalFiberPseudofunctor X.p).DescentData
        (fun I : (stackificationLiftPulledObjectCover (J := J) G hG f y).Arrow ↦ I.f) :=
  Pseudofunctor.DescentData.pullFunctor
    (canonicalFiberPseudofunctor X.p)
    (f := fun I : (stackificationLiftObjectCover (J := J) G hG y).Arrow ↦ I.f)
    (f' := fun I : (stackificationLiftPulledObjectCover (J := J) G hG f y).Arrow ↦ I.f)
    (p := f)
    (α := fun I : (stackificationLiftPulledObjectCover (J := J) G hG f y).Arrow ↦ I.base)
    (p' := fun I : (stackificationLiftPulledObjectCover (J := J) G hG f y).Arrow ↦ 𝟙 I.Y)
    (w := fun I : (stackificationLiftPulledObjectCover (J := J) G hG f y).Arrow ↦ by
      simp [stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base])

/-- Helper for Chap08 Lemma 8 8 3: the object-descent data for `y`, pulled back to the
base-changed cover. -/
noncomputable def stackificationLiftPulledObjectDescentData
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (f : V ⟶ U) (y : S'.p.Fiber U) :
    (canonicalFiberPseudofunctor X.p).DescentData
      (fun I : (stackificationLiftPulledObjectCover (J := J) G hG f y).Arrow ↦ I.f) :=
  (stackificationLiftPulledObjectDescentPullFunctor X G hG f y).obj
    (stackificationLiftObjectDescentData X G hG F y)

/-- Helper for Chap08 Lemma 8 8 3: the actual pullback of the already-glued object has descent
data equal to the pulled-back descent data of the original glued object. -/
noncomputable def stackificationLiftPulledGluedObjectDescentIso
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (f : V ⟶ U) (y : S'.p.Fiber U) :
    ((canonicalFiberPseudofunctor X.p).toDescentData
      (fun I : (stackificationLiftPulledObjectCover (J := J) G hG f y).Arrow ↦ I.f)).obj
        (f ^*[canonicalPullbackChoice X.p]
          stackificationLiftObjectGlued X G hG F y) ≅
      stackificationLiftPulledObjectDescentData X G hG F f y :=
  let pullF := stackificationLiftPulledObjectDescentPullFunctor X G hG f y
  ((Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso
    (canonicalFiberPseudofunctor X.p)
    (f := fun I : (stackificationLiftObjectCover (J := J) G hG y).Arrow ↦ I.f)
    (f' := fun I : (stackificationLiftPulledObjectCover (J := J) G hG f y).Arrow ↦ I.f)
    (p := f)
    (α := fun I : (stackificationLiftPulledObjectCover (J := J) G hG f y).Arrow ↦ I.base)
    (p' := fun I : (stackificationLiftPulledObjectCover (J := J) G hG f y).Arrow ↦ 𝟙 I.Y)
    (w := fun I : (stackificationLiftPulledObjectCover (J := J) G hG f y).Arrow ↦ by
      simp [stackificationLiftPulledObjectCover, GrothendieckTopology.Cover.Arrow.base])).app
        (stackificationLiftObjectGlued X G hG F y)).symm ≪≫
    pullF.mapIso (stackificationLiftObjectGluedIso X G hG F y)

/-- Helper for Chap08 Lemma 8 8 3: the pulled-back descent data of `y` is effective in the
target stack. -/
theorem stackificationLiftPulledObjectGlued_exists
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (f : V ⟶ U) (y : S'.p.Fiber U) :
    ∃ Hy : X.p.Fiber V,
      Nonempty
        (((canonicalFiberPseudofunctor X.p).toDescentData
          (fun I : (stackificationLiftPulledObjectCover (J := J) G hG f y).Arrow ↦ I.f)).obj
            Hy ≅
          stackificationLiftPulledObjectDescentData X G hG F f y) := by
  exact
    stack_cover_obj_glue (J := J) X
      (stackificationLiftPulledObjectCover (J := J) G hG f y)
      (stackificationLiftPulledObjectDescentData X G hG F f y)

/-- Helper for Chap08 Lemma 8 8 3: the object obtained by gluing the pulled-back descent data of
`y` on the base-changed cover. -/
noncomputable def stackificationLiftPulledObjectGlued
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (f : V ⟶ U) (y : S'.p.Fiber U) : X.p.Fiber V :=
  Classical.choose (stackificationLiftPulledObjectGlued_exists X G hG F f y)

/-- Helper for Chap08 Lemma 8 8 3: the pulled-cover glued object realizes the pulled-back
descent data. -/
noncomputable def stackificationLiftPulledObjectGluedIso
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (f : V ⟶ U) (y : S'.p.Fiber U) :
    ((canonicalFiberPseudofunctor X.p).toDescentData
      (fun I : (stackificationLiftPulledObjectCover (J := J) G hG f y).Arrow ↦ I.f)).obj
        (stackificationLiftPulledObjectGlued X G hG F f y) ≅
      stackificationLiftPulledObjectDescentData X G hG F f y :=
  Classical.choice
    (Classical.choose_spec
      (stackificationLiftPulledObjectGlued_exists X G hG F f y))

/-- Helper for Chap08 Lemma 8 8 3: gluing after pulling the descent data back along `f` gives
the same object as pulling back the already-glued object. -/
theorem stackificationLiftPulledObjectGluedPullbackIso_nonempty
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (f : V ⟶ U) (y : S'.p.Fiber U) :
    Nonempty
      (stackificationLiftPulledObjectGlued X G hG F f y ≅
        f ^*[canonicalPullbackChoice X.p]
          stackificationLiftObjectGlued X G hG F y) := by
  let Sfp := stackificationLiftPulledObjectCover (J := J) G hG f y
  let Ψ := (canonicalFiberPseudofunctor X.p).toDescentData
    (fun I : Sfp.Arrow ↦ I.f)
  haveI : Ψ.IsEquivalence :=
    (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence
      (J := J) (p := X.p)).1 inferInstance V Sfp
  let ddIso :
      Ψ.obj (stackificationLiftPulledObjectGlued X G hG F f y) ≅
        Ψ.obj
          (f ^*[canonicalPullbackChoice X.p]
            stackificationLiftObjectGlued X G hG F y) :=
    stackificationLiftPulledObjectGluedIso X G hG F f y ≪≫
      (stackificationLiftPulledGluedObjectDescentIso X G hG F f y).symm
  exact ⟨(Functor.FullyFaithful.ofFullyFaithful Ψ).preimageIso ddIso⟩

/-- Helper for Chap08 Lemma 8 8 3: chosen isomorphism between the pulled-cover glued object and
the pullback of the already-glued object. -/
noncomputable def stackificationLiftPulledObjectGluedPullbackIso
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (f : V ⟶ U) (y : S'.p.Fiber U) :
    stackificationLiftPulledObjectGlued X G hG F f y ≅
      f ^*[canonicalPullbackChoice X.p]
        stackificationLiftObjectGlued X G hG F y :=
  Classical.choice
    (stackificationLiftPulledObjectGluedPullbackIso_nonempty X G hG F f y)

end

end CategoryTheory
