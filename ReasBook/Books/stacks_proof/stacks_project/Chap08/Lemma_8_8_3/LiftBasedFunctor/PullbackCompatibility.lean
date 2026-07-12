import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.Arrows
import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.PullbackCompatibility.DescentComparison
import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.PullbackCompatibility.PulledGluedVertical
import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.PullbackCompatibility.VerticalNaturalityCore

universe u v uS vS w wD vD

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- The explicit comparison between gluing after source pullback and pulling back the glued
object in the target stack.

The object descent construction must commute, up to a chosen fiber isomorphism, with pulling the
target object back along a base arrow. This is the comparison needed to append the cartesian part
of a general arrow after the already-glued vertical part. -/
noncomputable def stackificationLiftObjectPullbackComparison
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (f : V ⟶ U) (y : S'.p.Fiber U) :
    stackificationLiftObjectGlued X G hG F
        (f ^*[canonicalPullbackChoice S'.p] y) ≅
      f ^*[canonicalPullbackChoice X.p]
        stackificationLiftObjectGlued X G hG F y := by
  let Sfp := stackificationLiftPulledObjectCover (J := J) G hG f y
  let Ψ := (canonicalFiberPseudofunctor X.p).toDescentData
    (fun I : Sfp.Arrow ↦ I.f)
  haveI : Ψ.IsEquivalence :=
    (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence
      (J := J) (p := X.p)).1 inferInstance V Sfp
  let sourceIso :
      Ψ.obj
          (stackificationLiftObjectGlued X G hG F
            (f ^*[canonicalPullbackChoice S'.p] y)) ≅
        stackificationLiftPulledObjectDescentData X G hG F f y :=
    stackificationLiftPulledObjectDescentComparison X G hG F f y
  let targetIso :
      Ψ.obj
          (f ^*[canonicalPullbackChoice X.p]
            stackificationLiftObjectGlued X G hG F y) ≅
        stackificationLiftPulledObjectDescentData X G hG F f y :=
    stackificationLiftPulledGluedObjectDescentIso X G hG F f y
  let ddIso :
      Ψ.obj
          (stackificationLiftObjectGlued X G hG F
            (f ^*[canonicalPullbackChoice S'.p] y)) ≅
      Ψ.obj
          (f ^*[canonicalPullbackChoice X.p]
            stackificationLiftObjectGlued X G hG F y) :=
    sourceIso ≪≫ targetIso.symm
  exact (Functor.FullyFaithful.ofFullyFaithful Ψ).preimageIso ddIso

/-- Helper for Chap08 Lemma 8 8 3: the chosen pullback comparison has the prescribed
component on every branch of the pulled cover. -/
theorem stackificationLiftObjectPullbackComparison_local_hom
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (f : V ⟶ U) (y : S'.p.Fiber U)
    (I : (stackificationLiftPulledObjectCover (J := J) G hG f y).Arrow) :
    ((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor.map
        (stackificationLiftObjectPullbackComparison X G hG F f y).hom =
      (stackificationLiftPulledObjectDescentComparison X G hG F f y).hom.hom I ≫
        (stackificationLiftPulledGluedObjectDescentIso X G hG F f y).inv.hom I := by
  dsimp only [stackificationLiftObjectPullbackComparison]
  rw [Functor.FullyFaithful.preimageIso_hom]
  let Sfp := stackificationLiftPulledObjectCover (J := J) G hG f y
  let Ψ := (canonicalFiberPseudofunctor X.p).toDescentData
    (fun I : Sfp.Arrow ↦ I.f)
  haveI : Ψ.IsEquivalence :=
    (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence
      (J := J) (p := X.p)).1 inferInstance V Sfp
  change (Ψ.map ((Functor.FullyFaithful.ofFullyFaithful Ψ).preimage _)).hom I = _
  rw [Functor.FullyFaithful.map_preimage]
  rfl

/-- Helper for Chap08 Lemma 8 8 3: the inverse of the chosen pullback comparison has the
prescribed component on every branch of the pulled cover. -/
theorem stackificationLiftObjectPullbackComparison_local_inv
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (f : V ⟶ U) (y : S'.p.Fiber U)
    (I : (stackificationLiftPulledObjectCover (J := J) G hG f y).Arrow) :
    ((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor.map
        (stackificationLiftObjectPullbackComparison X G hG F f y).inv =
      (stackificationLiftPulledGluedObjectDescentIso X G hG F f y).hom.hom I ≫
        (stackificationLiftPulledObjectDescentComparison X G hG F f y).inv.hom I := by
  dsimp only [stackificationLiftObjectPullbackComparison]
  rw [Functor.FullyFaithful.preimageIso_inv]
  let Sfp := stackificationLiftPulledObjectCover (J := J) G hG f y
  let Ψ := (canonicalFiberPseudofunctor X.p).toDescentData
    (fun I : Sfp.Arrow ↦ I.f)
  haveI : Ψ.IsEquivalence :=
    (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence
      (J := J) (p := X.p)).1 inferInstance V Sfp
  change (Ψ.map ((Functor.FullyFaithful.ofFullyFaithful Ψ).preimage _)).hom I = _
  rw [Functor.FullyFaithful.map_preimage]
  rfl

/-- The next small blocker for Chap08 Lemma 8 8 3, packaged as a nonempty witness for
consumers that only need existence. -/
theorem stackificationLiftObjectPullbackComparison_nonempty
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (f : V ⟶ U) (y : S'.p.Fiber U) :
    Nonempty
      (stackificationLiftObjectGlued X G hG F
          (f ^*[canonicalPullbackChoice S'.p] y) ≅
        f ^*[canonicalPullbackChoice X.p]
          stackificationLiftObjectGlued X G hG F y) :=
  ⟨stackificationLiftObjectPullbackComparison X G hG F f y⟩

/-- Helper for Chap08 Lemma 8 8 3: the object comparison specialized to the chosen cartesian
target of a total arrow in `S'`. -/
noncomputable def stackificationLiftArrowPullbackObjectComparison
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {T T' : S'.S} (φ : T ⟶ T') :
    stackificationLiftObjectGlued X G hG F
        (stackificationLiftArrowPullbackTarget (S' := S') φ) ≅
      S'.p.map φ ^*[canonicalPullbackChoice X.p]
        stackificationLiftObjectGlued X G hG F
          (Functor.Fiber.mk (p := S'.p) (a := T') rfl) :=
  stackificationLiftObjectPullbackComparison X G hG F (S'.p.map φ)
    (Functor.Fiber.mk (p := S'.p) (a := T') rfl)

end

end CategoryTheory
