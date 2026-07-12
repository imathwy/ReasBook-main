import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.PullbackCompatibility.PulledDescentNormalization

universe u v uS vS

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- The explicit object-level base-change comparison on the pulled cover for Chap08
Lemma 8 8 3.

On the base-changed cover of `y`, the object glued from the independently chosen cover of
`f ^* y` must induce the same descent data as the pulled-back descent data of `y`. Proving this
amounts to comparing the two local source-model systems on the common refinements of these two
covers. -/
noncomputable def stackificationLiftPulledObjectDescentComparison
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (f : V ⟶ U) (y : S'.p.Fiber U) :
    (((canonicalFiberPseudofunctor X.p).toDescentData
      (fun I : (stackificationLiftPulledObjectCover (J := J) G hG f y).Arrow ↦ I.f)).obj
        (stackificationLiftObjectGlued X G hG F
          (f ^*[canonicalPullbackChoice S'.p] y)) ≅
    stackificationLiftPulledObjectDescentData X G hG F f y) := by
  refine Pseudofunctor.DescentData.isoMk
    (fun I ↦ stackificationLiftPulledLocalIso X G hG F f y I) ?_
  intro W q I₁ I₂ f₁ f₂ hf₁ hf₂
  classical
  let z : S'.p.Fiber V := f ^*[canonicalPullbackChoice S'.p] y
  let Iz₁ := stackificationLiftPulledToObjectCover (J := J) G hG f y I₁
  let Iz₂ := stackificationLiftPulledToObjectCover (J := J) G hG f y I₂
  have hpulled :=
    stackificationLiftPulledDescentData_hom_eq_transition X G hG F f y q f₁ f₂ hf₁ hf₂
  have hmodel :=
    stackificationLiftPulledModelComparisonIso_comm X G hG F f y q f₁ f₂ hf₁ hf₂
  have hglued :=
    stackificationLiftObjectGluedLocalIso_comm X G hG F z q
      (I₁ := Iz₁) (I₂ := Iz₂) f₁ f₂ hf₁ hf₂
  let Fp := canonicalFiberPseudofunctor X.p
  let id₂ := (Fp.map f₂.op.toLoc).toFunctor.map
    ((Cat.Hom.toNatIso (Fp.mapId (LocallyDiscrete.mk (op I₂.Y)))).app
      ((FibredCategoryMor.fiberFunctor F I₂.Y).obj
        (stackificationLiftPulledObjectCoverModel (J := J) G hG f y I₂).1)).symm.hom
  dsimp only [stackificationLiftPulledLocalIso]
  simp only [Iso.trans_hom, Functor.map_comp, Category.assoc]
  slice_lhs 3 4 => exact hpulled
  slice_lhs 2 3 => exact (reassoc_of% hmodel) id₂
  let lp₁ := (Fp.map f₁.op.toLoc).toFunctor.map
    (stackificationLiftObjectGluedLocalIso X G hG F z Iz₁).hom
  let tr := stackificationLiftObjectTransition X G hG F z
    (stackificationLiftObjectCover (J := J) G hG z)
    (stackificationLiftObjectModel (J := J) G hG z) q
    (I₁ := Iz₁) (I₂ := Iz₂) f₁ f₂ hf₁ hf₂
  let em₂ := (Fp.map f₂.op.toLoc).toFunctor.map
    (stackificationLiftPulledModelComparisonIso X G hG F f y I₂).hom
  have hassoc_left : lp₁ ≫ (tr ≫ em₂) ≫ id₂ = lp₁ ≫ tr ≫ (em₂ ≫ id₂) := by
    simp only [Category.assoc]
  slice_lhs 1 4 => exact hassoc_left
  slice_lhs 1 2 => exact hglued
  let D₂ :=
    (((Fp.toDescentData
      (fun I : (stackificationLiftObjectCover (J := J) G hG z).Arrow ↦ I.f)).obj
        (stackificationLiftObjectGlued X G hG F z)).hom q
          (i₁ := Iz₁) (i₂ := Iz₂) f₁ f₂ hf₁ hf₂)
  let lp₂ := (Fp.map f₂.op.toLoc).toFunctor.map
    (stackificationLiftObjectGluedLocalIso X G hG F z Iz₂).hom
  change ((D₂ ≫ lp₂) ≫ em₂) ≫ id₂ = D₂ ≫ lp₂ ≫ em₂ ≫ id₂
  simp only [Category.assoc]

theorem stackificationLiftPulledObjectDescentComparison_hom_hom
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (f : V ⟶ U) (y : S'.p.Fiber U)
    (I : (stackificationLiftPulledObjectCover (J := J) G hG f y).Arrow) :
    (stackificationLiftPulledObjectDescentComparison X G hG F f y).hom.hom I =
      (stackificationLiftPulledLocalIso X G hG F f y I).hom := by
  rfl

/-- The isolated remaining object-level base-change comparison for Chap08 Lemma 8 8 3,
packaged as a nonempty witness for consumers that only need existence. -/
theorem stackificationLiftPulledObjectDescentComparison_nonempty
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U V : C} (f : V ⟶ U) (y : S'.p.Fiber U) :
    Nonempty
      (((canonicalFiberPseudofunctor X.p).toDescentData
        (fun I : (stackificationLiftPulledObjectCover (J := J) G hG f y).Arrow ↦ I.f)).obj
          (stackificationLiftObjectGlued X G hG F
            (f ^*[canonicalPullbackChoice S'.p] y)) ≅
      stackificationLiftPulledObjectDescentData X G hG F f y) :=
  ⟨stackificationLiftPulledObjectDescentComparison X G hG F f y⟩

end

end CategoryTheory
