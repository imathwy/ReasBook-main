import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.Arrows

universe u v uS vS w wD vD

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- Helper for Chap08 Lemma 8 8 3: the chosen vertical factor through the chosen cartesian
pullback is the unique vertical arrow with that factorization property. -/
theorem stackificationLiftArrowVerticalFactor_eq_of_fac
    {T T' : S'.S} (φ : T ⟶ T')
    (v :
      (Functor.Fiber.mk (p := S'.p) (a := T) rfl : S'.p.Fiber (S'.p.obj T)) ⟶
        stackificationLiftArrowPullbackTarget (S' := S') φ)
    (hv :
      v.1 ≫
        (canonicalPullbackChoice S'.p).map (S'.p.map φ)
          (Functor.Fiber.mk (p := S'.p) (a := T') rfl : S'.p.Fiber (S'.p.obj T')) =
        φ) :
    stackificationLiftArrowVerticalFactor (S' := S') φ = v := by
  apply Functor.Fiber.hom_ext
  let cart :=
    (canonicalPullbackChoice S'.p).map (S'.p.map φ)
      (Functor.Fiber.mk (p := S'.p) (a := T') rfl : S'.p.Fiber (S'.p.obj T'))
  change (stackificationLiftArrowVerticalFactor (S' := S') φ).1 = v.1
  letI : S'.p.IsStronglyCartesian (S'.p.map φ) cart :=
    (canonicalPullbackChoice S'.p).isStronglyCartesian (S'.p.map φ)
      (Functor.Fiber.mk (p := S'.p) (a := T') rfl : S'.p.Fiber (S'.p.obj T'))
  have hLeft :
      S'.p.IsHomLift (𝟙 (S'.p.obj T))
        (stackificationLiftArrowVerticalFactor (S' := S') φ).1 :=
    (stackificationLiftArrowVerticalFactor (S' := S') φ).2
  have hRight : S'.p.IsHomLift (𝟙 (S'.p.obj T)) v.1 := v.2
  have hpost :
      (stackificationLiftArrowVerticalFactor (S' := S') φ).1 ≫ cart =
        v.1 ≫ cart := by
    have hchosen :
        (stackificationLiftArrowVerticalFactor (S' := S') φ).1 ≫ cart =
          φ := by
      simpa [cart] using stackificationLiftArrowVerticalFactor_fac (S' := S') φ
    exact hchosen.trans hv.symm
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ S'.p _ _ _ _
      (S'.p.map φ) cart inferInstance _ _ (𝟙 (S'.p.obj T))
      (stackificationLiftArrowVerticalFactor (S' := S') φ).1 v.1 hLeft hRight hpost

end

end CategoryTheory
