import Mathlib
import stacks_project.Chap04.Definition_4_32_1
import stacks_project.Chap04.Definition_4_35_1
import stacks_project.Chap04.Lemma_4_33_7
import stacks_project.Chap04.Lemma_4_32_3
import stacks_project.Chap04.Lemma_4_41_1_2_Yoneda_lemma_for_fibred_categories

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open CategoryOver
open BasedFunctor
open Functor
open Functor.Fiber
open CategoryTheory.Limits
open Functor.IsHomLift

variable {C : Type u} [Category.{v} C]
variable {X Y : Type (max u v)} [Category.{v} X] [Category.{v} Y]
variable {pX : X ⥤ C} {pY : Y ⥤ C}

namespace FibredCategoryOver

/- Domain-style sampling for Lemma 4.42.1:
- primary domain: fibers of the left projection of the explicit slice `2`-fibre product.
- inspected owner-level declarations:
  `BasedFunctor.fiberFunctor`,
  `Fiber.inducedFunctor`,
  `CategoryOver.fibreOfPullback_equiv_pullbackOfFibres`,
  `explicitTwoFibreProductLeftProjection`,
  `StructuredArrow`.
- best owner abstraction: the core object here is the fiber of the owner projection
  `explicitTwoFibreProductLeftProjection G F`; over a fixed `f : Over U`, that fiber should be
  described by the canonical comma owner `StructuredArrow` in the fiber `pY.Fiber f.left`, not by
  a new slice-specific wrapper.
- primitive data: the based functors `G`, `F`, and the fixed slice object `f : Over U`.
- derived API: the canonical equivalence from that structured-arrow category to the corresponding
  fiber of the explicit `2`-fibre-product projection.

Source/core/bridge triage:
- `source-facing`: `sliceTwoFibreProductStructuredArrowEquivFiber`.
- `core/canonical`: `Functor.Fiber`, `BasedFunctor.fiberFunctor`,
  `CategoryOver.fibreOfPullback_equiv_pullbackOfFibres`,
  `explicitTwoFibreProductLeftProjection`, and `StructuredArrow`.
- `bridge/view`: the internal comparison functors
  `sliceTwoFibreProductStructuredArrowToExplicit` and
  `sliceTwoFibreProductStructuredArrowToFiber`. -/

end FibredCategoryOver

section SliceTwoFibreProductStructuredArrow

variable {U : C}
variable (G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor pY)
variable (F : BasedCategory.ofFunctor pX ⥤ᵇ BasedCategory.ofFunctor pY)

/-- The canonical functor from the structured-arrow category to the total explicit
`2`-fibre product, with constant left projection `f`. -/
private noncomputable def sliceTwoFibreProductStructuredArrowToExplicit
    [IsFibredInGroupoids pY] (f : Over U) :
    StructuredArrow ((G.fiberFunctor f.left).obj (Fiber.mk rfl)) (F.fiberFunctor f.left) ⥤
      (explicitTwoFibreProduct G F).obj where
  obj A := by
    letI : IsFibredInGroupoids (BasedCategory.ofFunctor pY).p := by
      change IsFibredInGroupoids pY
      infer_instance
    letI : IsIso A.hom := IsFibredInGroupoids.hom_isIso f.left A.hom
    exact
      { U := f.left
        obj :=
          { fst := Fiber.mk rfl
            snd := A.right
            iso := asIso A.hom } }
  map {A B} α := by
    letI : (Over.forget U).IsHomLift (𝟙 f.left) (𝟙 f) := IsHomLift.id rfl
    letI : pX.IsHomLift (𝟙 f.left) α.right.1 := α.right.2
    exact
      { base := 𝟙 f.left
        a := (Fiber.homMk (Over.forget U) f.left (𝟙 f)).1
        a_over := (Fiber.homMk (Over.forget U) f.left (𝟙 f)).2
        b := (Fiber.homMk pX f.left α.right.1).1
        b_over := (Fiber.homMk pX f.left α.right.1).2
        comm := by
          refine ⟨?_⟩
          change G.map (𝟙 f) ≫ B.hom.1 = A.hom.1 ≫ F.map α.right.1
          have hα : B.hom.1 = A.hom.1 ≫ ((F.fiberFunctor f.left).map α.right).1 := by
            simpa using (congrArg Subtype.val (StructuredArrow.w α)).symm
          have hg : G.map (𝟙 f) = 𝟙 _ := by
            exact G.toFunctor.map_id f
          rw [hg, Category.id_comp]
          simpa using hα }
  map_id A := by
    cases A
    rfl
  map_comp α β := by
    apply ExplicitTwoFibreProductHom.ext
    · change 𝟙 f = 𝟙 f ≫ 𝟙 f
      simp
    · letI : pX.IsHomLift (𝟙 f.left) α.right.1 := α.right.2
      letI : pX.IsHomLift (𝟙 f.left) β.right.1 := β.right.2
      rfl

private theorem sliceTwoFibreProductStructuredArrowToExplicit_comp_projection
    [IsFibredInGroupoids pY] (f : Over U) :
    sliceTwoFibreProductStructuredArrowToExplicit G F f ⋙
        (explicitTwoFibreProductLeftProjection G F).toFunctor =
      (Functor.const
        (StructuredArrow ((G.fiberFunctor f.left).obj (Fiber.mk rfl)) (F.fiberFunctor f.left))).obj
        f :=
  Functor.ext (fun _ ↦ rfl) (fun _ _ α ↦ by
    change 𝟙 f = eqToHom (by simp) ≫ 𝟙 f ≫ eqToHom (by simp)
    simp)

/-- The canonical functor from the structured-arrow category
`(G(f) ↓ F_V)` to the fiber over `f` of the explicit `2`-fibre-product projection. -/
private noncomputable def sliceTwoFibreProductStructuredArrowToFiber
    [IsFibredInGroupoids pY] (f : Over U) :
    StructuredArrow ((G.fiberFunctor f.left).obj (Fiber.mk rfl)) (F.fiberFunctor f.left) ⥤
      ((explicitTwoFibreProductLeftProjection G F).toFunctor).Fiber f :=
  Fiber.inducedFunctor
    (sliceTwoFibreProductStructuredArrowToExplicit_comp_projection G F f)

-- Proof sketch: an object of the fiber over `f : V ⟶ U` in the explicit `2`-fibre-product
-- already has left leg equal to `f`, so the remaining data are exactly an object
-- `x ∈ X_V` together with a morphism `G(f) ⟶ F(x)` in `Y_V`, i.e. a structured arrow from the
-- canonical fibre object `G(f)` to the induced fibre functor `F_V`.
/-- Lemma 4.42.1: for a functor `G : C/U ⥤ Y` over `C` and a functor `F : X ⥤ Y` over `C`, the
fiber over `f : V ⟶ U` of the explicit `2`-fibre-product projection
`(C/U) ×_Y X ⟶ C/U` is canonically equivalent to the structured-arrow category
`StructuredArrow (G(f)) (F_V)`, where `G(f)` is regarded as an object of `Y_V` and `F_V` is the
induced functor `X_V ⥤ Y_V`. Equivalently, its objects are pairs `(x, φ)` with `x ∈ X_V` and
`φ : G(f) ⟶ F(x)` in `Y_V`. -/
private theorem sliceTwoFibreProductStructuredArrowToFiber_isEquivalence
    [IsFibredInGroupoids pY] (f : Over U) :
    (sliceTwoFibreProductStructuredArrowToFiber G F f).IsEquivalence := sorry

/-- The canonical equivalence in Lemma 4.42.1 between the structured-arrow category
`StructuredArrow (G(f)) (F_V)` and the fiber over `f` of the left projection
`(C/U) ×_Y X ⟶ C/U`. -/
noncomputable def sliceTwoFibreProductStructuredArrowEquivFiber
    [IsFibredInGroupoids pY] (f : Over U) :
    StructuredArrow ((G.fiberFunctor f.left).obj (Fiber.mk rfl)) (F.fiberFunctor f.left) ≌
      ((explicitTwoFibreProductLeftProjection G F).toFunctor).Fiber f :=
  letI : (sliceTwoFibreProductStructuredArrowToFiber G F f).IsEquivalence :=
    sliceTwoFibreProductStructuredArrowToFiber_isEquivalence G F f
  (sliceTwoFibreProductStructuredArrowToFiber G F f).asEquivalence

end SliceTwoFibreProductStructuredArrow

end CategoryTheory
