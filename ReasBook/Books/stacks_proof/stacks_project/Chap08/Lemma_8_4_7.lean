import Mathlib
import StacksProject_2024.Chap08.Lemma_8_2_3

-- Declarations for this item will be appended below by the statement pipeline.

open Opposite
universe u v vS w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {X Y : FibredCategoryOver C}

namespace FibredCategoryMor

/- Domain-style sampling for Lemma 8.4.7:
- primary domain: morphisms of fibred categories over a base, their underlying based functors,
  and the canonical Hom-presheaf comparison maps on fibers;
- sampled owner-level declarations:
  `SubTwoCategory.Hom.toHom`,
  `FibredCategoryMor.fullyFaithful_iff_fiberwise`,
  `FibredCategoryMor.fibredMorphismPresheafMap`,
  `FibredCategoryMor.fibredMorphismPresheafMap_isIso_of_fullyFaithful`;
- best owner abstraction: the ambient owner morphism `F : X ⟶ Y`, with the canonical
  full-faithfulness owner `F.toHom`;
- primitive data: only `F`;
- derived API: the comparison morphisms `fibredMorphismPresheafMap F x y` and their `IsIso`
  criterion on each fiber.

Source/core/bridge triage:
- `source-facing`: the Hom-presheaf criterion for full faithfulness;
- `core/canonical`: `Nonempty F.toHom.FullyFaithful`;
- `bridge/view`: `fibredMorphismPresheafMap F x y`. -/

-- Proof sketch: if the underlying based functor of `F` is fully faithful, then after evaluating
-- the canonical morphism of Hom-presheaves from Lemma `8.2.3` on any object of `C/U`, one gets
-- the induced bijection on morphism sets in the corresponding fiber. Conversely, an isomorphism
-- of these Hom-sheaves gives bijectivity on all fiberwise morphism sets; choosing a strongly
-- cartesian lift of a base arrow reduces arbitrary morphisms over that arrow to morphisms in a
-- fiber, which shows full faithfulness of the canonical owner `toBasedFunctor F`.
/-- Lemma 8.4.7, formalized at the primitive owner level: a morphism of fibred categories is
fully faithful exactly when, for every `U : C` and every `x y ∈ X_U`, the canonical morphism of
Hom-presheaves `Mor_X(x, y) ⟶ Mor_Y(F(x), F(y))` on `C/U` is an isomorphism. For stacks, the
source and target Hom-presheaves are sheaves, so this recovers the usual source statement about
an isomorphism of sheaves. -/
@[stacks 04WQ]
theorem fullyFaithful_iff_fibredMorphismPresheafMap_isIso
    (F : X ⟶ Y) :
    Nonempty F.toHom.FullyFaithful ↔
      ∀ ⦃U : C⦄ (x y : X.p.Fiber U),
        IsIso (fibredMorphismPresheafMap F x y) := by
  constructor
  · intro hF _ x y
    exact fibredMorphismPresheafMap_isIso_of_fullyFaithful F hF x y
  · intro hF
    refine (FibredCategoryMor.fullyFaithful_iff_fiberwise F).2 ?_
    intro U
    rw [Functor.FullyFaithful.nonempty_iff_map_bijective]
    intro x y
    let eX : (x ⟶ y) ≃
        ((canonicalFiberPseudofunctor X.p).presheafHom x y).obj (op (Over.mk (𝟙 U))) :=
      (canonicalFiberPseudofunctor X.p).presheafHomObjHomEquiv
    let eY : ((fiberFunctor F U).obj x ⟶
        (fiberFunctor F U).obj y) ≃
        ((canonicalFiberPseudofunctor Y.p).presheafHom
          ((fiberFunctor F U).obj x)
          ((fiberFunctor F U).obj y)).obj (op (Over.mk (𝟙 U))) :=
      (canonicalFiberPseudofunctor Y.p).presheafHomObjHomEquiv
    let map :
        (x ⟶ y) → ((fiberFunctor F U).obj x ⟶ (fiberFunctor F U).obj y) :=
      (fiberFunctor F U).map
    let app := (fibredMorphismPresheafMap F x y).app (op (Over.mk (𝟙 U)))
    have hApp :
        Function.Bijective app := by
      rw [← isIso_iff_bijective]
      exact (NatTrans.isIso_iff_isIso_app (fibredMorphismPresheafMap F x y)).mp (hF x y) _
    have hApp_id (φ : x ⟶ y) :
        app (eX φ) = eY (map φ) := by
      exact fibredMorphismPresheafMap_app_id F x y φ
    have hAppComp : Function.Bijective (app ∘ eX) :=
      (Equiv.bijective_comp eX app).2 hApp
    have hCompEq : app ∘ eX = eY ∘ map := by
      funext φ
      exact hApp_id φ
    have hMapComp : Function.Bijective (eY ∘ map) := by
      rw [← hCompEq]
      exact hAppComp
    exact (Equiv.comp_bijective map eY).1 hMapComp

end FibredCategoryMor

end CategoryTheory
