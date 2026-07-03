import Mathlib
import StacksProject_2024.Chap04.Lemma_4_39_5
import StacksProject_2024.Chap08.Definition_8_6_1
import StacksProject_2024.Chap08.Lemma_8_5_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ u₃ v₁ v₂ v₃

namespace CategoryTheory

open BasedFunctor

section

variable {C : Type u₁} {S₁ : Type u₂} {S₂ : Type u₃}
variable [Category.{v₁} C] [Category.{v₂} S₁] [Category.{v₃} S₂]
variable (J : GrothendieckTopology C)

variable (p₁ : S₁ ⥤ C) (p₂ : S₂ ⥤ C)

/- Domain-style sampling for Lemma 8.6.4:
- primary domain: stack conditions on a site for categories fibred in setoids, transported along
  equivalences over the base category;
- inspected owner-level declarations:
  `IsStackInSetoids`,
  `IsStackInGroupoids`,
  `BasedFunctor.isFibredInSetoids_iff_of_isEquivalenceOverBase`,
  `isStackInGroupoids_iff_of_equivalence_over_base`;
- best owner abstraction: the source-facing owner `IsStackInSetoids J p`; the conjunction
  `IsFibredInSetoids p ∧ IsStackOnSite J p` is derived API and should not remain the main public
  surface;
- primitive data: the projection functor `p : S ⥤ C` and the equivalence-over-base data `hF`;
- derived API: the transported fiberwise thinness, which combines with the existing owner theorem
  `isStackInGroupoids_iff_of_equivalence_over_base` to recover `IsStackInSetoids`.

Source/core/bridge triage:
- `source-facing`: `isStackInSetoids_iff_of_equivalence_over_base`;
- `core/canonical`: `IsStackInSetoids`, `IsStackInGroupoids`, and
  `BasedFunctor.isFibredInSetoids_iff_of_isEquivalenceOverBase`;
- `bridge/view`: transport of the owner components `IsStackInGroupoids` and
  `IsFibredInSetoids` along an equivalence over the base. -/

/-- Lemma 8.6.4: if `S₁` and `S₂` are equivalent as categories over the site `(C, J)`, then
`S₁` is a stack in setoids over `(C, J)` if and only if `S₂` is a stack in setoids over
`(C, J)`. -/
theorem isStackInSetoids_iff_of_equivalence_over_base
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase) :
    IsStackInSetoids J p₁ ↔ IsStackInSetoids J p₂ := by
  constructor
  · intro h
    letI : IsStackInSetoids J p₁ := h
    letI : IsStackInGroupoids J p₂ :=
      (isStackInGroupoids_iff_of_equivalence_over_base J p₁ p₂ F hF).1 inferInstance
    have hthin₂ : ∀ U : C, Quiver.IsThin (p₂.Fiber U) := by
      intro U
      letI : (F.fiberFunctor U).IsEquivalence :=
        BasedFunctor.fiberFunctor_isEquivalence_of_isEquivalenceOverBase F hF U
      let e := (F.fiberFunctor U).asEquivalence
      letI : Quiver.IsThin (p₁.Fiber U) := inferInstance
      have hthin : Quiver.IsThin (p₁.Fiber U) := inferInstance
      refine fun X Y ↦ ⟨fun f g ↦ ?_⟩
      have hmap : e.inverse.map f = e.inverse.map g := by
        exact @Subsingleton.elim (e.inverse.obj X ⟶ e.inverse.obj Y) (hthin _ _) _ _
      apply e.inverse.map_injective
      exact hmap
    have hsetoids₂ : IsFibredInSetoids p₂ := by
      letI : ∀ U : C, Quiver.IsThin (p₂.Fiber U) := hthin₂
      infer_instance
    letI : IsFibredInSetoids p₂ := hsetoids₂
    infer_instance
  · intro h
    letI : IsStackInSetoids J p₂ := h
    letI : IsStackInGroupoids J p₁ :=
      (isStackInGroupoids_iff_of_equivalence_over_base J p₁ p₂ F hF).2 inferInstance
    have hthin₁ : ∀ U : C, Quiver.IsThin (p₁.Fiber U) := by
      intro U
      letI : (F.fiberFunctor U).IsEquivalence :=
        BasedFunctor.fiberFunctor_isEquivalence_of_isEquivalenceOverBase F hF U
      let e := (F.fiberFunctor U).asEquivalence
      letI : Quiver.IsThin (p₂.Fiber U) := inferInstance
      have hthin : Quiver.IsThin (p₂.Fiber U) := inferInstance
      refine fun X Y ↦ ⟨fun f g ↦ ?_⟩
      have hmap : e.functor.map f = e.functor.map g := by
        exact @Subsingleton.elim (e.functor.obj X ⟶ e.functor.obj Y) (hthin _ _) _ _
      apply e.functor.map_injective
      exact hmap
    have hsetoids₁ : IsFibredInSetoids p₁ := by
      letI : ∀ U : C, Quiver.IsThin (p₁.Fiber U) := hthin₁
      infer_instance
    letI : IsFibredInSetoids p₁ := hsetoids₁
    infer_instance

end

end CategoryTheory
