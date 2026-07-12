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
    have hp₁ : IsFibredInSetoids (BasedCategory.ofFunctor p₁).p := by
      simpa using (inferInstance : IsFibredInSetoids p₁)
    letI : IsStackInGroupoids J p₂ :=
      (isStackInGroupoids_iff_of_equivalence_over_base J p₁ p₂ F hF).1 inferInstance
    letI : IsFibredInSetoids p₂ :=
      by simpa using (isFibredInSetoids_iff_of_isEquivalenceOverBase F hF).1 hp₁
    infer_instance
  · intro h
    letI : IsStackInSetoids J p₂ := h
    have hp₂ : IsFibredInSetoids (BasedCategory.ofFunctor p₂).p := by
      simpa using (inferInstance : IsFibredInSetoids p₂)
    letI : IsStackInGroupoids J p₁ :=
      (isStackInGroupoids_iff_of_equivalence_over_base J p₁ p₂ F hF).2 inferInstance
    letI : IsFibredInSetoids p₁ :=
      by simpa using (isFibredInSetoids_iff_of_isEquivalenceOverBase F hF).2 hp₂
    infer_instance

end

end CategoryTheory
