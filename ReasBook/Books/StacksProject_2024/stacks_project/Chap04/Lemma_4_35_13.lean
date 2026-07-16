import Mathlib
import StacksProject_2024.stacks_project.Chap04.Definition_4_35_1
import StacksProject_2024.stacks_project.Chap04.Lemma_4_33_11

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]

/- Domain-style sampling for Lemma 4.35.13:
- primary domain: fibred-in-groupoids structures on functors to a slice category.
- inspected owner-level declarations:
  `CategoryTheory.IsFibredInGroupoids`,
  `Functor.isFibered_of_comp_over_forget`,
  `Functor.isStronglyCartesian_of_comp_over_forget`,
  `IsFibredInGroupoids.isStronglyCartesian_map`.
- best owner abstraction: the source-facing statement should live directly on the owner class
  `IsFibredInGroupoids`; the slice-level structure is derived from the two transfer lemmas of
  Lemma `4.33.11`, not stored through a parallel local wrapper.
- primitive data: the fibred-in-groupoids structure on `p' ⋙ Over.forget U`.
- derived API: the induced `p'.IsFibered` instance from Lemma `4.33.11` and the resulting
  fibred-in-groupoids structure on `p'`.

Source/core/bridge triage:
- `source-facing`: `isFibredInGroupoids_of_comp_over_forget`.
- `core/canonical`: `IsFibredInGroupoids`, `Functor.IsFibered`, `Functor.IsStronglyCartesian`.
- `bridge/view`: the anonymous instance below derived from the source-facing theorem. -/

/-- Lemma 4.35.13: if a functor `p' : S ⥤ Over U` becomes fibred in groupoids after composing with
the forgetful functor `Over.forget U : Over U ⥤ C`, then `p'` is itself fibred in groupoids over
`Over U`. Equivalently, if a category fibred in groupoids over `C` factors through the slice
category `C/U`, then the induced functor to `C/U` is fibred in groupoids. -/
theorem isFibredInGroupoids_of_comp_over_forget {U : C} (p' : S ⥤ Over U)
    [IsFibredInGroupoids (p' ⋙ Over.forget U)] :
    IsFibredInGroupoids p' where
  toIsFibered := inferInstance
  isStronglyCartesian_map φ := by
    let q := p' ⋙ Over.forget U
    letI : IsFibredInGroupoids q := by
      dsimp [q]
      infer_instance
    letI : q.IsStronglyCartesian (p'.map φ).left φ := by
      simpa [q] using (show q.IsStronglyCartesian (q.map φ) φ from inferInstance)
    exact isStronglyCartesian_of_comp_over_forget p'

instance {U : C} (p' : S ⥤ Over U) [IsFibredInGroupoids (p' ⋙ Over.forget U)] :
    IsFibredInGroupoids p' :=
  isFibredInGroupoids_of_comp_over_forget p'

end CategoryTheory.Functor
