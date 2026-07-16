import Mathlib
import StacksProject_2024.stacks_project.Chap04.Definition_4_35_6
import StacksProject_2024.stacks_project.Chap04.Definition_4_37_2
import StacksProject_2024.stacks_project.Chap04.Lemma_4_36_4

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

open Opposite
open scoped CategoryTheory.Bicategory

namespace CategoryTheory

open BasedFunctor

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

/-
Domain-style sampling for Lemma 4.37.3:
- primary domain: categories fibred in groupoids and their canonical split models over a fixed
  base;
- sampled owner-level declarations:
  `BasedFunctor.IsEquivalenceOverBase`,
  `FibredCategoryOver.hom_isEquivalenceOverBase`,
  `Functor.IsSplitFibredCategory.exists_groupoidPresheafModel_over_base`,
  `exists_split_fibred_category_over_base`,
  `IsFibredInGroupoids`;
- best owner abstraction: the canonical bridge theorem here should stay on
  `BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q` with the owner predicate
  `BasedFunctor.IsEquivalenceOverBase`, because this is the exact universe-general surface already
  provided by `Functor.IsSplitFibredCategory.exists_groupoidPresheafModel_over_base`; the split
  replacement is first produced in `FibredCategoryOver C`, and the explicit presheaf-of-groupoids
  model is then supplied by
  `Functor.IsSplitFibredCategory.exists_groupoidPresheafModel_over_base`.
- primitive data: only the fibred-in-groupoids functor `p`.
- derived API: the split model over `C` and the source-facing existential statement below.

Source/core/bridge triage:
- `source-facing`: the existence of a split groupoid-valued model equivalent over the base;
- `core/canonical`: `BasedFunctor.IsEquivalenceOverBase`, `FibredCategoryOver C`,
  `Bicategory.Equivalence`, and the owner predicates
  `Functor.IsSplitFibredCategory` and `IsFibredInGroupoids`;
- `bridge/view`: the presheaf `F : Cᵒᵖ ⥤ Grpd` together with its co-Grothendieck presentation and
  the induced based functor over `C`. -/

namespace IsFibredInGroupoids

/-- Lemma 4.37.3: every category fibred in groupoids `p : S ⥤ C` is equivalent over `C` to the
split category attached to a contravariant groupoid-valued presheaf on `C`. -/
  theorem exists_groupoidPresheafModel_over_base
    (p : S ⥤ C) [IsFibredInGroupoids p] :
    ∃ F : Cᵒᵖ ⥤ Grpd.{v₂, u₂},
      ∃ e : BasedCategory.ofFunctor p ⥤ᵇ
          BasedCategory.ofFunctor
            (Pseudofunctor.CoGrothendieck.forget
              ((F ⋙ Grpd.forgetToCat).toPseudofunctor')),
        e.IsEquivalenceOverBase := by
  rcases exists_split_fibred_category_over_base p with ⟨Y, e, hYsplit⟩
  have he : FibredCategoryMor.IsEquivalenceOverBase e.hom :=
    FibredCategoryOver.hom_isEquivalenceOverBase e
  have hY : IsFibredInGroupoids Y.p :=
    isFibredInGroupoids_of_isFibered_and_fiber_groupoid Y.p inferInstance fun U ↦ by
      letI : IsGroupoid ((BasedCategory.ofFunctor p).p.Fiber U) := by
        simpa using (inferInstance : IsGroupoid (p.Fiber U))
      exact fiber_isGroupoid_of_isEquivalenceOverBase (FibredCategoryMor.toBasedFunctor e.hom)
        (by simpa using he) U
  letI : IsFibredInGroupoids Y.p := hY
  letI : Y.p.IsSplitFibredCategory := hYsplit
  rcases Functor.IsSplitFibredCategory.exists_groupoidPresheafModel_over_base Y.p with
    ⟨F, eF, hF⟩
  refine ⟨F, FibredCategoryMor.toBasedFunctor e.hom ⋙ eF, ?_⟩
  simpa using BasedFunctor.IsEquivalenceOverBase.comp (by simpa using he) hF

end IsFibredInGroupoids

end CategoryTheory
