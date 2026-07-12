import Mathlib
import StacksProject_2024.Chap04.Lemma_4_35_2
import StacksProject_2024.Chap04.Definition_4_32_1
import StacksProject_2024.Chap08.Definition_8_5_1
import StacksProject_2024.Chap08.Lemma_8_4_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ u₃ v₁ v₂ v₃

namespace CategoryTheory

open BasedFunctor

section

variable {C : Type u₁} {S₁ : Type u₂} {S₂ : Type u₃}
variable [Category.{v₁} C] [Category.{v₂} S₁] [Category.{v₃} S₂]
variable (J : GrothendieckTopology C)

variable (p₁ : S₁ ⥤ C) (p₂ : S₂ ⥤ C)

/- Domain-style sampling for Lemma 8.5.4:
- primary domain: stacks in groupoids over a site, transported along equivalences in `Cat/C`.
- inspected owner-level declarations:
  `IsStackInGroupoids`,
  `isStackOnSite_iff_of_equivalence_over_base`,
  `IsFibredInGroupoids`,
  `BasedFunctor.fiber_isGroupoid_of_isEquivalenceOverBase`.
- best owner abstraction: the source-facing owner remains `IsStackInGroupoids J p`; the
  equivalence-over-base datum is only a bridge transporting the canonical owners
  `IsStackOnSite` and `IsFibredInGroupoids`.
- primitive data: the two projection functors and the over-base equivalence data.
- derived API: transport of `IsStackOnSite` and of the fiberwise groupoid condition, then
  reassembly through the existing owner instance
  `[IsFibredInGroupoids p] [IsStackOnSite J p] → IsStackInGroupoids J p`.

Source/core/bridge triage:
- `source-facing`: `isStackInGroupoids_iff_of_equivalence_over_base`.
- `core/canonical`: `IsStackInGroupoids`, `IsStackOnSite`, `IsFibredInGroupoids`, and
  `BasedFunctor.fiber_isGroupoid_of_isEquivalenceOverBase`.
- `bridge/view`: transport of the owner predicates along an equivalence over the base. -/

-- Proof sketch: transport the owner `IsStackOnSite` across the equivalence over the base by
-- Lemma `8.4.4`. Then transport the groupoid structure on each fiber via the owner theorem
-- `BasedFunctor.fiber_isGroupoid_of_isEquivalenceOverBase`, rebuild
-- `IsFibredInGroupoids` from the fiberwise groupoid condition, and conclude by the canonical
-- instance `[IsFibredInGroupoids p] [IsStackOnSite J p] → IsStackInGroupoids J p`.
/-- Lemma 8.5.4: if `S₁` and `S₂` are equivalent as categories over the site `(C, J)`, then
`S₁` is a stack in groupoids over `(C, J)` if and only if `S₂` is. -/
theorem isStackInGroupoids_iff_of_equivalence_over_base
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase) :
    IsStackInGroupoids J p₁ ↔ IsStackInGroupoids J p₂ := by
  constructor
  · intro h
    letI : IsStackInGroupoids J p₁ := h
    letI : IsStackOnSite J p₂ :=
      (isStackOnSite_iff_of_equivalence_over_base J p₁ p₂ F hF).1 inferInstance
    letI : IsFibredInGroupoids p₂ :=
      isFibredInGroupoids_of_isFibered_and_fiber_groupoid p₂ inferInstance
        fun U ↦ by
          letI : IsGroupoid ((BasedCategory.ofFunctor p₁).p.Fiber U) := by
            simpa using (inferInstance : IsGroupoid (p₁.Fiber U))
          exact BasedFunctor.fiber_isGroupoid_of_isEquivalenceOverBase F hF U
    exact inferInstance
  · intro h
    let e : EquivalenceOverBase F := Classical.choice hF.nonempty
    letI : IsStackInGroupoids J p₂ := h
    letI : IsStackOnSite J p₁ :=
      (isStackOnSite_iff_of_equivalence_over_base J p₁ p₂ F hF).2 inferInstance
    letI : IsFibredInGroupoids p₁ :=
      isFibredInGroupoids_of_isFibered_and_fiber_groupoid p₁ inferInstance
        fun U ↦ by
          letI : IsGroupoid ((BasedCategory.ofFunctor p₂).p.Fiber U) := by
            simpa using (inferInstance : IsGroupoid (p₂.Fiber U))
          exact BasedFunctor.fiber_isGroupoid_of_isEquivalenceOverBase
            e.inverse e.inverse_isEquivalenceOverBase U
    exact inferInstance

end

end CategoryTheory
