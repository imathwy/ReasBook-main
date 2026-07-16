import Mathlib
import StacksProject_2024.stacks_project.Chap04.Lemma_4_35_3
import StacksProject_2024.stacks_project.Chap08.Definition_8_5_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

section

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]
variable (J : GrothendieckTopology C) (p : S ⥤ C)

/- Domain-style sampling for Lemma 8.5.3:
- primary domain: stacks over a site and the associated category fibred in groupoids cut out by
  strongly cartesian morphisms.
- inspected owner-level declarations:
  `stronglyCartesianProjection`,
  `stronglyCartesianProjection_isFibredInGroupoids`,
  `IsStackOnSite`,
  `IsStackInGroupoids`.
- best owner abstraction: the source-facing result should conclude in the Chapter 8 owner
  `IsStackInGroupoids J (stronglyCartesianProjection p)`, assembled from the Chapter 4 owner
  theorem giving the fibred-in-groupoids structure and the owner-level stack-on-site theorem on
  `stronglyCartesianProjection p`.
- primitive data: the original stack hypothesis `[IsStackOnSite J p]`.
- derived API: the owner-level theorem `stronglyCartesianProjection_isStackOnSite`, the
  fibred-in-groupoids instance on `stronglyCartesianProjection p`, and the final source-facing
  stack-in-groupoids theorem below.

Source/core/bridge triage:
- `source-facing`: `associatedGroupoidProjection_isStack`.
- `core/canonical`: `IsStackOnSite J _`, `IsStackInGroupoids J _`.
- `bridge/view`: `stronglyCartesianProjection` and the Chapter 4 owner theorem
  `stronglyCartesianProjection_isFibredInGroupoids`. -/

-- Proof sketch: Stacks Project, Lemma 8.5.3, identifies descent data in
-- `stronglyCartesianProjection p` with descent data in `p`, because the morphisms of the
-- associated category fibred in groupoids are precisely the strongly cartesian morphisms and these
-- contain all isomorphisms. Combined with Lemma `4.35.3`, this gives the canonical Chapter 8
-- conclusion that `stronglyCartesianProjection p` itself is a stack in groupoids over `(C, J)`.
theorem stronglyCartesianProjection_isStackOnSite
    [IsStackOnSite J p] :
    IsStackOnSite J (stronglyCartesianProjection p) := by
  sorry

/-- Lemma 8.5.3: if `p : S ⥤ C` is a stack over the site `(C, J)`, then the associated category
fibred in groupoids `stronglyCartesianProjection p` is a stack in groupoids over `(C, J)`. -/
theorem associatedGroupoidProjection_isStack
    [IsStackOnSite J p] :
    IsStackInGroupoids J (stronglyCartesianProjection p) := by
  letI : IsStackOnSite J (stronglyCartesianProjection p) :=
    stronglyCartesianProjection_isStackOnSite J p
  infer_instance

end

end CategoryTheory
