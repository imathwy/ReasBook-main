import Mathlib
import stacks_project.Chap04.Example_4_38_5
import stacks_project.Chap08.Definition_8_6_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace CategoryTheory

open CategoryOfElements

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Lemma 8.6.2:
- primary domain: stacks in sets on a site for the canonical category-of-elements projection
  attached to a set-valued presheaf.
- inspected owner-level declarations:
  `CategoryOfElements.π`,
  `presheaf_categoryOfElementsProjection_isFibredInSets`,
  `IsStackInSets`,
  `IsStackOnSite`.
- best owner abstraction: the chapter’s source-facing owner is `IsStackInSets J ((π F).leftOp)`;
  the weaker predicate `IsStackOnSite J ((π F).leftOp)` is only a derived bridge obtained from
  the already available fibred-in-sets structure on the category-of-elements projection.
- primitive data: a presheaf `F`.
- derived API: the companion bridge to `IsStackOnSite`, obtained by combining
  `presheaf_categoryOfElementsProjection_isFibredInSets` with the source-facing stack-in-sets
  theorem.

Source/core/bridge triage:
- `source-facing`: `presheaf_isSheaf_iff_categoryOfElements_isStackInSets`.
- `core/canonical`: `IsStackInSets J ((π F).leftOp)` together with the canonical instance
  `presheaf_categoryOfElementsProjection_isFibredInSets F`.
- `bridge/view`: `presheaf_isSheaf_iff_categoryOfElements_isStackOnSite`. -/

-- Proof sketch: the category-of-elements projection of `F` is canonically fibred in sets, so the
-- source statement should land directly in the chapter owner `IsStackInSets`. The weaker
-- stack-on-site predicate is then recovered as a thin companion bridge by inference.
/-- Lemma 8.6.2: under the equivalence of Lemma `4.38.6` between set-valued presheaves on `C` and
categories fibred in sets over `C`, a presheaf `F` is a sheaf for `J` exactly when the projection
of its category of elements is a stack in sets over `(C, J)`. -/
theorem presheaf_isSheaf_iff_categoryOfElements_isStackInSets
    (J : GrothendieckTopology C) (F : Cᵒᵖ ⥤ Type w) :
    Presheaf.IsSheaf J F ↔ IsStackInSets J ((π F).leftOp) := sorry

/-- Companion bridge for Lemma 8.6.2: for a set-valued presheaf, the source-facing
`IsStackInSets` statement immediately implies and is implied by the underlying stack-on-site
predicate on the same category-of-elements projection. -/
theorem presheaf_isSheaf_iff_categoryOfElements_isStackOnSite
    (J : GrothendieckTopology C) (F : Cᵒᵖ ⥤ Type w) :
    Presheaf.IsSheaf J F ↔ IsStackOnSite J ((π F).leftOp) := by
  constructor
  · intro h
    letI : IsStackInSets J ((π F).leftOp) :=
      (presheaf_isSheaf_iff_categoryOfElements_isStackInSets J F).1 h
    exact inferInstance
  · intro h
    letI : IsStackOnSite J ((π F).leftOp) := h
    letI : IsStackInSets J ((π F).leftOp) := inferInstance
    exact (presheaf_isSheaf_iff_categoryOfElements_isStackInSets J F).2 inferInstance

end CategoryTheory
