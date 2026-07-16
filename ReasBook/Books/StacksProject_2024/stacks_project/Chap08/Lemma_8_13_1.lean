import Mathlib
import StacksProject_2024.stacks_project.Chap04.Example_4_3_4
import StacksProject_2024.stacks_project.Chap04.Example_4_38_7
import StacksProject_2024.stacks_project.Chap08.Lemma_8_4_4
import StacksProject_2024.stacks_project.Chap08.Lemma_8_6_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open scoped RepresentablePresheaf

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Lemma 8.13.1:
- primary domain: stacks on a site, specialized to representable presheaves and the slice
  projection `Over.forget U`.
- inspected owner-level declarations:
  `presheaf_isSheaf_iff_categoryOfElements_isStackOnSite`,
  `representableElementsOpToOver_isEquivalenceOverBase`,
  `IsStackOnSite`,
  `Over.forget`.
- best owner abstraction: the core owner is
  `IsStackOnSite J ((CategoryOfElements.π F).leftOp)` for a presheaf `F`; the slice projection
  `Over.forget U` is reached from that owner by the canonical over-base equivalence for the
  representable presheaf `h[U]`.
- primitive data: the object `U : C` and the representable presheaf `h[U]`.
- derived API: the slice-category reformulation obtained by transporting the stack condition
  across `representableElementsOpToOver_isEquivalenceOverBase U`.

Source/core/bridge triage:
- `source-facing`: `over_forget_isStackOnSite_iff_representable_isSheaf`.
- `core/canonical`: `presheaf_isSheaf_iff_categoryOfElements_isStackOnSite`.
- `bridge/view`: `representableElementsOpToOver_isEquivalenceOverBase U`. -/

-- Proof sketch: the canonical owner theorem `presheaf_isSheaf_iff_categoryOfElements_isStackOnSite`
-- identifies the sheaf condition on a presheaf with the stack condition on its category of
-- elements. For the representable presheaf `h[U]`, Example `4.38.7` gives the canonical
-- over-base equivalence between that category of elements and the slice projection `Over.forget U`,
-- so transport the stack condition across that equivalence.
/-- Lemma 8.13.1: for an object `U` of a site `(C, J)`, the localization functor
`j_U : C/U ⥤ C`, written in Lean as `Over.forget U`, is a stack over `(C, J)` if and only if the
representable presheaf `h_U`, written canonically as `h[U]`, is a sheaf. This is the canonical
chapter-facing form of the source statement. -/
theorem over_forget_isStackOnSite_iff_representable_isSheaf
    (J : GrothendieckTopology C) (U : C) :
    IsStackOnSite J (Over.forget U) ↔ Presheaf.IsSheaf J h[U] := by
  let p := (CategoryOfElements.π h[U]).leftOp
  exact
    (isStackOnSite_iff_of_equivalence_over_base J
        p (Over.forget U)
        (representableElementsOpToOver U)
        (representableElementsOpToOver_isEquivalenceOverBase U)).symm.trans
      (presheaf_isSheaf_iff_categoryOfElements_isStackOnSite J h[U]).symm

end CategoryTheory
