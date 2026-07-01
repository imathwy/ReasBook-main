import Mathlib
import stacks_project.Chap04.Lemma_4_39_5
import stacks_project.Chap08.Definition_8_6_1
import stacks_project.Chap08.Lemma_8_4_4
import stacks_project.Chap08.Lemma_8_6_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

variable {C : Type u} {S : Type (max u v)} [Category.{v} C] [Category.{v} S]

/- Domain-style sampling for Lemma 8.6.3:
- primary domain: stack conditions on a site for categories fibred in setoids, compared with the
  canonical presheaf of fiberwise isomorphism classes;
- inspected owner-level declarations:
  `IsStackInSetoids`,
  `IsStackOnSite`,
  `Functor.fiberIsoClassPresheaf`,
  `FibredInSetoidsOver.ofFunctor`,
  `FibredInSetoidsOver.associatedFibredInSets`,
  `FibredInSetoidsOver.toFibredInSets`,
  `FibredInSetoidsOver.toFibredInSets_isEquivalenceOverBase`;
- best owner abstraction: the source-facing owner in this section is `IsStackInSetoids J p`; the
  underlying canonical owners are `IsStackOnSite J p` and the presheaf `fiberIsoClassPresheaf p`,
  while bundled `FibredInSetoidsOver` language is only a bridge view used internally;
- primitive data: a functor `p : S ⥤ C` with `[IsFibredInSetoids p]`;
- derived API: the comparison with `IsStackOnSite J p`, plus the bundled equivalence-over-base
  bridge through `FibredInSetoidsOver.ofFunctor p` and `X.associatedFibredInSets`.

Source/core/bridge triage:
- `source-facing`: `isStackInSetoids_iff_isoClassPresheaf_isSheaf`;
- `core/canonical`: `IsStackInSetoids`, `IsStackOnSite`, and `fiberIsoClassPresheaf`;
- `bridge/view`: any bundled reformulation using `FibredInSetoidsOver` or `FibredInSetsOver`. -/

-- Proof sketch: first use Lemma `8.6.2` at the source-facing `IsStackInSets` level for the
-- canonical fibred-in-sets replacement of `p.fiberIsoClassPresheaf`. Then forget down to the
-- underlying stack-on-site predicate and transport that predicate back across the canonical
-- equivalence-over-base from `p` to its fibred-in-sets model. Finally recover the source-facing
-- owner `IsStackInSetoids J p` from `[IsFibredInSetoids p]`.
/-- Lemma 8.6.3: a category fibred in setoids over a site `(C, J)` admits a stack structure if
and only if the presheaf sending `U` to the set of isomorphism classes of objects of the fiber
over `U` is a sheaf. -/
theorem isStackInSetoids_iff_isoClassPresheaf_isSheaf
    (J : GrothendieckTopology C) (p : S ⥤ C) [IsFibredInSetoids p] :
    IsStackInSetoids J p ↔ Presheaf.IsSheaf J p.fiberIsoClassPresheaf := by
  let X := FibredInSetoidsOver.ofFunctor p
  have hStackOnSite : IsStackOnSite J p ↔ Presheaf.IsSheaf J p.fiberIsoClassPresheaf := by
    let Y := X.associatedFibredInSets
    have hStackInSets : Presheaf.IsSheaf J p.fiberIsoClassPresheaf ↔ IsStackInSets J Y.p := by
      simpa [Y, X] using
        presheaf_isSheaf_iff_categoryOfElements_isStackInSets J p.fiberIsoClassPresheaf
    have hY : IsStackOnSite J Y.p ↔ Presheaf.IsSheaf J p.fiberIsoClassPresheaf := by
      constructor
      · intro h
        letI : IsStackOnSite J Y.p := h
        letI : IsStackInSets J Y.p := inferInstance
        exact hStackInSets.2 inferInstance
      · intro h
        letI : IsStackInSets J Y.p := hStackInSets.1 h
        exact inferInstance
    exact
      (isStackOnSite_iff_of_equivalence_over_base
        J p Y.p X.toFibredInSets X.toFibredInSets_isEquivalenceOverBase).trans hY
  constructor
  · intro h
    letI : IsStackInSetoids J p := h
    exact hStackOnSite.1 (show IsStackOnSite J p from inferInstance)
  · intro h
    letI : IsStackOnSite J p := hStackOnSite.2 h
    exact inferInstance

end CategoryTheory
