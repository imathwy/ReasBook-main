import Mathlib
import stacks_project.Chap04.Lemma_4_39_5
import stacks_project.Chap08.Lemma_8_4_4
import stacks_project.Chap08.Lemma_8_4_2
import stacks_project.Chap08.Definition_8_6_1
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

-- Proof sketch: first rewrite `IsStackInSetoids` as the underlying owner `IsStackOnSite`. Then
-- compare `p` coverwise with the associated fibred-in-sets model supplied by Lemma `4.39.5`.
-- Finally identify that associated model with the category of elements of the iso-class
-- presheaf and apply Lemma `8.6.2` in its `IsStackOnSite` form.
/-- Helper for Lemma 8.6.3: for a fibred category in setoids, the source-facing owner
`IsStackInSetoids` is equivalent to the underlying owner `IsStackOnSite`. -/
private lemma stack_in_setoids_iff_stack_on_site
    (J : GrothendieckTopology C) (p : S ⥤ C) [IsFibredInSetoids p] :
    IsStackInSetoids J p ↔ IsStackOnSite J p := by
  constructor
  · intro h
    -- Forgetting from stacks in setoids only drops the explicit source-facing fiber condition.
    let _ : IsStackInSetoids J p := h
    exact inferInstance
  · intro h
    -- Reassemble the source-facing owner from the setoid-fiber hypothesis and `h`.
    let _ : IsStackOnSite J p := h
    exact inferInstance

/-- Helper for Lemma 8.6.3: the canonical associated fibred-in-sets replacement carries the same
stack-on-site condition as the original fibred category in setoids. -/
private lemma associated_sets_model_stack_on_site_iff
    (J : GrothendieckTopology C) (p : S ⥤ C) [IsFibredInSetoids p] :
    IsStackOnSite J p ↔
      IsStackOnSite J (FibredInSetoidsOver.ofFunctor p).associatedFibredInSets.p := by
  let X := FibredInSetoidsOver.ofFunctor p
  let F : BasedCategory.ofFunctor p ⥤ᵇ
      BasedCategory.ofFunctor X.associatedFibredInSets.p :=
    show BasedCategory.ofFunctor p ⥤ᵇ
        BasedCategory.ofFunctor X.associatedFibredInSets.p from
      FibredInSetoidsOver.toBasedFunctor X.toFibredInSets
  have hF : F.IsEquivalenceOverBase := by
    -- The canonical comparison is already proved to be an equivalence over the base.
    simpa [F] using (FibredInSetoidsOver.toFibredInSets_isEquivalenceOverBase X)
  -- Route correction: transport the owner `IsStackOnSite` across the canonical equivalence over
  -- the base instead of rebuilding fixed-cover descent transport locally.
  -- Apply the owner-level equivalence theorem from Lemma `8.4.4` to `X.toFibredInSets`.
  simpa [X] using
    (isStackOnSite_iff_of_equivalence_over_base J
      p X.associatedFibredInSets.p
      F hF)

/-- Helper for Lemma 8.6.3: the associated fibred-in-sets model of a fibred category in setoids is
the category of elements of its iso-class presheaf, so its stack-on-site condition is exactly the
sheaf condition on that presheaf. -/
private lemma associated_sets_model_stack_on_site_iff_iso_class_sheaf
    (J : GrothendieckTopology C) (p : S ⥤ C) [IsFibredInSetoids p] :
    IsStackOnSite J (FibredInSetoidsOver.ofFunctor p).associatedFibredInSets.p ↔
      Presheaf.IsSheaf J p.fiberIsoClassPresheaf := by
  let X := FibredInSetoidsOver.ofFunctor p
  let Y := X.associatedFibredInSets
  -- Identify the associated sets model with the category of elements of the iso-class presheaf.
  simpa [X, Y] using
    (presheaf_isSheaf_iff_categoryOfElements_isStackOnSite J p.fiberIsoClassPresheaf).symm

/-- Lemma 8.6.3: a category fibred in setoids over a site `(C, J)` admits a stack structure if
and only if the presheaf sending `U` to the set of isomorphism classes of objects of the fiber
over `U` is a sheaf. -/
theorem isStackInSetoids_iff_isoClassPresheaf_isSheaf
    (J : GrothendieckTopology C) (p : S ⥤ C) [IsFibredInSetoids p] :
    IsStackInSetoids J p ↔ Presheaf.IsSheaf J p.fiberIsoClassPresheaf := by
  -- First strip the source-facing owner to the underlying stack-on-site condition.
  have hSetoids :
      IsStackInSetoids J p ↔ IsStackOnSite J p :=
    stack_in_setoids_iff_stack_on_site (J := J) (p := p)
  have hTransport :
      IsStackOnSite J p ↔
        IsStackOnSite J (FibredInSetoidsOver.ofFunctor p).associatedFibredInSets.p :=
    associated_sets_model_stack_on_site_iff (J := J) (p := p)
  have hSheaf :
      IsStackOnSite J (FibredInSetoidsOver.ofFunctor p).associatedFibredInSets.p ↔
        Presheaf.IsSheaf J p.fiberIsoClassPresheaf :=
    associated_sets_model_stack_on_site_iff_iso_class_sheaf (J := J) (p := p)
  -- Compose the source-faithful route: setoids -> stack-on-site -> associated sets -> sheaf.
  exact hSetoids.trans (hTransport.trans hSheaf)

end CategoryTheory
