import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap21.Lemma_21_39_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

namespace CategoryTheory.ModulesOnCategory

/- Domain-style sampling for Lemma 21.39.10:
- primary domain: tensor compatibility of the category-over-a-point derived lower shriek for
  `B`-module-valued presheaves, with the Chapter 21 modules-on-a-category statement as the
  specialization `C₁ = C₂ = C`;
- sampled owner declarations:
  `CategoryTheory.categoryOverPointDerivedColimit_tensorProjectionInverseImages_isomorphic`,
  `CategoryTheory.categoryOverPointDerivedColimit`,
  `Functor.presheafInverseImage`,
  `Functor.mapDerivedCategory`;
- best owner abstraction:
  `source-facing`: the modules-on-category tensor compatibility statement from the Stacks text;
  `core/canonical`: the owner theorem
    `CategoryTheory.categoryOverPointDerivedColimit_tensorProjectionInverseImages_isomorphic`;
  `bridge/view`: the chaotic-topology constant-sheaf presentation of `B`-module sheaves as
    `B`-valued presheaves, so this file should stay recall-only instead of keeping a second local
    wrapper;
- primitive data: the categories `C` and `C × C`, the lower-shriek owner
  `categoryOverPointDerivedColimit`, the projection inverse-image owner
  `Functor.presheafInverseImage`, and the derived objects on the relevant presheaf categories;
- derived API here: direct reuse of the upstream tensor-compatibility owner theorem rather than a
  parallel modules-on-category shell.
-/

/- Lemma 21.39.10: the constant `B`-module statement on a category with the chaotic topology is
just the specialization `C₁ = C₂ = C` of the canonical owner theorem
`CategoryTheory.categoryOverPointDerivedColimit_tensorProjectionInverseImages_isomorphic` from
Lemma `21.39.9`. This file therefore remains recall-only instead of introducing a second local
tensor-comparison declaration. -/
recall CategoryTheory.categoryOverPointDerivedColimit_tensorProjectionInverseImages_isomorphic

end CategoryTheory.ModulesOnCategory
