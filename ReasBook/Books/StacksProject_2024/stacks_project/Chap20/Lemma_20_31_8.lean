import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap20.RingedSpaceModuleHasDerivedCategory
import StacksProject_2024.stacks_project.Chap21.Lemma_21_33_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

namespace AlgebraicGeometry.RingedSpace

/-
Domain-style sampling for Lemma 20.31.8:
- primary domain: relative derived cup products and derived base-change maps in a commutative
  square of derived categories;
- sampled owner declarations:
  `CategoryTheory.CommSq`,
  `CategoryTheory.relativeDerivedCupProduct`,
  `CategoryTheory.IsDerivedBaseChangeMap`,
  `CategoryTheory.relativeDerivedCupProduct_baseChange_commSq`;
- source/core/bridge triage:
  `source-facing`: the ringed-space specialization of the base-change compatibility square;
  `core/canonical`: the categorical owners above;
  `bridge/view`: specialization from the generic categorical `CommSq` theorem to `ModuleDerived`
    for ringed spaces.

Primitive data are the four functors, the two adjunctions, the commutativity isomorphism, and the
four pullback-tensor comparison isomorphisms. The cup product and base-change-map predicates are
derived API from the categorical owner layer, so this file should reuse those owners directly
instead of duplicating them locally.
-/

/- Lemma 20.31.8 is exactly the categorical square-form owner theorem
`CategoryTheory.relativeDerivedCupProduct_baseChange_commSq`, specialized to derived categories
of `𝒪_X`-modules on ringed spaces. -/
recall CategoryTheory.relativeDerivedCupProduct_baseChange_commSq

end AlgebraicGeometry.RingedSpace
