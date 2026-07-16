import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap21.Lemma_21_33_1_assoc

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry.RingedSpace

section

/- Domain-style sampling for Lemma 20.31.5:
- primary domain: associativity of the relative cup product in derived categories of module
  sheaves;
- sampled owner declarations:
  `CategoryTheory.relativeDerivedCupProduct`,
  `CategoryTheory.relativeDerivedCupProduct_associative_commSq`,
  `RingedSite.Hom.modulePullbackDerived_pushforward_adjunction`;
- best owner abstraction:
  `source-facing`: the associativity statement for the relative cup product of Remark 20.28.7;
  `core/canonical`: `CategoryTheory.relativeDerivedCupProduct_associative_commSq`;
  `bridge/view`: this Chapter 20 item is recall-only, since the source-facing associativity square
    is exactly the generic owner theorem specialized to derived categories of
    `𝒪_X`-modules on ringed spaces.

Primitive data live in the owner theorem: the morphism, the adjunction `Lf^* ⊣ Rf_*`, the
pullback-tensor comparison, and the source/target tensor associators. The cup product and its
associativity square are derived API from that owner, so this file should not keep a parallel
ringed-space theorem with the same interface. -/

/- Lemma 20.31.5 is exactly the generic owner theorem
`CategoryTheory.relativeDerivedCupProduct_associative_commSq`, viewed on derived categories of
`𝒪_X`-modules on ringed spaces. -/
recall CategoryTheory.relativeDerivedCupProduct_associative_commSq

end

end AlgebraicGeometry.RingedSpace
