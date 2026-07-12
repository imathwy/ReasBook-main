import Mathlib.Tactic.Recall
import StacksProject_2024.Chap21.Lemma_21_33_1_assoc

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

namespace RingedSite.Hom

/- Domain-style sampling for Lemma 21.33.2:
- primary domain: associativity of the relative derived cup product for `L(f)^* ⊣ R(f)_*` on
  derived categories of module sheaves over ringed sites;
- sampled owner declarations:
  `CategoryTheory.relativeDerivedCupProduct`,
  `CategoryTheory.relativeDerivedCupProduct_associative_commSq`,
  `RingedSite.Hom.modulePullbackDerived_pushforward_adjunction`,
  `CategoryTheory.CommSq`;
- best owner abstraction:
  `source-facing`: the ringed-site associativity square for the relative cup product of
    Remark 21.19.7;
  `core/canonical`: `CategoryTheory.relativeDerivedCupProduct_associative_commSq`;
  `bridge/view`: the specialization of that owner theorem to the derived pullback/pushforward
    adjunction on module sheaves over ringed sites.
- primitive data: the morphism `f`, the chosen adjunction `L(f)^* ⊣ R(f)_*`, the pullback-tensor
  comparison, and the source/target tensor associators;
- derived API: direct reuse of the generic owner theorem rather than a parallel ringed-site
  specialization theorem.

Source/core/bridge triage:
- `source-facing`: the ringed-site associativity statement;
- `core/canonical`: `CategoryTheory.relativeDerivedCupProduct_associative_commSq`;
- `bridge/view`: specialization to `ModuleDerived X`, `ModuleDerived Y`, and the chosen tensor
  functors. This file is recall-only rather than a second owner of the same associativity square.
-/

/- Lemma 21.33.2: for the ringed-site derived pullback/pushforward adjunction
`L(f)^* ⊣ R(f)_*`, the relative cup product of Remark 21.19.7 is associative. This is exactly the
canonical theorem `CategoryTheory.relativeDerivedCupProduct_associative_commSq`, specialized to
`ModuleDerived X`, `ModuleDerived Y`, the chosen tensor functors, the pullback-tensor comparison,
and the source/target tensor associators. -/
recall CategoryTheory.relativeDerivedCupProduct_associative_commSq

end RingedSite.Hom
