import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap21.Lemma_21_18_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

namespace SheafOfModules.RingedSite

/- Domain-style sampling for Lemma 21.18.8:
- primary domain: derived pullback/tensor comparison for sheaves of modules on ringed sites;
- sampled declarations:
  `leftDerivedPullback_tensor_existsComparison_commSq`,
  `CategoryTheory.CommSq`;
- owner abstraction:
  `source-facing`: the existence of the commutative square of Lemma `21.18.8`;
  `core/canonical`: `leftDerivedPullback_tensor_existsComparison_commSq`;
  `bridge/view`: the underived comparison square packaged inside
    `leftDerivedPullback_tensor_existsComparison_commSq`.
- primitive data: the site pullback on complexes, the functor-level derived tensor comparison
  isomorphism statement, its source/target counits, and an accompanying underived comparison;
- derived API: this file should reuse the owner theorem giving those witnesses directly rather than
  keep a parallel local wrapper. -/

/- Lemma 21.18.8 reuses the commutative-square owner
`leftDerivedPullback_tensor_existsComparison_commSq` from Lemma `21.18.4`. -/
recall leftDerivedPullback_tensor_existsComparison_commSq

end SheafOfModules.RingedSite
