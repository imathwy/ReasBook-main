import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap21.Lemma_21_33_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

namespace RingedSite.Hom

/- Domain-style sampling for Lemma 21.33.3:
- primary domain: braided commutativity of the relative derived cup product;
- sampled owner declarations:
  `CategoryTheory.relativeDerivedCupProduct`,
  `CategoryTheory.relativeDerivedCupProduct_commutative_commSq`,
  `CategoryTheory.CommSq`;
- best owner abstraction:
  `source-facing`: the ringed-site commutativity statement for the relative cup product of
    Remark 21.19.7;
  `core/canonical`: `CategoryTheory.relativeDerivedCupProduct_commutative_commSq`;
  `bridge/view`: none beyond specialization language, so this file should remain recall-only.
- primitive data: the adjunction-level tensor comparison and its braiding compatibility already
  built into the owner theorem;
- derived API: direct reuse of the categorical owner, rather than a parallel ringed-site wrapper.

Source/core/bridge triage:
- `source-facing`: the ringed-site commutativity statement;
- `core/canonical`: `CategoryTheory.relativeDerivedCupProduct_commutative_commSq`;
- `bridge/view`: recall-only specialization to the Chapter 21 ringed-site setting. -/

/- Lemma 21.33.3: for the ringed-site derived pullback/pushforward adjunction
`L(f)^* ⊣ R(f)_*`, the relative cup product of Remark 21.19.7 is compatible with the braidings on
source and target. This is exactly the canonical theorem
`CategoryTheory.relativeDerivedCupProduct_commutative_commSq`, specialized to the Chapter 21
ringed-site derived setting. -/
recall CategoryTheory.relativeDerivedCupProduct_commutative_commSq

end RingedSite.Hom
