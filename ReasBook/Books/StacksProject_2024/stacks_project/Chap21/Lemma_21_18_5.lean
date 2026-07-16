import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap21.Lemma_21_18_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

namespace SheafOfModules.RingedSite

/- Domain-style sampling for Lemma 21.18.5:
- primary domain: the same-site specialization of the derived pullback/tensor comparison for
  sheaves of modules on a commutative ringed site;
- sampled owner declarations:
  `leftDerivedPullback_tensorComparison`;
- best owner abstraction:
  `source-facing`: the same-site isomorphism statement
    `Lα^*(K ⊗^L L) ≅ Lα^* K ⊗^L Lα^* L`;
  `core/canonical`: `leftDerivedPullback_tensorComparison`;
  `bridge/view`: this file is recall-only, because Lemma `21.18.5` is exactly the identity-site
    specialization of Lemma `21.18.4`, not a second owner with extra API.
- primitive data: the structure-sheaf morphism `α` and the canonical comparison morphism supplied
  upstream by Lemma `21.18.4`;
- derived API: reuse the Chapter 21 owner directly instead of duplicating its same-site
  specialization with theorem-local variables or instance scaffolding. -/

/- Lemma 21.18.5: the same-site pullback/tensor comparison
`Lα^*(K ⊗^L L) ≅ Lα^* K ⊗^L Lα^* L`
is exactly the identity-site specialization of the Chapter 21 owner
`leftDerivedPullback_tensorComparison` from Lemma `21.18.4`. -/
recall leftDerivedPullback_tensorComparison

end SheafOfModules.RingedSite
