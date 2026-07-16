import Mathlib
import stacks_proof.stacks_project.Chap12.Definition_12_27_5

universe w v u

namespace CategoryTheory

noncomputable section

/- Domain-style sampling for Theorem 19.11.7:
- primary domain: functorial injective embeddings in Grothendieck abelian categories;
- sampled owner declarations:
  `HasFunctorialInjectiveEmbeddings`,
  `EnoughInjectives`,
  `IsGrothendieckAbelian`,
  `hasFunctorialInjectiveEmbeddings_of_isGrothendieckAbelian`;
- best owner abstraction: this item is a `bridge/view` recall of the Chapter 12 owner-level bridge
  from a Grothendieck abelian category to `HasFunctorialInjectiveEmbeddings C`;
- primitive data: an abelian category equipped with `IsGrothendieckAbelian C`;
- derived API: the canonical Chapter 12 declaration
  `hasFunctorialInjectiveEmbeddings_of_isGrothendieckAbelian`.

Source/core/bridge triage:
- `source-facing`: Theorem 19.11.7, asserting functorial injective embeddings for a Grothendieck
  abelian category;
- `core/canonical`: the project owner `HasFunctorialInjectiveEmbeddings C`;
- `bridge/view`: the canonical declaration
  `hasFunctorialInjectiveEmbeddings_of_isGrothendieckAbelian`.

This item is a pure canonical recall: the exact bridge declaration already exists upstream in
Chapter 12, so this file should reuse that owner directly rather than introduce a parallel named
instance. -/

/- Theorem 19.11.7: every Grothendieck abelian category admits functorial injective embeddings. -/
recall hasFunctorialInjectiveEmbeddings_of_isGrothendieckAbelian

end

end CategoryTheory
