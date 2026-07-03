import Mathlib
import StacksProject_2024.Chap12.Definition_12_27_5

universe w v u

namespace CategoryTheory

noncomputable section

/- Domain-style sampling for Theorem 19.11.7:
- primary domain: functorial injective embeddings in Grothendieck abelian categories;
- sampled owner declarations:
  `EnoughInjectives`,
  `IsGrothendieckAbelian.enoughInjectives`,
  `HasFunctorialInjectiveEmbeddings`,
  `hasFunctorialInjectiveEmbeddings_of_enoughInjectives`;
- best owner abstraction: this item is a `bridge/view` specialization from the Grothendieck owner
  hypothesis to the Chapter 12 owner `HasFunctorialInjectiveEmbeddings C`;
- primitive data: the canonical mathlib instance `EnoughInjectives C` for a Grothendieck abelian
  category;
- derived API: the Chapter 12 bridge `hasFunctorialInjectiveEmbeddings_of_enoughInjectives`.

Source/core/bridge triage:
- `source-facing`: Theorem 19.11.7, asserting functorial injective embeddings for a Grothendieck
  abelian category;
- `core/canonical`: mathlib's `EnoughInjectives C` instance for Grothendieck abelian categories and
  the project owner `HasFunctorialInjectiveEmbeddings C`;
- `bridge/view`: the specialization from the former to the latter. -/

/-- Theorem 19.11.7: every Grothendieck abelian category admits functorial injective embeddings. -/
noncomputable instance grothendieckAbelian_hasFunctorialInjectiveEmbeddings
    (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C] :
    HasFunctorialInjectiveEmbeddings C := by
  exact hasFunctorialInjectiveEmbeddings_of_isGrothendieckAbelian

end

end CategoryTheory
