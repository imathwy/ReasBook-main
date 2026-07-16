import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap12.Definition_12_27_5
import StacksProject_2024.stacks_project.Chap13.Lemma_13_23_4

universe v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling:
- primary domain: bounded-below injective resolutions of cochain complexes, produced from
  functorial injective embeddings;
- sampled owner declarations:
  `HasFunctorialInjectiveEmbeddings`,
  `EnoughInjectives`,
  `CochainComplex.ResolutionFunctorOne`,
  `CategoryTheory.exists_resolutionFunctorOne`;
- best owner abstraction: `CategoryTheory.exists_resolutionFunctorOne` is the chapter owner
  theorem for the existence statement, with `CochainComplex.ResolutionFunctorOne 𝒜` as the
  underlying source-facing type and the Chapter 12 instance
  `HasFunctorialInjectiveEmbeddings 𝒜 → EnoughInjectives 𝒜` as the canonical bridge;
- primitive data: the chosen functorial injective embedding structure on `𝒜`;
- derived API: the induced `EnoughInjectives 𝒜` instance and the chapter-level existence theorem
  `CategoryTheory.exists_resolutionFunctorOne`; the later passage to
  `CategoryTheory.HomotopyResolutionFunctor 𝒜` is a downstream bridge.

Source/core/bridge triage:
- `source-facing`: Lemma 13.24.1, asserting that functorial injective embeddings suffice to
  construct a resolution functor 1 on bounded-below cochain complexes;
- `core/canonical`: `CategoryTheory.exists_resolutionFunctorOne`;
- `bridge/view`: the canonical instance `HasFunctorialInjectiveEmbeddings 𝒜 → EnoughInjectives 𝒜`.
-/

variable [HasFunctorialInjectiveEmbeddings 𝒜]

/- Lemma 13.24.1: via the Chapter 12 instance
`HasFunctorialInjectiveEmbeddings 𝒜 → EnoughInjectives 𝒜`, this is exactly the chapter owner
theorem `exists_resolutionFunctorOne`. -/
recall exists_resolutionFunctorOne

end CategoryTheory
