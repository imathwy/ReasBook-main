import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap13.Definition_13_11_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped CategoryTheory

noncomputable section

universe v₁ v₂ u₁ u₂

/- Domain-style sampling for 20.3.0.2:
- primary domain: derived categories and source-facing higher right derived functors;
- sampled owner declarations:
  `DerivedCategory.homologyFunctor`,
  `Functor.rightDerived`,
  `DerivedCategory.singleFunctor`;
- best owner abstraction: the canonical homology functor on the target derived category,
  postcomposed with the chosen derived functor;
- primitive data: a chosen functor `RF : 𝒜 ⥤ DerivedCategory ℬ`;
- derived API: the composite `RF ⋙ DerivedCategory.homologyFunctor ℬ i`.

Source/core/bridge triage:
- `source-facing`: the textbook formula `R^i F = H^i ∘ RF`;
- `core/canonical`: `DerivedCategory.homologyFunctor`;
- `bridge/view`: the specialization obtained by postcomposing `RF` with `H^i`.

This item is therefore a source-facing bridge built directly from the canonical owner, so the file
should expose the composite itself rather than a parallel local abbreviation with the same
interface. -/

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian ℬ] [HasDerivedCategory ℬ]
variable (RF : 𝒜 ⥤ DerivedCategory ℬ) (i : ℤ)

/- Canonical owner recall: the cohomology functor on `D(ℬ)` is `DerivedCategory.homologyFunctor`,
written in the source-facing chapter notation as `H^i`. -/
recall DerivedCategory.homologyFunctor

/- 20.3.0.2: for a chosen right derived functor `RF : 𝒜 ⥤ D(ℬ)`, the `i`-th right derived
functor is the source-facing composite `H^i ∘ RF`, using the Chapter 13 cohomology notation
for the canonical owner `DerivedCategory.homologyFunctor`. -/
#check (RF ⋙ H^i : 𝒜 ⥤ ℬ)

end
