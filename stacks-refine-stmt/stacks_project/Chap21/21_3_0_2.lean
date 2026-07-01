import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

/- Domain-style sampling for 21.3.0.2:
- primary domain: derived categories, homology functors, and source-facing formulas for higher
  right derived functors;
- inspected canonical/project declarations:
  `DerivedCategory.homologyFunctor`,
  `Functor.rightDerived`,
  `DerivedCategory.singleFunctor`;
- best owner abstraction: `DerivedCategory.homologyFunctor`;
- primitive data: only a chosen functor `RF : 𝒪 ⥤ DerivedCategory ℬ`;
- derived API: the source-facing composite `RF ⋙ DerivedCategory.homologyFunctor ℬ i`.

Source/core/bridge triage:
- `source-facing`: the textbook formula `R^i F = H^i ∘ RF` for a chosen realization `RF`;
- `core/canonical`: `DerivedCategory.homologyFunctor`;
- `bridge/view`: the specialization obtained by postcomposing `RF` with `H^i`.

This item adds no new owner-level data beyond the canonical homology functor, so the refined
surface should use that owner directly rather than keep a one-off local alias and a tautological
`_def` theorem. -/

section

variable {𝒪 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒪] [Category.{v₂} ℬ]
  [Abelian ℬ] [HasDerivedCategory ℬ]
  (RF : 𝒪 ⥤ DerivedCategory ℬ) (i : ℤ)

/- 21.3.0.2: for a chosen derived functor `RF : Mod(\mathcal O) ⥤ D(\mathcal B)`, the `i`-th
right derived functor is exactly the canonical composite `RF ⋙ H^i`. -/
#check (RF ⋙ DerivedCategory.homologyFunctor ℬ i)

end

end CategoryTheory
