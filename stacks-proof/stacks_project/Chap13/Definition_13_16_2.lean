import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import stacks_project.Chap13.Definition_13_11_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open DerivedCategory.TStructure

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

/- Domain-style sampling for Definition 13.16.2:
- primary domain: bounded-below derived categories and right derived functors.
- inspected owner declarations:
  `boundedBelowDerivedCategory`,
  `ObjectProperty.ι`,
  `DerivedCategory.singleFunctor`,
  `DerivedCategory.homologyFunctor`.
- owner abstraction: the bounded-below owner `D⁺(-)`, with the degree-zero embedding
  `𝒜 ⥤ D⁺(𝒜)` obtained by lifting `DerivedCategory.singleFunctor 𝒜 0`, followed by the canonical
  inclusion `D⁺(𝒝) ⥤ D(𝒝)` and `DerivedCategory.homologyFunctor 𝒝 i`.
- primitive data: a chosen bounded-below right derived functor `RF : D⁺(𝒜) ⥤ D⁺(𝒝)`.
- derived API: the source-facing composite `A ↦ H^i((RF(A[0])) : D(𝒝))`.

Source/core/bridge triage:
- `source-facing`: the textbook functor `R^iF`;
- `core/canonical`: `boundedBelowDerivedCategory`, `DerivedCategory.singleFunctor`,
  `ObjectProperty.ι`, and `DerivedCategory.homologyFunctor`;
- `bridge/view`: the realization `R^iF(A) = H^i((RF(A[0])) : D(𝒝))`.

This item is a source-facing bridge built from the canonical derived-category owners, so the
file should expose only that named composite and not an unbounded surrogate owner. -/

section

variable {𝒜 : Type u₁} {𝒝 : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} 𝒝]
  [Abelian 𝒜] [Abelian 𝒝]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} 𝒝]

variable (RF : D⁺(𝒜) ⥤ D⁺(𝒝)) (i : ℤ)

/- Definition 13.16.2: once a chosen functor `RF` models the bounded-below right derived
functor of an additive functor `F : 𝒜 ⥤ 𝒝`, its `i`-th right derived functor is the canonical
composite sending `A` to `H^i((RF(A[0])) : D(\mathcal B))`. -/
#check
  (ObjectProperty.lift (t.plus : ObjectProperty (D(𝒜)))
      (DerivedCategory.singleFunctor 𝒜 0)
      (fun A ↦ by
        exact ⟨0, inferInstance⟩) ⋙
    RF ⋙
    ObjectProperty.ι (t.plus : ObjectProperty (D(𝒝))) ⋙
      DerivedCategory.homologyFunctor 𝒝 i)

end

end CategoryTheory
