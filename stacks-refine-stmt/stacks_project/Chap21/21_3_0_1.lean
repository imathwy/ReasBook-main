import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap13.Lemma_13_20_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open DerivedCategory.TStructure

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

/- Domain sampling:
- primary domain: bounded-below derived categories and the functorial formula for bounded-below
  right derived functors;
- sampled canonical/project declarations:
  - `t.plus`
  - `boundedBelowDerivedCategory`
  - `mapBoundedBelowHomotopyToDerivedBelow`
  - `Functor.totalRightDerived`
- best owner abstraction: the Chapter 13 owner `boundedBelowDerivedCategory`, cut out by
  `t.plus`;
- primitive data: the owner property `t.plus` on `DerivedCategory 𝒜` and its full subcategory
  `D^+(𝒜)`;
- derived API: the source formula that, once a lift `j'` and target functor `F` are fixed, the
  bounded-below right derived functor is the composite `j' ⋙ F`.

Source/core/bridge triage:
- `source-facing`: the textbook formula `RF = F ∘ j'`;
- `core/canonical`: `t.plus` and `boundedBelowDerivedCategory`;
- `bridge/view`: the direct identification of the source formula with the canonical composite
  `j' ⋙ F`, where `RF` itself is represented by the bounded-below specialization of
  `Functor.totalRightDerived`.

This item adds no new owner-level mathematics, so the correct refinement is direct canonical
recall/use rather than parallel local definitions. -/

section

variable {𝒪 : Type u₁} [Category.{v₁} 𝒪] [Abelian 𝒪] [HasDerivedCategory.{w} 𝒪]

/- Owner recall: the bounded-below property on `D(\mathcal O)` is the canonical `t`-structure
owner `t.plus`. -/
#check (t.plus : ObjectProperty (DerivedCategory 𝒪))

/- Owner recall: `D^+(\mathcal O)` is the canonical full subcategory cut out by that owner. -/
#check (boundedBelowDerivedCategory 𝒪 : Type _)

end

section

variable {𝒪 : Type u₁} {𝒥 : Type u₂} {ℬ : Type u₃}
  [Category.{v₁} 𝒪] [Category.{v₂} 𝒥] [Category.{v₃} ℬ]
  [Abelian 𝒪] [Abelian ℬ]
  [HasDerivedCategory.{w} 𝒪] [HasDerivedCategory.{w} ℬ]
variable (j' : boundedBelowDerivedCategory 𝒪 ⥤ 𝒥)
variable (F : 𝒥 ⥤ boundedBelowDerivedCategory ℬ)

/- 21.3.0.1: once a lift `j' : D^+(\mathcal O) ⥤ 𝒥` and a functor
`F : 𝒥 ⥤ D^+(\mathcal B)` are fixed, the source formula `RF = F ∘ j'` is exactly the canonical
composite `j' ⋙ F`; no extra wrapper declaration is mathematically needed. -/
#check (show boundedBelowDerivedCategory 𝒪 ⥤ boundedBelowDerivedCategory ℬ from j' ⋙ F)

end

end CategoryTheory
