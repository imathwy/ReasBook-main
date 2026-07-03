import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap13.Lemma_13_10_6
import stacks_project.Chap13.Lemma_13_26_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoryTheory

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

/- Domain-style sampling for 13.26.13.5:
- primary domain: bounded-below homotopy lifts of additive functors defined on the filtered-
  injective full subcategory of finite filtered objects;
- inspected owner declarations:
  `filteredInjectiveSubcategory`,
  `exists_filteredInjectiveExtension`,
  `mapBoundedBelowHomotopyCategory`;
- best owner abstraction: the source category `𝓘^f(𝒜)` is already owned upstream by
  `filteredInjectiveSubcategory 𝒜`, and once the source-facing extension data
  `T_ext : 𝓘^f(𝒜) ⥤+ Fil^f(ℬ)` from `13.26.13.4` is fixed, the induced `K^+` functor is
  canonically the owner lift `mapBoundedBelowHomotopyCategory T_ext.obj`;
- primitive data: the additive filtered extension
  `T_ext : filteredInjectiveSubcategory 𝒜 ⥤+ Fil^f(ℬ)`;
- derived API: the bounded-below homotopy lift
  `mapBoundedBelowHomotopyCategory T_ext.obj`.

Source/core/bridge triage:
- `source-facing`: the additive filtered extension `T_ext` from `13.26.13.4`;
- `core/canonical`: `filteredInjectiveSubcategory` and
  `mapBoundedBelowHomotopyCategory`;
- `bridge/view`: the specialized `K^+` functor
  `mapBoundedBelowHomotopyCategory T_ext.obj :
    K⁺(𝓘^f(𝒜)) ⥤ K⁺(Fil^f(ℬ))`.

This item is therefore a bridge-only canonical recall: it should expose the owner lift directly,
without introducing a second local name for the induced bounded-below homotopy functor. -/

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [EnoughInjectives 𝒜]
  [Preadditive ℬ] [HasZeroObject ℬ]
  [HasZeroObject (𝓘^f(𝒜))]
  [HasZeroObject (Fil^f(ℬ))]
  [HasBinaryBiproducts (𝓘^f(𝒜))]
  [HasBinaryBiproducts (Fil^f(ℬ))]

variable (T_ext : 𝓘^f(𝒜) ⥤+ Fil^f(ℬ))

/- Canonical owner recall: once the additive filtered extension `T_ext` on `𝓘^f(𝒜)` is fixed,
the induced bounded-below homotopy functor is the existing owner
`mapBoundedBelowHomotopyCategory`, specialized to the underlying functor `T_ext.obj`. -/
recall mapBoundedBelowHomotopyCategory

/- 13.26.13.5: for an additive functor `T_ext : 𝓘^f(𝒜) ⥤+ Fil^f(ℬ)`, the induced functor
`K^+(𝓘^f(𝒜)) ⥤ K^+(Fil^f(ℬ))` is exactly the canonical bounded-below homotopy lift of the
underlying functor `T_ext.obj`. -/
#check
  (mapBoundedBelowHomotopyCategory T_ext.obj :
    K⁺(𝓘^f(𝒜)) ⥤ K⁺(Fil^f(ℬ)))

end

end CategoryTheory
