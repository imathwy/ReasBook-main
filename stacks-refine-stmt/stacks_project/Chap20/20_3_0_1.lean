import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap13.Lemma_13_20_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory.TStructure

noncomputable section

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

/- Domain sampling:
- Primary domain: bounded-below derived categories and bounded-below right derived functors.
- Core/canonical declarations inspected:
  - `t.plus`
  - `boundedBelowDerivedCategory`
  - `mapBoundedBelowHomotopyToDerivedBelow`
  - `Functor.totalRightDerived`
- Owner abstraction: `boundedBelowDerivedCategory`, cut out by
  `t.plus`; for the functorial construction, the owner is the bounded-below specialization of
  `Functor.totalRightDerived`.
- Layer triage:
  - `source-facing`: eventual vanishing of homology in sufficiently low degrees and the textbook
    formula `RF = F ∘ j'`;
  - `core/canonical`: `t.plus`, `boundedBelowDerivedCategory`, and
    `Functor.totalRightDerived`;
  - `bridge/view`: the thin unpacking theorem below from `D^+(X)` to the low-degree vanishing
    statement.
- Primitive vs. derived:
  - primitive data: the canonical bounded-below owner `t.plus` and its full subcategory;
  - derived API: the source-wording vanishing theorem for objects of `D^+(X)`.
-/

section

variable {X : Type u₁} [Category.{v₁} X] [Abelian X] [HasDerivedCategory.{w} X]

/- Owner recall: the bounded-below property on `D(X)` is the canonical `t`-structure owner
`t.plus`. -/
#check (t.plus : ObjectProperty (DerivedCategory X))

/- Owner recall: `D^+(X)` is the canonical full subcategory cut out by that owner property. -/
#check (boundedBelowDerivedCategory X : Type _)

/- Bridge recall: Chapter 13 already exposes the eventual low-degree vanishing specification of
the bounded-below owner. -/
recall derivedCategory_t_plus_iff
    (K : DerivedCategory X) :
    (t.plus : ObjectProperty (DerivedCategory X)) K ↔
      ∃ n : ℤ, ∀ i : ℤ, i < n →
        IsZero ((DerivedCategory.homologyFunctor X i).obj K)

/-- Every object of `boundedBelowDerivedCategory X` has vanishing homology in sufficiently low
degrees. -/
theorem boundedBelowDerivedCategory_isBoundedBelow
    (K : boundedBelowDerivedCategory X) :
    ∃ n : ℤ, ∀ i : ℤ, i < n →
      IsZero ((DerivedCategory.homologyFunctor X i).obj K.obj) := by
  exact (derivedCategory_t_plus_iff K.obj).1 K.property

end

section

variable {X : Type u₁} {𝒥 : Type u₂} {ℬ : Type u₃}
  [Category.{v₁} X] [Category.{v₂} 𝒥] [Category.{v₃} ℬ]
  [Abelian X] [Abelian ℬ]
  [HasDerivedCategory.{w} X] [HasDerivedCategory.{w} ℬ]
variable (j' : boundedBelowDerivedCategory X ⥤ 𝒥)
variable (F : 𝒥 ⥤ boundedBelowDerivedCategory ℬ)

/- 20.3.0.1, functorial formula: once a lift `j' : D^+(X) ⥤ 𝒥` and a functor
`F : 𝒥 ⥤ D^+(\mathcal B)` are fixed, the source formula `RF = F ∘ j'` is the canonical composite
`j' ⋙ F`; no extra wrapper is needed. -/
#check (show boundedBelowDerivedCategory X ⥤ boundedBelowDerivedCategory ℬ from j' ⋙ F)

end

end CategoryTheory
