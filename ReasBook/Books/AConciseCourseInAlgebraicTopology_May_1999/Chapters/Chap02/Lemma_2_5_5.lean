import Mathlib.CategoryTheory.Skeletal
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

open CategoryTheory

variable (C : Type u₁) [Category.{v₁} C]
variable (skC : Type u₂) [Category.{v₂} skC]

/- Lemma 2.5.5: if `J : sk C ⥤ C` exhibits `sk C` as a skeleton of `C`, then the functor `J`
is an equivalence of categories. -/
recall IsSkeletonOf.eqv (J : skC ⥤ C) (hJ : IsSkeletonOf C skC J) : J.IsEquivalence
