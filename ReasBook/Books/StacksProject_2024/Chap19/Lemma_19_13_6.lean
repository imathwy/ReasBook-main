import Mathlib
import StacksProject_2024.Chap13.Definition_13_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe w u₁ u₂ v₁ v₂

namespace CategoryTheory

section

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Abelian A]
  [Category.{v₂} B] [Abelian B]

/-- The standard chosen derived categories used for this item. -/
local instance additiveFunctorDerivedSource_hasDerivedCategory :
    HasDerivedCategory.{max u₁ v₁} A :=
  HasDerivedCategory.standard A

/-- The standard chosen derived categories used for this item. -/
local instance additiveFunctorDerivedTarget_hasDerivedCategory :
    HasDerivedCategory.{max u₂ v₂} B :=
  HasDerivedCategory.standard B

-- Proof sketch: choose the functorial K-injective resolution on `A` provided by the
-- Grothendieck hypothesis, and use that every K-injective complex computes the right derived
-- functor of `F.mapHomologicalComplex (ComplexShape.up ℤ)` after localization to `D(B)`.
/-- The cochain-level functor induced by an additive functor out of a Grothendieck abelian
category admits a total right derived functor. -/
theorem mapHomologicalComplexQ_hasRightDerivedFunctor
    (F : A ⥤ B) [F.Additive] [IsGrothendieckAbelian.{w} A] :
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) := sorry

attribute [local instance] mapHomologicalComplexQ_hasRightDerivedFunctor

/-- The total right derived functor `RF : D(A) ⥤ D(B)` attached to an additive functor
`F : A ⥤ B`. -/
noncomputable abbrev additiveFunctorTotalRightDerived
    (F : A ⥤ B) [F.Additive] [IsGrothendieckAbelian.{w} A] :
    DerivedCategory A ⥤ DerivedCategory B :=
  (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).totalRightDerived
    DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))

-- Proof sketch: choose a Milnor triangle for `K` built from a product of K-injective complexes
-- representing the stages of `Ksys`. The right derived functor is computed on those
-- K-injective representatives by applying `F`, and the hypothesis that `F` preserves countable
-- products identifies the image of the Milnor difference map with the Milnor difference map of
-- the stagewise image system. Exact countable products in `B` then identify the termwise product
-- complexes with products in `D(B)`, so the image triangle exhibits `RF(K)` as the derived limit
-- of `(RF(K_n))`.
/-- Lemma 19.13.6: let `F : A ⥤ B` be an additive functor of abelian categories. Assume `A` is a
Grothendieck abelian category, `B` has exact countable products, and `F` commutes with countable
products. Then the total right derived functor `RF : D(A) ⥤ D(B)` carries a derived limit of a
sequential inverse system in `D(A)` to a derived limit of the stagewise image system in `D(B)`. -/
theorem additiveFunctor_totalRightDerived_preservesDerivedLimit
    (F : A ⥤ B) [F.Additive] [IsGrothendieckAbelian.{w} A]
    [HasCountableProducts B] [CountableAB4Star B]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    {Ksys : ℕᵒᵖ ⥤ DerivedCategory A} {K : DerivedCategory A}
    (hK : IsDerivedLimit Ksys K) :
    IsDerivedLimit
      (Ksys ⋙ additiveFunctorTotalRightDerived F)
      ((additiveFunctorTotalRightDerived F).obj K) := sorry

end

end CategoryTheory
