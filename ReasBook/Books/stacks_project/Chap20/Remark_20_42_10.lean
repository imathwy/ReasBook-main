import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-- The structure sheaf of a ringed space, viewed as a `RingCat`-valued sheaf. -/
/-- The category of sheaves of `\mathcal O_X`-modules on a ringed space. -/
/-- The unbounded derived category `D(\mathcal O_X)` of sheaves of `\mathcal O_X`-modules. -/
abbrev RingedSpaceDerived (X : RingedSpace.{u}) :=
  DerivedCategory (RingedSpace.Modules X)

section

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpaceDerived X)]
variable [BraidedCategory (RingedSpaceDerived X)]
variable [MonoidalClosed (RingedSpaceDerived X)]

/-- The evaluation morphism `R\mathcal H\!\mathit{om}(K, K') \otimes^{\mathbf L} K \to K'`,
written in the textbook's factor order. -/
noncomputable def ringedSpaceDerivedInternalHomEvaluation
    (K K' : RingedSpaceDerived X) :
    (ihom K).obj K' ⊗ K ⟶ K' :=
  (β_ ((ihom K).obj K') K).hom ≫ MonoidalClosed.uncurry (𝟙 ((ihom K).obj K'))

-- Proof sketch: unfold `ringedSpaceDerivedInternalHomEvaluation`; the morphism is defined by
-- first braiding `R\mathcal H\!\mathit{om}(K, K')` past `K`, and then applying the counit
-- `K \otimes^{\mathbf L} R\mathcal H\!\mathit{om}(K, K') \to K'` of the internal-Hom adjunction.
/-- The book-order evaluation morphism is the braiding followed by the closed-monoidal
evaluation map. -/
theorem ringedSpaceDerivedInternalHomEvaluation_eq
    (K K' : RingedSpaceDerived X) :
    ringedSpaceDerivedInternalHomEvaluation K K' =
      (β_ ((ihom K).obj K') K).hom ≫ MonoidalClosed.uncurry (𝟙 ((ihom K).obj K')) := sorry

/-- The uncurried morphism underlying the tensor-internal-Hom comparison on
`D(\mathcal O_X)`. -/
noncomputable def ringedSpaceDerivedTensorInternalHomComparisonTranspose
    (K K' M M' : RingedSpaceDerived X) :
    (((ihom K).obj K' ⊗ (ihom M).obj M') ⊗ (K ⊗ M)) ⟶ (K' ⊗ M') :=
  (α_ ((ihom K).obj K') ((ihom M).obj M') (K ⊗ M)).hom ≫
    (((ihom K).obj K') ◁ (α_ ((ihom M).obj M') K M).inv) ≫
    (((ihom K).obj K') ◁ (((β_ ((ihom M).obj M') K).hom) ▷ M)) ≫
    (((ihom K).obj K') ◁ (α_ K ((ihom M).obj M') M).hom) ≫
    (α_ ((ihom K).obj K') K (((ihom M).obj M') ⊗ M)).inv ≫
    ringedSpaceDerivedInternalHomEvaluation K K' ▷ (((ihom M).obj M') ⊗ M) ≫
    K' ◁ ringedSpaceDerivedInternalHomEvaluation M M'

-- Proof sketch: unfold
-- `ringedSpaceDerivedTensorInternalHomComparisonTranspose`; it first reassociates the four
-- factors, flips the middle two by the braiding, then evaluates
-- `R\mathcal H\!\mathit{om}(K, K') \otimes^{\mathbf L} K` and
-- `R\mathcal H\!\mathit{om}(M, M') \otimes^{\mathbf L} M` separately.
/-- The uncurried comparison morphism flips the middle two factors and then applies the two
evaluation maps. -/
theorem ringedSpaceDerivedTensorInternalHomComparisonTranspose_eq
    (K K' M M' : RingedSpaceDerived X) :
    ringedSpaceDerivedTensorInternalHomComparisonTranspose K K' M M' =
      (α_ ((ihom K).obj K') ((ihom M).obj M') (K ⊗ M)).hom ≫
        (((ihom K).obj K') ◁ (α_ ((ihom M).obj M') K M).inv) ≫
        (((ihom K).obj K') ◁ (((β_ ((ihom M).obj M') K).hom) ▷ M)) ≫
        (((ihom K).obj K') ◁ (α_ K ((ihom M).obj M') M).hom) ≫
        (α_ ((ihom K).obj K') K (((ihom M).obj M') ⊗ M)).inv ≫
        ringedSpaceDerivedInternalHomEvaluation K K' ▷ (((ihom M).obj M') ⊗ M) ≫
        K' ◁ ringedSpaceDerivedInternalHomEvaluation M M' := sorry

/-- Remark 20.42.10: in `D(\mathcal O_X)`, there is a canonical morphism
`R\mathcal H\!\mathit{om}(K, K') \otimes_{\mathcal O_X}^{\mathbf L}
R\mathcal H\!\mathit{om}(M, M') \to
R\mathcal H\!\mathit{om}(K \otimes_{\mathcal O_X}^{\mathbf L} M,
K' \otimes_{\mathcal O_X}^{\mathbf L} M')`. -/
noncomputable def ringedSpaceDerivedTensorInternalHomComparison
    (K K' M M' : RingedSpaceDerived X) :
    (ihom K).obj K' ⊗ (ihom M).obj M' ⟶ (ihom (K ⊗ M)).obj (K' ⊗ M') :=
  MonoidalClosed.curry <|
    (β_ (K ⊗ M) ((ihom K).obj K' ⊗ (ihom M).obj M')).hom ≫
      ringedSpaceDerivedTensorInternalHomComparisonTranspose K K' M M'

-- Proof sketch: `ringedSpaceDerivedTensorInternalHomComparison` is defined as the adjoint
-- transpose of the explicit four-factor morphism. Uncurrying therefore recovers the braiding
-- that puts `K \otimes^{\mathbf L} M` into the left slot, followed by the transpose map.
/-- Uncurrying the canonical tensor-internal-Hom comparison recovers the explicit morphism
obtained by braiding `K \otimes^{\mathbf L} M` to the front and then evaluating each internal
Hom factor. -/
theorem ringedSpaceDerivedTensorInternalHomComparison_uncurry
    (K K' M M' : RingedSpaceDerived X) :
    MonoidalClosed.uncurry (ringedSpaceDerivedTensorInternalHomComparison K K' M M') =
      (β_ (K ⊗ M) ((ihom K).obj K' ⊗ (ihom M).obj M')).hom ≫
        ringedSpaceDerivedTensorInternalHomComparisonTranspose K K' M M' := sorry

end

end AlgebraicGeometry.RingedSpace
