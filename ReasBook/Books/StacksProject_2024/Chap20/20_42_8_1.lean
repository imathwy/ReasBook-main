import StacksProject_2024.Chap20.Lemma_20_42_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

variable [MonoidalCategory (RingedSpaceDerived X)]
variable [BraidedCategory (RingedSpaceDerived X)]
variable [MonoidalClosed (RingedSpaceDerived X)]

/-- The derived dual `L^∨` of an object `L` of `D(\mathcal O_X)`. -/
noncomputable abbrev ringedSpaceDerivedDual
    (L : RingedSpaceDerived X) :
    RingedSpaceDerived X :=
  (ihom L).obj (𝟙_ (RingedSpaceDerived X))

notation:max L:max "^∨" => ringedSpaceDerivedDual L

/-- 20.42.8.1: the canonical morphism
`M \otimes_{\mathcal O_X}^{\mathbf L} L^\vee \to R\mathcal H\!\mathit{om}(L, M)` in
`D(\mathcal O_X)`. It is obtained by braiding to `L^\vee \otimes M`, identifying `M` with
`R\mathcal H\!\mathit{om}(\mathcal O_X, M)`, and then composing internal Homs. -/
noncomputable def ringedSpaceDerivedEvaluationHom
    (L M : RingedSpaceDerived X) :
    M ⊗ L^∨ ⟶ (ihom L).obj M :=
  (β_ M L^∨).hom ≫
    (L^∨ ◁
      (unitIsoSelf M).symm.hom) ≫
    comp L (𝟙_ (RingedSpaceDerived X)) M

end

end AlgebraicGeometry.RingedSpace
