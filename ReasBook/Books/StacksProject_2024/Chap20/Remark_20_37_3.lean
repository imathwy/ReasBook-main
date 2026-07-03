import Mathlib
import StacksProject_2024.Chap20.Lemma_20_32_3

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable (X : RingedSpace.{u}) (U : Opens X.carrier)
variable [IsGrothendieckAbelian.{v} (ringedSpaceModuleCat X)]

/-- The category of `\mathcal O_X`-modules on a ringed space is abelian. -/
local instance ringedSpaceModuleCatAbelian : Abelian (ringedSpaceModuleCat X) :=
  inferInstance

/-- The category of `\mathcal O_X`-modules on a ringed space carries the standard derived
category. -/
local instance ringedSpaceModuleCatHasDerivedCategory :
    HasDerivedCategory (ringedSpaceModuleCat X) :=
  HasDerivedCategory.standard (ringedSpaceModuleCat X)

/-- The underived sections functor `\Gamma(U,-)` on `\mathcal O_X`-modules, viewed in abelian
groups. -/
abbrev moduleSectionsAsAbelianFunctor :
    ringedSpaceModuleCat X ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf ((RingedSpace.ringCatSheaf X)) ⋙
    sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} ⋙
      (evaluation (Opens X.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op U)

/-- The derived sections functor `R\Gamma(U,-)` on `D(\mathcal O_X)`, viewed in
`D(\operatorname{Ab})`. -/
abbrev moduleSectionsAsAbelianDerived
    [(moduleSectionsAsAbelianFunctor X U).Additive] :
    DerivedCategory (ringedSpaceModuleCat X) ⥤
      DerivedCategory AddCommGrpCat.{u} :=
  CategoryTheory.additiveFunctorTotalRightDerived (moduleSectionsAsAbelianFunctor X U)

/-- A model for `R^1 \!\varprojlim H^q(U, K_n)`, given by the cokernel of the Milnor difference
map on the tower `n ↦ H^q(U, K_n)`. -/
abbrev firstDerivedLimitCohomologyAtOpen
    [(moduleSectionsAsAbelianFunctor X U).Additive]
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory (ringedSpaceModuleCat X)) (q : ℤ) :
    AddCommGrpCat.{u} :=
  cokernel
    (derivedLimitDifferenceMap
      (Ksys ⋙ moduleSectionsAsAbelianDerived X U ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} q))

-- Proof sketch: identify `\underline{\mathcal H}^m(U)` with the value at `U` of the objectwise
-- cohomology presheaf from Lemma `20.32.3`, then apply the Milnor short exact sequence
-- from Lemma `20.37.1` to the tower `Ksys`.
/-- Remark 20.37.3: for a ringed space `(X, \mathcal O_X)`, an open subset `U ⊆ X`, a
sequential inverse system `(K_n)` in `D(\mathcal O_X)`, a chosen derived limit
`K = R\!\varprojlim K_n`, and `m : ℤ`, the presheaf values
`\underline{\mathcal H}^m(U) = H^m(U, K)` fit into the short exact sequence
`0 \to R^1 \!\varprojlim \underline{\mathcal H}^{m - 1}_n(U) \to \underline{\mathcal H}^m(U) \to
\varprojlim \underline{\mathcal H}^m_n(U) \to 0`. Here
`ringedSpaceObjectwiseCohomologyPresheaf X K m` models the presheaf
`U \mapsto \underline{\mathcal H}^m(U)`, and the left term is modeled by
`firstDerivedLimitCohomologyAtOpen X U Ksys (m - 1)`. -/
theorem objectwiseCohomologyPresheaf_value_shortExact
    [(moduleSectionsAsAbelianFunctor X U).Additive]
    (Ksys : ℕᵒᵖ ⥤ DerivedCategory (ringedSpaceModuleCat X))
    (K : DerivedCategory (ringedSpaceModuleCat X))
    (hK : IsDerivedLimit Ksys K) (m : ℤ) :
    ∃ (ι :
        firstDerivedLimitCohomologyAtOpen X U Ksys (m - 1) ⟶
          (ringedSpaceObjectwiseCohomologyPresheaf X K m).obj (op U))
      (π :
        (ringedSpaceObjectwiseCohomologyPresheaf X K m).obj (op U) ⟶
          limit
            (Ksys ⋙ moduleSectionsAsAbelianDerived X U ⋙
              DerivedCategory.homologyFunctor AddCommGrpCat.{u} m))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry

end

end AlgebraicGeometry.RingedSpace
