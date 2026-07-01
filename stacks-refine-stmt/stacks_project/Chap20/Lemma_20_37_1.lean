import Mathlib
import stacks_project.Chap15.Lemma_15_87_10
import stacks_project.Chap19.Lemma_19_13_6
import stacks_project.Chap20.Lemma_20_33_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable (X : RingedSpace.{u}) (U : Opens X.carrier)
variable [IsGrothendieckAbelian (RingedSpace.Modules X)]

/-- Sheaves of `\mathcal O_X`-modules on a ringed space form an abelian category. -/
local instance sheafModulesAbelian : Abelian (RingedSpace.Modules X) := inferInstance

/-- The category of `\mathcal O_X`-modules on a ringed space carries the standard derived
category. -/
local instance sheafModulesHasDerivedCategory : HasDerivedCategory (RingedSpace.Modules X) :=
  HasDerivedCategory.standard (RingedSpace.Modules X)

-- Proof sketch: apply Lemma `19.13.6` to the additive sections functor `\Gamma(U,-)` on
-- `\mathcal O_X`-modules, using the canonical owner
-- `derivedSectionsAtOpenToAbelian X U`.
/-- Lemma 20.37.1 (1): for a ringed space `X` and an open subset `U ⊆ X`, the derived sections
functor `R\Gamma(U,-)` on `D(\mathcal O_X)` sends a sequential derived inverse limit to the
derived inverse limit of the stagewise derived sections. -/
theorem derivedSectionsOverOpen_preservesDerivedLimit
    {Ksys : ℕᵒᵖ ⥤ ringedSpaceModuleDerived X}
    {K : ringedSpaceModuleDerived X}
    (hK : IsDerivedLimit Ksys K) :
    IsDerivedLimit (Ksys ⋙ derivedSectionsAtOpenToAbelian X U)
      ((derivedSectionsAtOpenToAbelian X U).obj K) := sorry

-- Proof sketch: first apply part `(1)` to identify `R\Gamma(U, K)` as a derived limit of the
-- tower `n ↦ R\Gamma(U, K_n)`, then apply the Milnor short exact sequence
-- `derivedLimit_cohomology_shortExact` in `D(\operatorname{Ab})`.
/-- Lemma 20.37.1 (2): for a ringed space `X`, an open subset `U ⊆ X`, a sequential inverse
system `(K_n)` in `D(\mathcal O_X)`, a chosen derived limit `K = R\!\varprojlim K_n`, and
`m : ℤ`, the groups `H^m(U, K)` fit into the short exact sequence
`0 \to R^1 \!\varprojlim H^{m-1}(U, K_n) \to H^m(U, K) \to \varprojlim H^m(U, K_n) \to 0`.
Here the left term is canonically realized as the owner
`((Ksys ⋙ derivedSectionsAtOpenToAbelian X U) ⋙
  DerivedCategory.homologyFunctor AddCommGrpCat.{u} (m - 1)).firstDerivedLimit`. -/
theorem derivedSectionsOverOpen_cohomology_shortExact
    (Ksys : ℕᵒᵖ ⥤ ringedSpaceModuleDerived X)
    (K : ringedSpaceModuleDerived X)
    (hK : IsDerivedLimit Ksys K) (m : ℤ) :
    ∃ (ι :
        ((Ksys ⋙ derivedSectionsAtOpenToAbelian X U) ⋙
          DerivedCategory.homologyFunctor AddCommGrpCat.{u} (m - 1)).firstDerivedLimit ⟶
          (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).obj
            ((derivedSectionsAtOpenToAbelian X U).obj K))
      (π :
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).obj
            ((derivedSectionsAtOpenToAbelian X U).obj K) ⟶
          limit
            ((Ksys ⋙ derivedSectionsAtOpenToAbelian X U) ⋙
              DerivedCategory.homologyFunctor AddCommGrpCat.{u} m))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry

end

end AlgebraicGeometry.RingedSpace
