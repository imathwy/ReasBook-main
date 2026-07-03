import Mathlib
import StacksProject_2024.Chap20.«20_14_1_1»
import StacksProject_2024.Chap20.Remark_20_28_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

variable
    (leftDerivedPullback :
      DerivedCategory (ModuleCat (globalSectionsRing X)) ⥤ DerivedCategory (RingedSpace.Modules X))
variable
    (globalSectionsAdj :
      Adjunction leftDerivedPullback (moduleDerivedGlobalSections X))
variable (derivedTensorX :
  DerivedCategory (RingedSpace.Modules X) ⥤
    DerivedCategory (RingedSpace.Modules X) ⥤
      DerivedCategory (RingedSpace.Modules X))
variable (derivedTensorΓ :
  DerivedCategory (ModuleCat (globalSectionsRing X)) ⥤
    DerivedCategory (ModuleCat (globalSectionsRing X)) ⥤
      DerivedCategory (ModuleCat (globalSectionsRing X)))
variable (pullbackTensorIso :
  ∀ (A B : DerivedCategory (ModuleCat (globalSectionsRing X))),
    leftDerivedPullback.obj ((derivedTensorΓ.obj B).obj A) ≅
      ((derivedTensorX.obj (leftDerivedPullback.obj B)).obj (leftDerivedPullback.obj A)))

/-- Remark 20.31.2: a representative `ξ : \Gamma(X,\mathcal O_X)[-i] \to R\Gamma(X,K)` defines
the associated left cup-product morphism
`R\Gamma(X,M)[-i] \to R\Gamma(X, K \otimes_{\mathcal O_X}^{\mathbf L} M)`. The source is
identified with `\Gamma(X,\mathcal O_X)[-i] \otimes_A^{\mathbf L} R\Gamma(X,M)` by the chosen
isomorphism `shiftTensorIso`. -/
noncomputable def derivedGlobalSections_leftCupBy
    {K M : DerivedCategory (RingedSpace.Modules X)}
    (i : ℤ)
    (shiftTensorIso :
      ((moduleDerivedGlobalSections X).obj M)⟦-i⟧ ≅
        ((derivedTensorΓ.obj ((moduleDerivedGlobalSections X).obj M)).obj
          ((DerivedCategory.singleFunctor (ModuleCat (globalSectionsRing X)) (-i)).obj
            (ModuleCat.of (globalSectionsRing X) (globalSectionsRing X)))))
    (ξ :
      ((DerivedCategory.singleFunctor (ModuleCat (globalSectionsRing X)) (-i)).obj
        (ModuleCat.of (globalSectionsRing X) (globalSectionsRing X))) ⟶
        (moduleDerivedGlobalSections X).obj K) :
    ((moduleDerivedGlobalSections X).obj M)⟦-i⟧ ⟶
      (moduleDerivedGlobalSections X).obj ((derivedTensorX.obj M).obj K) :=
  shiftTensorIso.hom ≫
    (derivedTensorΓ.obj ((moduleDerivedGlobalSections X).obj M)).map ξ ≫
      relativeDerivedCupProduct leftDerivedPullback (moduleDerivedGlobalSections X)
        globalSectionsAdj
        derivedTensorX derivedTensorΓ pullbackTensorIso K M

-- Proof sketch: unfold `derivedGlobalSections_leftCupBy`. By definition it is the composite of
-- the chosen identification `RΓ(X,M)[-i] ≅ Γ(X,\mathcal O_X)[-i] ⊗^L_A RΓ(X,M)`, the tensor of
-- the representative `ξ` with the identity on `RΓ(X,M)`, and the global derived cup product.
/-- The left cup-product map is the composite of the shift-tensor identification, the tensor of
the representative `ξ`, and the global derived cup product. -/
theorem derivedGlobalSections_leftCupBy_def
    {K M : DerivedCategory (RingedSpace.Modules X)}
    (i : ℤ)
    (shiftTensorIso :
      ((moduleDerivedGlobalSections X).obj M)⟦-i⟧ ≅
        ((derivedTensorΓ.obj ((moduleDerivedGlobalSections X).obj M)).obj
          ((DerivedCategory.singleFunctor (ModuleCat (globalSectionsRing X)) (-i)).obj
            (ModuleCat.of (globalSectionsRing X) (globalSectionsRing X)))))
    (ξ :
      ((DerivedCategory.singleFunctor (ModuleCat (globalSectionsRing X)) (-i)).obj
        (ModuleCat.of (globalSectionsRing X) (globalSectionsRing X))) ⟶
        (moduleDerivedGlobalSections X).obj K) :
    derivedGlobalSections_leftCupBy derivedTensorX derivedTensorΓ i shiftTensorIso ξ =
      shiftTensorIso.hom ≫
        (derivedTensorΓ.obj ((moduleDerivedGlobalSections X).obj M)).map ξ ≫
          relativeDerivedCupProduct leftDerivedPullback (moduleDerivedGlobalSections X)
            globalSectionsAdj
            derivedTensorX derivedTensorΓ pullbackTensorIso K M := sorry

end

end AlgebraicGeometry.RingedSpace
