import Mathlib
import StacksProject_2024.Chap20.«20_14_1_1»
import StacksProject_2024.Chap20.Remark_20_28_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

section

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)
local notation "DΓX" => DerivedCategory (ModuleCat (globalSectionsRing X))
local notation "RΓ" => moduleDerivedGlobalSections X

variable
    (leftDerivedPullback : DΓX ⥤ DModX)
variable
    (globalSectionsAdj : Adjunction leftDerivedPullback RΓ)
variable (derivedTensorX : DModX ⥤ DModX ⥤ DModX)
variable (derivedTensorΓ : DΓX ⥤ DΓX ⥤ DΓX)
variable (pullbackTensorIso :
  ∀ (A B : DΓX),
    leftDerivedPullback.obj ((derivedTensorΓ.obj B).obj A) ≅
      ((derivedTensorX.obj (leftDerivedPullback.obj B)).obj (leftDerivedPullback.obj A)))

-- Proof sketch: the cohomology-class tensor `ξ ⊗ η` is the morphism obtained by functoriality of
-- the derived tensor product on `RΓ(X, K)` and `RΓ(X, L)`, precomposed with the chosen
-- identification of the source object with the tensor of the two shifted copies of the unit.
-- Its adjoint transpose is expressed directly in terms of the canonical lifts
-- `(globalSectionsAdj.homEquiv _ _).symm ξ` and `(globalSectionsAdj.homEquiv _ _).symm η`.
/-- Lemma 20.31.1: for derived global sections, composing the tensor of two cohomology-class
representatives with the canonical derived cup product has adjoint transpose equal to the tensor
of their canonical lifted representatives under `Lf^* ⊣ R\Gamma(X, -)`. This is the agreement with the
usual cup product construction described in the text. -/
theorem derivedGlobalSections_cupProduct_homEquiv
    {K L : DModX}
    {A₁ A₂ A₁₂ : DΓX}
    (tensorSourceIso : A₁₂ ≅ ((derivedTensorΓ.obj A₂).obj A₁))
    (ξ : A₁ ⟶ RΓ.obj K)
    (η : A₂ ⟶ RΓ.obj L) :
    ((globalSectionsAdj.homEquiv A₁₂ ((derivedTensorX.obj L).obj K)).symm)
        (tensorSourceIso.hom ≫
          (derivedTensorΓ.map η).app A₁ ≫
          (derivedTensorΓ.obj (RΓ.obj L)).map ξ ≫
          relativeDerivedCupProduct leftDerivedPullback RΓ globalSectionsAdj
            derivedTensorX derivedTensorΓ pullbackTensorIso K L) =
      leftDerivedPullback.map tensorSourceIso.hom ≫
        (pullbackTensorIso A₁ A₂).hom ≫
        (derivedTensorX.map ((globalSectionsAdj.homEquiv A₂ L).symm η)).app
          (leftDerivedPullback.obj A₁) ≫
        (derivedTensorX.obj L).map ((globalSectionsAdj.homEquiv A₁ K).symm ξ) := by
  rw [globalSectionsAdj.homEquiv_naturality_left_symm,
    globalSectionsAdj.homEquiv_naturality_left_symm,
    globalSectionsAdj.homEquiv_naturality_left_symm]
  simp [relativeDerivedCupProduct_homEquiv]

end

end AlgebraicGeometry.RingedSpace
