import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The structure sheaf of a ringed space, regarded as a sheaf of rings. -/
section

variable {X Y : RingedSpace.{u}}

local notation "DModX" => DerivedCategory (SheafOfModules (ringCatSheaf X))
local notation "DModY" => DerivedCategory (SheafOfModules (ringCatSheaf Y))

variable (leftDerivedPullback : DModY ⥤ DModX)
variable (rightDerivedPushforward : DModX ⥤ DModY)
variable (pullPushAdj : leftDerivedPullback ⊣ rightDerivedPushforward)
variable (derivedTensorX : DModX ⥤ DModX ⥤ DModX)
variable (derivedTensorY : DModY ⥤ DModY ⥤ DModY)
variable (pullbackTensorIso :
  ∀ (A B : DModY),
    leftDerivedPullback.obj ((derivedTensorY.obj B).obj A) ≅
      ((derivedTensorX.obj (leftDerivedPullback.obj B)).obj (leftDerivedPullback.obj A)))

/-- The adjoint-side morphism whose transpose is the relative cup product. -/
private noncomputable abbrev relativeDerivedCupProductAdjoint
    (K L : DModX) :
    leftDerivedPullback.obj
        ((derivedTensorY.obj (rightDerivedPushforward.obj L)).obj
          (rightDerivedPushforward.obj K)) ⟶
      ((derivedTensorX.obj L).obj K) :=
  (pullbackTensorIso
      (rightDerivedPushforward.obj K)
      (rightDerivedPushforward.obj L)).hom ≫
    ((derivedTensorX.map (pullPushAdj.counit.app L)).app
      (leftDerivedPullback.obj (rightDerivedPushforward.obj K))) ≫
    ((derivedTensorX.obj L).map (pullPushAdj.counit.app K))

/-- Remark 20.28.7: given the adjunction `Lf^* ⊣ Rf_*` and the pullback-tensor comparison of
Lemma 20.27.3, there is a canonical relative cup product
`Rf_* K \otimes^{\mathbf L} Rf_* L ⟶ Rf_*(K \otimes^{\mathbf L} L)`. -/
noncomputable def relativeDerivedCupProduct
    (K L : DModX) :
    ((derivedTensorY.obj (rightDerivedPushforward.obj L)).obj
      (rightDerivedPushforward.obj K)) ⟶
      rightDerivedPushforward.obj ((derivedTensorX.obj L).obj K) :=
  (pullPushAdj.homEquiv _ _)
    (relativeDerivedCupProductAdjoint
      leftDerivedPullback rightDerivedPushforward pullPushAdj derivedTensorX derivedTensorY
      pullbackTensorIso K L)

-- Proof sketch: unfold `relativeDerivedCupProduct`; it was defined by applying the adjunction
-- equivalence `Hom(Lf^* -, -) ≃ Hom(-, Rf_* -)` to the counit-induced composite after the
-- pullback-tensor comparison.
/-- The relative cup product is adjoint to the pullback-tensor comparison followed by the two
counit maps `Lf^* Rf_* K ⟶ K` and `Lf^* Rf_* L ⟶ L`. -/
theorem relativeDerivedCupProduct_homEquiv
    (K L : DModX) :
    (pullPushAdj.homEquiv _ _)
        (relativeDerivedCupProduct leftDerivedPullback rightDerivedPushforward pullPushAdj
          derivedTensorX derivedTensorY pullbackTensorIso K L) =
      relativeDerivedCupProductAdjoint leftDerivedPullback rightDerivedPushforward pullPushAdj
        derivedTensorX derivedTensorY pullbackTensorIso K L := sorry

end

end AlgebraicGeometry.RingedSpace
