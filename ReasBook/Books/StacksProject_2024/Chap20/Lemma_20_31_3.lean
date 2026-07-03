import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace AlgebraicGeometry.RingedSpace

section

variable {X Y : RingedSpace.{u}}

/-- The structure sheaf of a ringed space, regarded as a sheaf of rings. -/
local notation "DModX" => DerivedCategory (SheafOfModules (ringCatSheaf X))
local notation "DModY" => DerivedCategory (SheafOfModules (ringCatSheaf Y))

variable
    (leftDerivedPullback : DModY ⥤ DModX)
    (rightDerivedPushforward : DModX ⥤ DModY)
    (pullPushAdj : leftDerivedPullback ⊣ rightDerivedPushforward)
    (derivedTensorX : DModX ⥤ DModX ⥤ DModX)
    (derivedTensorY : DModY ⥤ DModY ⥤ DModY)
    (pullbackTensorIso :
      ∀ (A B : DModY),
        leftDerivedPullback.obj ((derivedTensorY.obj B).obj A) ≅
          ((derivedTensorX.obj (leftDerivedPullback.obj B)).obj
            (leftDerivedPullback.obj A)))

/-- The adjoint-side morphism whose transpose is the relative derived cup product. -/
private noncomputable abbrev relativeDerivedCupProductAdjoint
    (K M : DModX) :
    leftDerivedPullback.obj
        ((derivedTensorY.obj (rightDerivedPushforward.obj M)).obj
          (rightDerivedPushforward.obj K)) ⟶
      ((derivedTensorX.obj M).obj K) :=
  (pullbackTensorIso
      (rightDerivedPushforward.obj K)
      (rightDerivedPushforward.obj M)).hom ≫
    ((derivedTensorX.map (pullPushAdj.counit.app M)).app
      (leftDerivedPullback.obj (rightDerivedPushforward.obj K))) ≫
    ((derivedTensorX.obj M).map (pullPushAdj.counit.app K))

variable {SourceComplex : Type v} {TargetComplex : Type w}

/-- The derived cup product `Rf_* K ⊗^{\mathbf L} Rf_* M ⟶ Rf_*(K ⊗^{\mathbf L} M)` attached to
the adjunction `leftDerivedPullback ⊣ rightDerivedPushforward` and the pullback-tensor
comparison. -/
noncomputable def relativeDerivedCupProduct
    (K M : DModX) :
    ((derivedTensorY.obj (rightDerivedPushforward.obj M)).obj
      (rightDerivedPushforward.obj K)) ⟶
      rightDerivedPushforward.obj ((derivedTensorX.obj M).obj K) :=
  (pullPushAdj.homEquiv _ _)
    (relativeDerivedCupProductAdjoint leftDerivedPullback rightDerivedPushforward pullPushAdj
      derivedTensorX derivedTensorY pullbackTensorIso K M)

variable
    (sourceComplexToDerived : SourceComplex → DModX)
    (targetComplexToDerived : TargetComplex → DModY)
    (pushforwardComplex : SourceComplex → TargetComplex)
    (sourceTensorComplex : SourceComplex → SourceComplex → SourceComplex)
    (pushforwardTensorComplex : SourceComplex → SourceComplex → TargetComplex)
    (targetTensorCounit :
      ∀ (K M : SourceComplex),
        ((derivedTensorY.obj (targetComplexToDerived (pushforwardComplex M))).obj
          (targetComplexToDerived (pushforwardComplex K))) ⟶
            targetComplexToDerived (pushforwardTensorComplex K M))
    (pushforwardUnit :
      ∀ (K : SourceComplex),
        targetComplexToDerived (pushforwardComplex K) ⟶
          rightDerivedPushforward.obj (sourceComplexToDerived K))
    (naiveCupProduct :
      ∀ (K M : SourceComplex),
        targetComplexToDerived (pushforwardTensorComplex K M) ⟶
          targetComplexToDerived (pushforwardComplex (sourceTensorComplex K M)))
    (sourceTensorCounit :
      ∀ (K M : SourceComplex),
        ((derivedTensorX.obj (sourceComplexToDerived M)).obj
          (sourceComplexToDerived K)) ⟶
            sourceComplexToDerived (sourceTensorComplex K M))

-- Proof sketch: compare the two outer composites by transporting both across the adjunction
-- `leftDerivedPullback ⊣ rightDerivedPushforward`. Remark `20.28.7` identifies the clockwise
-- composite with the pullback-tensor comparison followed by the two counits, while Lemma `20.28.6`
-- replaces the derived pullback comparisons by the underived ones on chosen representatives. The
-- remaining rectangle is then exactly the functoriality square for the naive cup product and the
-- map from derived tensor products to total tensor complexes, so the two transposes agree.
/-- Lemma 20.31.3: the comparison from the tensor of the underived pushforwards to the derived
pushforward of the derived tensor product is compatible with the naive cup product on chosen
complex representatives. Equivalently, the square whose top edge is the tensor of the canonical
maps `f_* K^\bullet ⟶ Rf_* K^\bullet` and `f_* M^\bullet ⟶ Rf_* M^\bullet`, whose right edge is
the derived cup product followed by the map to `Rf_* \mathrm{Tot}(K^\bullet \otimes
M^\bullet)`, whose left edge is the passage to `\mathrm{Tot}(f_* K^\bullet \otimes f_* M^\bullet)`,
and whose bottom edge is the naive cup product followed by the canonical map to the derived
pushforward commutes. -/
theorem derivedPushforward_tensor_naiveCupProduct_square_commutes
    (K M : SourceComplex) :
    ((derivedTensorY.map (pushforwardUnit M)).app
        (targetComplexToDerived (pushforwardComplex K))) ≫
      ((derivedTensorY.obj (rightDerivedPushforward.obj (sourceComplexToDerived M))).map
        (pushforwardUnit K)) ≫
      relativeDerivedCupProduct leftDerivedPullback rightDerivedPushforward pullPushAdj
        derivedTensorX derivedTensorY pullbackTensorIso
        (sourceComplexToDerived K) (sourceComplexToDerived M) ≫
      rightDerivedPushforward.map (sourceTensorCounit K M) =
    targetTensorCounit K M ≫
      naiveCupProduct K M ≫
      pushforwardUnit (sourceTensorComplex K M) := sorry

end

end AlgebraicGeometry.RingedSpace
