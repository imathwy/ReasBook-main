import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v w w'

namespace CategoryTheory

section

variable {SourceDerived : Type u} [Category.{v} SourceDerived]
variable {TargetDerived : Type u} [Category.{v} TargetDerived]

variable
  (leftDerivedPullback : TargetDerived ⥤ SourceDerived)
  (rightDerivedPushforward : SourceDerived ⥤ TargetDerived)
  (pullPushAdj : leftDerivedPullback ⊣ rightDerivedPushforward)
  (tensorSource : SourceDerived ⥤ SourceDerived ⥤ SourceDerived)
  (tensorTarget : TargetDerived ⥤ TargetDerived ⥤ TargetDerived)
  (pullbackTensorIso :
    ∀ (K L : TargetDerived),
      leftDerivedPullback.obj ((tensorTarget.obj L).obj K) ≅
        ((tensorSource.obj (leftDerivedPullback.obj L)).obj
          (leftDerivedPullback.obj K)))

/-- The adjoint-side morphism whose transpose is the relative derived cup product. -/
private noncomputable abbrev relativeDerivedCupProductAdjoint
    (K M : SourceDerived) :
    leftDerivedPullback.obj
        ((tensorTarget.obj (rightDerivedPushforward.obj M)).obj
          (rightDerivedPushforward.obj K)) ⟶
      ((tensorSource.obj M).obj K) :=
  (pullbackTensorIso
      (rightDerivedPushforward.obj K)
      (rightDerivedPushforward.obj M)).hom ≫
    ((tensorSource.map (pullPushAdj.counit.app M)).app
      (leftDerivedPullback.obj (rightDerivedPushforward.obj K))) ≫
    ((tensorSource.obj M).map (pullPushAdj.counit.app K))

/-- The relative derived cup product obtained by transposing the pullback-side morphism across the
adjunction `leftDerivedPullback ⊣ rightDerivedPushforward`. -/
noncomputable def relativeDerivedCupProduct
    (K M : SourceDerived) :
    ((tensorTarget.obj (rightDerivedPushforward.obj M)).obj
      (rightDerivedPushforward.obj K)) ⟶
      rightDerivedPushforward.obj ((tensorSource.obj M).obj K) :=
  (pullPushAdj.homEquiv _ _)
    (relativeDerivedCupProductAdjoint
      leftDerivedPullback rightDerivedPushforward pullPushAdj
      tensorSource tensorTarget pullbackTensorIso K M)

variable {SourceComplex : Type w} {TargetComplex : Type w'}

variable
  (sourceComplexToDerived : SourceComplex → SourceDerived)
  (targetComplexToDerived : TargetComplex → TargetDerived)
  (pushforwardComplex : SourceComplex → TargetComplex)
  (sourceTensorComplex : SourceComplex → SourceComplex → SourceComplex)
  (pushforwardTensorComplex : SourceComplex → SourceComplex → TargetComplex)
  (targetTensorCounit :
    ∀ (K M : SourceComplex),
      ((tensorTarget.obj (targetComplexToDerived (pushforwardComplex M))).obj
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
      ((tensorSource.obj (sourceComplexToDerived M)).obj
        (sourceComplexToDerived K)) ⟶
          sourceComplexToDerived (sourceTensorComplex K M))

/-- The top horizontal arrow obtained by tensoring the canonical maps from underived to derived
pushforward. -/
private abbrev pushforwardTensorTopMap
    (K M : SourceComplex) :
    ((tensorTarget.obj (targetComplexToDerived (pushforwardComplex M))).obj
      (targetComplexToDerived (pushforwardComplex K))) ⟶
      ((tensorTarget.obj (rightDerivedPushforward.obj (sourceComplexToDerived M))).obj
        (rightDerivedPushforward.obj (sourceComplexToDerived K))) :=
  ((tensorTarget.map (pushforwardUnit M)).app
    (targetComplexToDerived (pushforwardComplex K))) ≫
    ((tensorTarget.obj (rightDerivedPushforward.obj (sourceComplexToDerived M))).map
      (pushforwardUnit K))

/-- The left vertical arrow given by the passage to the total underived tensor complex followed by
the naive cup product. -/
private abbrev naiveCupProductLeftMap
    (K M : SourceComplex) :
    ((tensorTarget.obj (targetComplexToDerived (pushforwardComplex M))).obj
      (targetComplexToDerived (pushforwardComplex K))) ⟶
      targetComplexToDerived (pushforwardComplex (sourceTensorComplex K M)) :=
  targetTensorCounit K M ≫ naiveCupProduct K M

/-- The right vertical arrow given by the relative derived cup product followed by the canonical
map to the pushed-forward total tensor complex. -/
private abbrev derivedCupProductRightMap
    (K M : SourceComplex) :
    ((tensorTarget.obj (rightDerivedPushforward.obj (sourceComplexToDerived M))).obj
      (rightDerivedPushforward.obj (sourceComplexToDerived K))) ⟶
      rightDerivedPushforward.obj (sourceComplexToDerived (sourceTensorComplex K M)) :=
  relativeDerivedCupProduct
      leftDerivedPullback rightDerivedPushforward pullPushAdj
      tensorSource tensorTarget pullbackTensorIso
      (sourceComplexToDerived K) (sourceComplexToDerived M) ≫
    rightDerivedPushforward.map (sourceTensorCounit K M)

-- Proof sketch: transpose the clockwise and anticlockwise outer composites across the adjunction
-- `Lf^* ⊣ Rf_*`. Remark `21.19.7` identifies the transpose of the right-hand route with the
-- pullback-tensor comparison and the two counits. Lemma `21.19.6` replaces the derived counit by
-- the underived counit after the comparison `Lf^* ⟶ f^*`, and Lemma `21.18.8` supplies the upper
-- commutative polygon. The remaining lower square is the defining functoriality square for the
-- naive cup product and the morphism
-- `\mathcal A^\bullet \otimes^{\mathbf L} \mathcal B^\bullet ⟶
--   \mathrm{Tot}(\mathcal A^\bullet \otimes \mathcal B^\bullet)`.
/-- Lemma 21.33.1: the diagram comparing the tensor of `f_*`-images, the relative derived cup
product, the passage from derived tensor products to total tensor complexes, and the naive cup
product commutes. In `CommSq` form, the top edge is the tensor of the canonical maps
`f_* K^\bullet ⟶ Rf_* K^\bullet` and `f_* M^\bullet ⟶ Rf_* M^\bullet`, the left edge is the map
to `\mathrm{Tot}(f_* K^\bullet \otimes f_* M^\bullet)` followed by the naive cup product, the
right edge is the relative cup product followed by the map to
`Rf_* \mathrm{Tot}(K^\bullet \otimes M^\bullet)`, and the bottom edge is the canonical map from
`f_* \mathrm{Tot}(K^\bullet \otimes M^\bullet)` to
`Rf_* \mathrm{Tot}(K^\bullet \otimes M^\bullet)`. -/
theorem derivedPushforward_tensor_naiveCupProduct_commSq
    (K M : SourceComplex) :
    CommSq
      (((tensorTarget.map (pushforwardUnit M)).app
          (targetComplexToDerived (pushforwardComplex K))) ≫
        ((tensorTarget.obj (rightDerivedPushforward.obj (sourceComplexToDerived M))).map
          (pushforwardUnit K)))
      (targetTensorCounit K M ≫ naiveCupProduct K M)
      (relativeDerivedCupProduct
          leftDerivedPullback rightDerivedPushforward pullPushAdj
          tensorSource tensorTarget pullbackTensorIso
          (sourceComplexToDerived K) (sourceComplexToDerived M) ≫
        rightDerivedPushforward.map (sourceTensorCounit K M))
      (pushforwardUnit (sourceTensorComplex K M)) := sorry

end

end CategoryTheory
