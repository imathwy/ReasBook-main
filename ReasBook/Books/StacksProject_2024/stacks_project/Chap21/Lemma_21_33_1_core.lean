import Mathlib.CategoryTheory.Adjunction.Basic

-- Core owner declarations extracted from Lemma 21.33.1 for downstream files that only use the
-- relative derived cup product itself.

open CategoryTheory
noncomputable section

universe u v

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

/- Core owner abstraction:
- `core/canonical`: `CategoryTheory.relativeDerivedCupProduct`;
- `bridge/view`: `CategoryTheory.relativeDerivedCupProductAdjointMap` and
  `CategoryTheory.relativeDerivedCupProduct_spec`.

This file keeps only the owner layer needed by direct downstream uses such as base-change
compatibility, without importing the later associativity/commutativity/composition developments.
-/

/-- The adjoint-side morphism whose transpose is the relative derived cup product. -/
noncomputable def relativeDerivedCupProductAdjointMap
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
    (relativeDerivedCupProductAdjointMap
      leftDerivedPullback rightDerivedPushforward pullPushAdj
      tensorSource tensorTarget pullbackTensorIso K M)

/-- Applying `Adjunction.homEquiv.symm` to the relative derived cup product recovers the
pullback-side tensor comparison followed by the two counit maps. -/
theorem relativeDerivedCupProduct_spec
    (K M : SourceDerived) :
    ((pullPushAdj.homEquiv
        ((tensorTarget.obj (rightDerivedPushforward.obj M)).obj
          (rightDerivedPushforward.obj K))
        ((tensorSource.obj M).obj K)).symm
      (relativeDerivedCupProduct
        leftDerivedPullback rightDerivedPushforward pullPushAdj
        tensorSource tensorTarget pullbackTensorIso K M)) =
      relativeDerivedCupProductAdjointMap
        leftDerivedPullback rightDerivedPushforward pullPushAdj
        tensorSource tensorTarget pullbackTensorIso K M := by
  simp [relativeDerivedCupProduct]

end

end CategoryTheory
