import Mathlib.CategoryTheory.CommSq
import StacksProject_2024.stacks_project.Chap21.Lemma_21_33_1_core

-- Associativity support owner extracted from Lemma 21.33.1 for downstream files that only need
-- the generic associativity square for the relative derived cup product.

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

variable
  (tensorAssocSource :
    ∀ (K L M : SourceDerived),
      ((tensorSource.obj M).obj ((tensorSource.obj L).obj K)) ≅
        ((tensorSource.obj ((tensorSource.obj M).obj L)).obj K))
  (tensorAssocTarget :
    ∀ (K L M : TargetDerived),
      ((tensorTarget.obj M).obj ((tensorTarget.obj L).obj K)) ≅
        ((tensorTarget.obj ((tensorTarget.obj M).obj L)).obj K))

/- Support-owner abstraction:
- `core/canonical`: `CategoryTheory.relativeDerivedCupProduct`;
- `bridge/view`: the associativity square for that cup product, expressed as a canonical
  `CommSq`.

This file keeps the generic associativity theorem separate from the later Chapter 21 wrapper file,
so Chapter 20 and Chapter 21 recall-only consumers can reuse it without importing the later
commutativity/composition developments.
-/

/-- The top edge in the associativity square for the relative derived cup product. -/
private abbrev relativeDerivedCupProductAssociativityTopMap
    (K L M : SourceDerived) :
    ((tensorTarget.obj (rightDerivedPushforward.obj M)).obj
        ((tensorTarget.obj (rightDerivedPushforward.obj L)).obj
          (rightDerivedPushforward.obj K))) ⟶
      ((tensorTarget.obj (rightDerivedPushforward.obj M)).obj
        (rightDerivedPushforward.obj ((tensorSource.obj L).obj K))) :=
  (tensorTarget.obj (rightDerivedPushforward.obj M)).map
    (relativeDerivedCupProduct
      leftDerivedPullback rightDerivedPushforward pullPushAdj
      tensorSource tensorTarget pullbackTensorIso K L)

/-- The left edge in the associativity square for the relative derived cup product. -/
private abbrev relativeDerivedCupProductAssociativityLeftMap
    (K L M : SourceDerived) :
    ((tensorTarget.obj (rightDerivedPushforward.obj M)).obj
        ((tensorTarget.obj (rightDerivedPushforward.obj L)).obj
          (rightDerivedPushforward.obj K))) ⟶
      ((tensorTarget.obj
          (rightDerivedPushforward.obj ((tensorSource.obj M).obj L))).obj
        (rightDerivedPushforward.obj K)) :=
  (tensorAssocTarget
      (rightDerivedPushforward.obj K)
      (rightDerivedPushforward.obj L)
      (rightDerivedPushforward.obj M)).hom ≫
    (tensorTarget.map
      (relativeDerivedCupProduct
        leftDerivedPullback rightDerivedPushforward pullPushAdj
        tensorSource tensorTarget pullbackTensorIso L M)).app
      (rightDerivedPushforward.obj K)

/-- The right edge in the associativity square for the relative derived cup product. -/
private abbrev relativeDerivedCupProductAssociativityRightMap
    (K L M : SourceDerived) :
    ((tensorTarget.obj (rightDerivedPushforward.obj M)).obj
      (rightDerivedPushforward.obj ((tensorSource.obj L).obj K))) ⟶
      rightDerivedPushforward.obj
        ((tensorSource.obj ((tensorSource.obj M).obj L)).obj K) :=
  relativeDerivedCupProduct
      leftDerivedPullback rightDerivedPushforward pullPushAdj
      tensorSource tensorTarget pullbackTensorIso
      ((tensorSource.obj L).obj K) M ≫
    rightDerivedPushforward.map (tensorAssocSource K L M).hom

/-- The bottom edge in the associativity square for the relative derived cup product. -/
private abbrev relativeDerivedCupProductAssociativityBottomMap
    (K L M : SourceDerived) :
    ((tensorTarget.obj (rightDerivedPushforward.obj ((tensorSource.obj M).obj L))).obj
      (rightDerivedPushforward.obj K)) ⟶
      rightDerivedPushforward.obj
        ((tensorSource.obj ((tensorSource.obj M).obj L)).obj K) :=
  relativeDerivedCupProduct
    leftDerivedPullback rightDerivedPushforward pullPushAdj
    tensorSource tensorTarget pullbackTensorIso
    K ((tensorSource.obj M).obj L)

-- Proof sketch: transpose both routes across the adjunction `leftDerivedPullback ⊣
-- rightDerivedPushforward`. Both become the same map obtained from the pullback-tensor
-- comparison, the chosen tensor associators, and the counit maps on the three tensor factors.
/-- The relative derived cup product is associative after inserting the chosen source and target
tensor associators. In `CommSq` form, the top edge cups first in the pair `(K, L)`, the left edge
first cups `(L, M)`, the right edge cups `(K ⊗ L, M)` and then inserts the source associator, and
the bottom edge cups `(K, L ⊗ M)`. -/
theorem relativeDerivedCupProduct_associative_commSq
    (K L M : SourceDerived) :
    CommSq
      (relativeDerivedCupProductAssociativityTopMap
        leftDerivedPullback rightDerivedPushforward pullPushAdj
        tensorSource tensorTarget pullbackTensorIso K L M)
      (relativeDerivedCupProductAssociativityLeftMap
        leftDerivedPullback rightDerivedPushforward pullPushAdj
        tensorSource tensorTarget pullbackTensorIso tensorAssocTarget K L M)
      (relativeDerivedCupProductAssociativityRightMap
        leftDerivedPullback rightDerivedPushforward pullPushAdj
        tensorSource tensorTarget pullbackTensorIso tensorAssocSource K L M)
      (relativeDerivedCupProductAssociativityBottomMap
        leftDerivedPullback rightDerivedPushforward pullPushAdj
        tensorSource tensorTarget pullbackTensorIso K L M) := by
  sorry

end

end CategoryTheory
