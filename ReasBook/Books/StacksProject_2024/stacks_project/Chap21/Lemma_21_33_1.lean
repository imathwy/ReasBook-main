import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import StacksProject_2024.stacks_project.Chap21.Lemma_21_33_1_assoc

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v w w'

namespace CategoryTheory

section

/- Domain-style sampling for Lemma 21.33.1:
- primary domain: relative cup products for an adjunction `Lf^* ⊣ Rf_*` between monoidal derived
  categories, together with the comparison square between the derived cup product and the naive
  underived tensor construction;
- sampled owner declarations:
  `CategoryTheory.CommSq`,
  `CategoryTheory.Adjunction.homEquiv`,
  `CategoryTheory.curriedTensor`,
  `CategoryTheory.relativeDerivedCupProduct`,
  `CategoryTheory.relativeDerivedCupProductAdjointMap`;
- best owner abstraction: the generic owner is the already extracted canonical owner
  `CategoryTheory.relativeDerivedCupProduct`, obtained by transposing the pullback-side tensor map
  across the adjunction; this file keeps the later source-facing compatibility theorems for that
  owner, not schematic statements about arbitrary unrelated comparison maps;
- primitive data: the adjunction `leftDerivedPullback ⊣ rightDerivedPushforward`, the source and
  target tensor functors, the pullback-tensor comparison, the underived-to-derived comparison maps,
  the source-side comparison `Lf^* (f_* K•) ⟶ K•`, and the naive cup product;
- derived API: `relativeDerivedCupProduct`, its adjoint-side bridge
  `relativeDerivedCupProductAdjointMap`, its braided commutativity square under a
  braiding-compatible pullback-tensor comparison, and the tensor/naive comparison square under the
  corresponding pullback-side compatibility square below.

Source/core/bridge triage:
- `source-facing`: `relativeDerivedCupProduct_commutative_commSq` and
  `derivedPushforward_tensor_naiveCupProduct_commSq`;
- `core/canonical`: `relativeDerivedCupProduct`, imported from
  `stacks_project.Chap21.Lemma_21_33_1_core`;
- `bridge/view`: `relativeDerivedCupProductAdjointMap` and its specification theorem
  `relativeDerivedCupProduct_spec`; the source-facing comparison square below uses the canonical
  owner term directly rather than introducing a parallel local edge-map API. -/

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

-- Proof sketch: transpose both routes across the adjunction `leftDerivedPullback ⊣
-- rightDerivedPushforward`. If the pullback-tensor comparison intertwines the source and target
-- braidings, the two transposes become the same morphism
-- `Lf^*(Rf_* K ⊗ Rf_* L) ⟶ L ⊗ K`, so the displayed square commutes.
section

variable [MonoidalCategory SourceDerived] [BraidedCategory SourceDerived]
variable [MonoidalCategory TargetDerived] [BraidedCategory TargetDerived]

/-- The relative derived cup product is compatible with the braidings on source and target,
provided the pullback-tensor comparison intertwines those braidings. In `CommSq` form, the left
edge is the target braiding, the right edge is the pushforward of the source braiding, and the
horizontal edges are the relative cup products with the two tensor factors in opposite orders. -/
theorem relativeDerivedCupProduct_commutative_commSq
    (pullbackTensorIso' :
      ∀ K L : TargetDerived,
        leftDerivedPullback.obj (K ⊗ L) ≅
          (leftDerivedPullback.obj K ⊗ leftDerivedPullback.obj L))
    (pullbackTensorBraiding :
      ∀ K L : TargetDerived,
        CommSq
          (pullbackTensorIso' K L).hom
          (leftDerivedPullback.map (β_ K L).hom)
          (β_ (leftDerivedPullback.obj K) (leftDerivedPullback.obj L)).hom
          (pullbackTensorIso' L K).hom)
    (K L : SourceDerived) :
    CommSq
      (relativeDerivedCupProduct
        leftDerivedPullback rightDerivedPushforward pullPushAdj
        (curriedTensor SourceDerived) (curriedTensor TargetDerived)
        (fun K L ↦ pullbackTensorIso' L K) L K)
      (β_ (rightDerivedPushforward.obj K) (rightDerivedPushforward.obj L)).hom
      (rightDerivedPushforward.map (β_ K L).hom)
      (relativeDerivedCupProduct
        leftDerivedPullback rightDerivedPushforward pullPushAdj
        (curriedTensor SourceDerived) (curriedTensor TargetDerived)
        (fun K L ↦ pullbackTensorIso' L K) K L) := by
  sorry

end

section

variable {MiddleDerived : Type u} [Category.{v} MiddleDerived]
variable {FinalDerived : Type u} [Category.{v} FinalDerived]

variable
  (leftDerivedPullback_f : MiddleDerived ⥤ SourceDerived)
  (rightDerivedPushforward_f : SourceDerived ⥤ MiddleDerived)
  (pullPushAdj_f : leftDerivedPullback_f ⊣ rightDerivedPushforward_f)
  (leftDerivedPullback_g : FinalDerived ⥤ MiddleDerived)
  (rightDerivedPushforward_g : MiddleDerived ⥤ FinalDerived)
  (pullPushAdj_g : leftDerivedPullback_g ⊣ rightDerivedPushforward_g)
  (leftDerivedPullback_comp : FinalDerived ⥤ SourceDerived)
  (rightDerivedPushforward_comp : SourceDerived ⥤ FinalDerived)
  (pullPushAdj_comp : leftDerivedPullback_comp ⊣ rightDerivedPushforward_comp)
  (pullbackCompIso : leftDerivedPullback_g ⋙ leftDerivedPullback_f ≅ leftDerivedPullback_comp)
  (pushforwardCompIso :
    rightDerivedPushforward_f ⋙ rightDerivedPushforward_g ≅ rightDerivedPushforward_comp)
  (pushforwardCompIso_hom_counit :
    Functor.whiskerRight pushforwardCompIso.hom leftDerivedPullback_comp ≫
        pullPushAdj_comp.counit =
      ((pullPushAdj_g.comp pullPushAdj_f).ofNatIsoLeft pullbackCompIso).counit)
  (tensorMiddle : MiddleDerived ⥤ MiddleDerived ⥤ MiddleDerived)
  (tensorFinal : FinalDerived ⥤ FinalDerived ⥤ FinalDerived)
  (pullbackTensorIso_f :
    ∀ (K L : MiddleDerived),
      leftDerivedPullback_f.obj ((tensorMiddle.obj L).obj K) ≅
        ((tensorSource.obj (leftDerivedPullback_f.obj L)).obj
          (leftDerivedPullback_f.obj K)))
  (pullbackTensorIso_g :
    ∀ (K L : FinalDerived),
      leftDerivedPullback_g.obj ((tensorFinal.obj L).obj K) ≅
        ((tensorMiddle.obj (leftDerivedPullback_g.obj L)).obj
          (leftDerivedPullback_g.obj K)))
  (pullbackTensorIso_comp :
    ∀ (K L : FinalDerived),
      leftDerivedPullback_comp.obj ((tensorFinal.obj L).obj K) ≅
        ((tensorSource.obj (leftDerivedPullback_comp.obj L)).obj
          (leftDerivedPullback_comp.obj K)))

/-- The source comparison edge in the composition square for the relative derived cup product. -/
private abbrev relativeDerivedCupProductCompSourceMap
    (K L : SourceDerived) :
    (tensorFinal.obj (rightDerivedPushforward_comp.obj L)).obj
        (rightDerivedPushforward_comp.obj K) ⟶
      (tensorFinal.obj
          (rightDerivedPushforward_g.obj (rightDerivedPushforward_f.obj L))).obj
        (rightDerivedPushforward_g.obj (rightDerivedPushforward_f.obj K)) :=
  ((tensorFinal.map (pushforwardCompIso.inv.app L)).app
      (rightDerivedPushforward_comp.obj K)) ≫
    (tensorFinal.obj
      (rightDerivedPushforward_g.obj (rightDerivedPushforward_f.obj L))).map
      (pushforwardCompIso.inv.app K)

/-- The target comparison edge in the composition square for the relative derived cup product. -/
private abbrev relativeDerivedCupProductCompTargetMap
    (K L : SourceDerived) :
    rightDerivedPushforward_comp.obj ((tensorSource.obj L).obj K) ⟶
      rightDerivedPushforward_g.obj
        (rightDerivedPushforward_f.obj ((tensorSource.obj L).obj K)) :=
  pushforwardCompIso.inv.app ((tensorSource.obj L).obj K)

/-- The iterated relative cup product along `f` and `g`. -/
private abbrev relativeDerivedCupProductCompIteratedMap
    (K L : SourceDerived) :
    (tensorFinal.obj
        (rightDerivedPushforward_g.obj (rightDerivedPushforward_f.obj L))).obj
      (rightDerivedPushforward_g.obj (rightDerivedPushforward_f.obj K)) ⟶
      rightDerivedPushforward_g.obj
        (rightDerivedPushforward_f.obj ((tensorSource.obj L).obj K)) :=
  relativeDerivedCupProduct
      leftDerivedPullback_g rightDerivedPushforward_g pullPushAdj_g
      tensorMiddle tensorFinal pullbackTensorIso_g
      (rightDerivedPushforward_f.obj K) (rightDerivedPushforward_f.obj L) ≫
    rightDerivedPushforward_g.map
      (relativeDerivedCupProduct
        leftDerivedPullback_f rightDerivedPushforward_f pullPushAdj_f
        tensorSource tensorMiddle pullbackTensorIso_f K L)

-- Proof sketch: transpose both routes across the adjunction
-- `leftDerivedPullback_comp ⊣ rightDerivedPushforward_comp`. The direct route becomes the
-- pullback-tensor comparison for the composite adjunction together with its counits. For the
-- iterated route, `relativeDerivedCupProduct_spec` expands both cup products to pullback-side
-- maps; the hypothesis `pushforwardCompIso_hom_counit` identifies the counit of the composite
-- pushforward comparison with the counit of the composed adjunction, so both transposes agree.
/-- The relative derived cup product is compatible with composition of derived pushforwards. In
`CommSq` form, the top edge is the cup product for the composite adjunction, the left edge is the
tensor of the comparison maps `R_comp ≅ R_g ⋙ R_f`, the right edge is the comparison map on the
tensor product, and the bottom edge is the iterated cup product for `g` followed by
`rightDerivedPushforward_g` applied to the cup product for `f`. -/
theorem relativeDerivedCupProduct_comp_commSq
    (K L : SourceDerived) :
    CommSq
      (relativeDerivedCupProduct
        leftDerivedPullback_comp rightDerivedPushforward_comp pullPushAdj_comp
        tensorSource tensorFinal pullbackTensorIso_comp K L)
      (relativeDerivedCupProductCompSourceMap
        rightDerivedPushforward_f rightDerivedPushforward_g rightDerivedPushforward_comp
        pushforwardCompIso tensorFinal K L)
      (relativeDerivedCupProductCompTargetMap
        tensorSource rightDerivedPushforward_f rightDerivedPushforward_g
        rightDerivedPushforward_comp pushforwardCompIso K L)
      (relativeDerivedCupProductCompIteratedMap
        tensorSource
        leftDerivedPullback_f rightDerivedPushforward_f pullPushAdj_f
        leftDerivedPullback_g rightDerivedPushforward_g pullPushAdj_g
        tensorMiddle tensorFinal pullbackTensorIso_f pullbackTensorIso_g K L) := by
  sorry

/-- Equality form of the composition compatibility square for the relative derived cup product. -/
theorem relativeDerivedCupProduct_comp_eq_iterated
    (K L : SourceDerived) :
    relativeDerivedCupProduct
        leftDerivedPullback_comp rightDerivedPushforward_comp pullPushAdj_comp
        tensorSource tensorFinal pullbackTensorIso_comp K L =
      (relativeDerivedCupProductCompSourceMap
        rightDerivedPushforward_f rightDerivedPushforward_g rightDerivedPushforward_comp
        pushforwardCompIso tensorFinal K L) ≫
        (relativeDerivedCupProductCompIteratedMap
          tensorSource
          leftDerivedPullback_f rightDerivedPushforward_f pullPushAdj_f
          leftDerivedPullback_g rightDerivedPushforward_g pullPushAdj_g
          tensorMiddle tensorFinal pullbackTensorIso_f pullbackTensorIso_g K L) ≫
        pushforwardCompIso.hom.app ((tensorSource.obj L).obj K) := by
  sorry

end

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

/-- The top edge of the tensor/naive-cup-product comparison square. -/
private abbrev derivedPushforwardTensorNaiveCupTopMap
    (K M : SourceComplex) :
    ((tensorTarget.obj (targetComplexToDerived (pushforwardComplex M))).obj
      (targetComplexToDerived (pushforwardComplex K))) ⟶
      ((tensorTarget.obj (rightDerivedPushforward.obj (sourceComplexToDerived M))).obj
        (rightDerivedPushforward.obj (sourceComplexToDerived K))) :=
  ((tensorTarget.map (pushforwardUnit M)).app
      (targetComplexToDerived (pushforwardComplex K))) ≫
    ((tensorTarget.obj (rightDerivedPushforward.obj (sourceComplexToDerived M))).map
      (pushforwardUnit K))

/-- The left edge of the tensor/naive-cup-product comparison square. -/
private abbrev derivedPushforwardTensorNaiveCupLeftMap
    (K M : SourceComplex) :
    ((tensorTarget.obj (targetComplexToDerived (pushforwardComplex M))).obj
      (targetComplexToDerived (pushforwardComplex K))) ⟶
      targetComplexToDerived (pushforwardComplex (sourceTensorComplex K M)) :=
  targetTensorCounit K M ≫ naiveCupProduct K M

/-- The right edge of the tensor/naive-cup-product comparison square. -/
private abbrev derivedPushforwardTensorNaiveCupRightMap
    (K M : SourceComplex) :
    ((tensorTarget.obj (rightDerivedPushforward.obj (sourceComplexToDerived M))).obj
      (rightDerivedPushforward.obj (sourceComplexToDerived K))) ⟶
      rightDerivedPushforward.obj (sourceComplexToDerived (sourceTensorComplex K M)) :=
  relativeDerivedCupProduct
      leftDerivedPullback rightDerivedPushforward pullPushAdj
      tensorSource tensorTarget pullbackTensorIso
      (sourceComplexToDerived K) (sourceComplexToDerived M) ≫
    rightDerivedPushforward.map (sourceTensorCounit K M)

/-- The bottom edge of the tensor/naive-cup-product comparison square. -/
private abbrev derivedPushforwardTensorNaiveCupBottomMap
    (K M : SourceComplex) :
    targetComplexToDerived (pushforwardComplex (sourceTensorComplex K M)) ⟶
      rightDerivedPushforward.obj (sourceComplexToDerived (sourceTensorComplex K M)) :=
  pushforwardUnit (sourceTensorComplex K M)

-- Proof sketch: transpose the clockwise and anticlockwise outer composites across the adjunction
-- `Lf^* ⊣ Rf_*`. Remark `21.19.7` identifies the transpose of the right-hand route with the
-- pullback-tensor comparison and the two counits. Lemma `21.19.6` replaces the derived counit by
-- the underived counit after the comparison `Lf^* ⟶ f^*`, and Lemma `21.18.8` supplies the upper
-- commutative polygon. The remaining lower square is the defining functoriality square for the
-- naive cup product and the morphism
-- `A• ⊗ᴸ B• ⟶ Tot (A• ⊗ B•)`.
/-- Lemma 21.33.1: the diagram comparing the tensor of `f_*`-images, the relative derived cup
product, the passage from derived tensor products to total tensor complexes, and the naive cup
product commutes, provided the chosen comparison maps satisfy the corresponding pullback-side
compatibility square. In `CommSq` form, the top edge is the tensor of the canonical maps
`f_* K• ⟶ Rf_* K•` and `f_* M• ⟶ Rf_* M•`, the left edge is the map
to `Tot (f_* K• ⊗ f_* M•)` followed by the naive cup product, the
right edge is the relative cup product followed by the map to
`Rf_* (Tot (K• ⊗ M•))`, and the bottom edge is the canonical map from
`f_* (Tot (K• ⊗ M•))` to
`Rf_* (Tot (K• ⊗ M•))`. The hypothesis records the corresponding
commutative square after applying `Lf^*`, with bottom edge the chosen comparison map
`Lf^* (f_* (Tot (K• ⊗ M•))) ⟶ Tot (K• ⊗ M•)`. -/
@[stacks 0FPK]
theorem derivedPushforward_tensor_naiveCupProduct_commSq
    (pullbackCounit :
      ∀ K : SourceComplex,
        leftDerivedPullback.obj (targetComplexToDerived (pushforwardComplex K)) ⟶
          sourceComplexToDerived K)
    (pullbackCounit_spec :
      ∀ K : SourceComplex,
        ((pullPushAdj.homEquiv
            (targetComplexToDerived (pushforwardComplex K))
            (sourceComplexToDerived K)).symm
          (pushforwardUnit K)) =
          pullbackCounit K)
    (pullbackCompatibility :
      ∀ K M : SourceComplex,
        CommSq
          (leftDerivedPullback.map
            (((tensorTarget.map (pushforwardUnit M)).app
                (targetComplexToDerived (pushforwardComplex K))) ≫
              ((tensorTarget.obj (rightDerivedPushforward.obj (sourceComplexToDerived M))).map
                (pushforwardUnit K))))
          (leftDerivedPullback.map (targetTensorCounit K M ≫ naiveCupProduct K M))
          (relativeDerivedCupProductAdjointMap
              leftDerivedPullback rightDerivedPushforward pullPushAdj
              tensorSource tensorTarget pullbackTensorIso
              (sourceComplexToDerived K) (sourceComplexToDerived M) ≫
            sourceTensorCounit K M)
          (pullbackCounit (sourceTensorComplex K M)))
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
      (pushforwardUnit (sourceTensorComplex K M)) := by
  sorry

end

end CategoryTheory
