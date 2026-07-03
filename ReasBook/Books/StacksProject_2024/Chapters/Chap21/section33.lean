import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_21_33_1 (from Chap21) -/
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

/-! ### Lemma_21_33_2 (from Chap21) -/
open CategoryTheory
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

/-- The abelian category of sheaves of modules on the ringed site `X`. -/
abbrev ModuleCat (X : RingedSite.{u, v}) :=
  SheafOfModules X.structureSheaf

/-- The unbounded derived category `D(\mathcal O_X)` of module sheaves on `X`. -/
abbrev ModuleDerived (X : RingedSite.{u, v}) :=
  DerivedCategory (ModuleCat X)

/-- The class of quasi-isomorphisms used to localize the homotopy category of module sheaves on
`X`. -/
abbrev ModuleQis (X : RingedSite.{u, v}) :=
  HomotopyCategory.quasiIso (ModuleCat X) (up ℤ)

/-- The direct-image functor on module sheaves attached to a morphism of ringed sites. -/
abbrev modulePushforward {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y) :
    ModuleCat X ⥤ ModuleCat Y :=
  SheafOfModules.pushforward f.structureSheafMap

/-- The functor on homotopy categories induced by direct image on module sheaves. -/
abbrev modulePushforwardToDerived {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [f.modulePushforward.Additive] :=
  mapHomotopyCategoryToDerived f.modulePushforward

/-- The functor on homotopy categories induced by inverse image on module sheaves. -/
abbrev modulePullbackToDerived {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [f.modulePullback.Additive] :=
  mapHomotopyCategoryToDerived f.modulePullback

/-- The unbounded right derived direct-image functor on module sheaves. -/
noncomputable abbrev modulePushforwardDerived {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [f.modulePushforward.Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)] :
    ModuleDerived X ⥤ ModuleDerived Y :=
  Functor.totalRightDerived (modulePushforwardToDerived f)
    (DerivedCategory.Qh :
      HomotopyCategory (ModuleCat X) (up ℤ) ⥤ DerivedCategory (ModuleCat X))
    (ModuleQis X)

/-- The unbounded left derived inverse-image functor on module sheaves. -/
noncomputable abbrev modulePullbackDerived {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [f.modulePullback.Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)] :
    ModuleDerived Y ⥤ ModuleDerived X :=
  Functor.totalLeftDerived (modulePullbackToDerived f)
    (DerivedCategory.Qh :
      HomotopyCategory (ModuleCat Y) (up ℤ) ⥤ DerivedCategory (ModuleCat Y))
    (ModuleQis Y)

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)

variable [f.modulePushforward.Additive]
variable [f.modulePullback.Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]

variable (tensorSource : ModuleDerived X ⥤ ModuleDerived X ⥤ ModuleDerived X)
variable (tensorTarget : ModuleDerived Y ⥤ ModuleDerived Y ⥤ ModuleDerived Y)
variable (adj : modulePullbackDerived f ⊣ modulePushforwardDerived f)

variable
  (pullbackTensorComparison :
    ∀ (K L : ModuleDerived Y),
      ((modulePullbackDerived f).obj ((tensorTarget.obj L).obj K)) ≅
        ((tensorSource.obj ((modulePullbackDerived f).obj L)).obj
          ((modulePullbackDerived f).obj K)))

/-- The morphism adjoint to the relative cup-product map, obtained from the pullback-tensor
comparison together with the counit `Lf^* Rf_* ⟶ \mathrm{id}` on each tensor factor. -/
noncomputable def relativeCupProductAdjointMap
    (K L : ModuleDerived X) :
    ((modulePullbackDerived f).obj
        ((tensorTarget.obj ((modulePushforwardDerived f).obj L)).obj
          ((modulePushforwardDerived f).obj K))) ⟶
      ((tensorSource.obj L).obj K) :=
  (pullbackTensorComparison
      ((modulePushforwardDerived f).obj K)
      ((modulePushforwardDerived f).obj L)).hom ≫
    ((tensorSource.map (adj.counit.app L)).app
      ((modulePullbackDerived f).obj ((modulePushforwardDerived f).obj K))) ≫
    ((tensorSource.obj L).map (adj.counit.app K))

/-- The relative cup-product morphism `Rf_* K ⊗^{\mathbf L} Rf_* L ⟶ Rf_*(K ⊗^{\mathbf L} L)`. -/
noncomputable def relativeCupProductMap
    (K L : ModuleDerived X) :
    ((tensorTarget.obj ((modulePushforwardDerived f).obj L)).obj
      ((modulePushforwardDerived f).obj K)) ⟶
      (modulePushforwardDerived f).obj ((tensorSource.obj L).obj K) :=
  (adj.homEquiv
      ((tensorTarget.obj ((modulePushforwardDerived f).obj L)).obj
        ((modulePushforwardDerived f).obj K))
      ((tensorSource.obj L).obj K))
    (relativeCupProductAdjointMap
      f tensorSource tensorTarget adj pullbackTensorComparison K L)

variable
  (tensorAssocSource :
    ∀ (K L M : ModuleDerived X),
      ((tensorSource.obj M).obj ((tensorSource.obj L).obj K)) ≅
        ((tensorSource.obj ((tensorSource.obj M).obj L)).obj K))
  (tensorAssocTarget :
    ∀ (K L M : ModuleDerived Y),
      ((tensorTarget.obj M).obj ((tensorTarget.obj L).obj K)) ≅
        ((tensorTarget.obj ((tensorTarget.obj M).obj L)).obj K))

/-- The derived tensor product on the source derived category with explicit left and right
factors. -/
private abbrev tensorSourceObj
    (tensorSource : ModuleDerived X ⥤ ModuleDerived X ⥤ ModuleDerived X)
    (K L : ModuleDerived X) : ModuleDerived X :=
  (tensorSource.obj L).obj K

/-- The derived tensor product on the target derived category with explicit left and right
factors. -/
private abbrev tensorTargetObj
    (tensorTarget : ModuleDerived Y ⥤ ModuleDerived Y ⥤ ModuleDerived Y)
    (K L : ModuleDerived Y) : ModuleDerived Y :=
  (tensorTarget.obj L).obj K

/-- The common source object `((Rf_* K ⊗ Rf_* L) ⊗ Rf_* M)` in the associativity square for the
relative cup product. -/
private abbrev relativeCupProductAssociativitySource
    (rightDerivedPushforward : ModuleDerived X ⥤ ModuleDerived Y)
    (tensorTarget : ModuleDerived Y ⥤ ModuleDerived Y ⥤ ModuleDerived Y)
    (K L M : ModuleDerived X) : ModuleDerived Y :=
  tensorTargetObj tensorTarget
    (tensorTargetObj tensorTarget (rightDerivedPushforward.obj K) (rightDerivedPushforward.obj L))
    (rightDerivedPushforward.obj M)

/-- The upper-right object `(Rf_*(K ⊗ L) ⊗ Rf_* M)` in the associativity square for the relative
cup product. -/
private abbrev relativeCupProductAssociativityUpperRight
    (rightDerivedPushforward : ModuleDerived X ⥤ ModuleDerived Y)
    (tensorSource : ModuleDerived X ⥤ ModuleDerived X ⥤ ModuleDerived X)
    (tensorTarget : ModuleDerived Y ⥤ ModuleDerived Y ⥤ ModuleDerived Y)
    (K L M : ModuleDerived X) : ModuleDerived Y :=
  tensorTargetObj tensorTarget
    (rightDerivedPushforward.obj (tensorSourceObj tensorSource K L))
    (rightDerivedPushforward.obj M)

/-- The lower-left object `(Rf_* K ⊗ Rf_*(L ⊗ M))` in the associativity square for the relative
cup product. -/
private abbrev relativeCupProductAssociativityLowerLeft
    (rightDerivedPushforward : ModuleDerived X ⥤ ModuleDerived Y)
    (tensorSource : ModuleDerived X ⥤ ModuleDerived X ⥤ ModuleDerived X)
    (tensorTarget : ModuleDerived Y ⥤ ModuleDerived Y ⥤ ModuleDerived Y)
    (K L M : ModuleDerived X) : ModuleDerived Y :=
  tensorTargetObj tensorTarget
    (rightDerivedPushforward.obj K)
    (rightDerivedPushforward.obj (tensorSourceObj tensorSource L M))

/-- The common target object `Rf_*(K ⊗ (L ⊗ M))` in the associativity square for the relative cup
product. -/
private abbrev relativeCupProductAssociativityTarget
    (rightDerivedPushforward : ModuleDerived X ⥤ ModuleDerived Y)
    (tensorSource : ModuleDerived X ⥤ ModuleDerived X ⥤ ModuleDerived X)
    (K L M : ModuleDerived X) : ModuleDerived Y :=
  rightDerivedPushforward.obj
    (tensorSourceObj tensorSource K (tensorSourceObj tensorSource L M))

/-- The top horizontal morphism, obtained by cupping first in the pair `(K, L)`. -/
private abbrev relativeCupProductAssociativityTopMap
    (K L M : ModuleDerived X) :
    relativeCupProductAssociativitySource (modulePushforwardDerived f) tensorTarget K L M ⟶
      relativeCupProductAssociativityUpperRight
        (modulePushforwardDerived f) tensorSource tensorTarget K L M :=
  (tensorTarget.obj ((modulePushforwardDerived f).obj M)).map
    (relativeCupProductMap f tensorSource tensorTarget adj pullbackTensorComparison K L)

/-- The left vertical morphism, obtained from the target-side tensor associator and cupping first
in the pair `(L, M)`. -/
private abbrev relativeCupProductAssociativityLeftMap
    (K L M : ModuleDerived X) :
    relativeCupProductAssociativitySource (modulePushforwardDerived f) tensorTarget K L M ⟶
      relativeCupProductAssociativityLowerLeft
        (modulePushforwardDerived f) tensorSource tensorTarget K L M :=
  (tensorAssocTarget
      ((modulePushforwardDerived f).obj K)
      ((modulePushforwardDerived f).obj L)
      ((modulePushforwardDerived f).obj M)).hom ≫
    (tensorTarget.map
      (relativeCupProductMap f tensorSource tensorTarget adj pullbackTensorComparison L M)).app
        ((modulePushforwardDerived f).obj K)

/-- The right vertical morphism, obtained by cupping `(K ⊗ L)` with `M` and then inserting the
source-side tensor associator. -/
private abbrev relativeCupProductAssociativityRightMap
    (K L M : ModuleDerived X) :
    relativeCupProductAssociativityUpperRight
        (modulePushforwardDerived f) tensorSource tensorTarget K L M ⟶
      relativeCupProductAssociativityTarget (modulePushforwardDerived f) tensorSource K L M :=
  relativeCupProductMap
      f tensorSource tensorTarget adj pullbackTensorComparison
      (tensorSourceObj tensorSource K L) M ≫
    (modulePushforwardDerived f).map (tensorAssocSource K L M).hom

/-- The bottom horizontal morphism, obtained by cupping first in the pair `(L, M)`. -/
private abbrev relativeCupProductAssociativityBottomMap
    (K L M : ModuleDerived X) :
    relativeCupProductAssociativityLowerLeft
        (modulePushforwardDerived f) tensorSource tensorTarget K L M ⟶
      relativeCupProductAssociativityTarget (modulePushforwardDerived f) tensorSource K L M :=
  relativeCupProductMap
    f tensorSource tensorTarget adj pullbackTensorComparison
    K (tensorSourceObj tensorSource L M)

-- Proof sketch: transpose both routes across the adjunction `Lf^* ⊣ Rf_*`. Both become the same
-- map `Lf^*((Rf_* K ⊗ Rf_* L) ⊗ Rf_* M) ⟶ K ⊗ (L ⊗ M)`, built from the pullback-tensor
-- comparison, the chosen tensor associators, and the three counit maps `Lf^* Rf_* ⟶ 𝟭`.
/-- Lemma 21.33.2: the relative cup product of Remark 21.19.7 is associative. After inserting the
chosen tensor associators on the target and source derived categories, the square whose top edge
first cups `(K, L)` and whose left edge first cups `(L, M)` commutes in `D(\mathcal O')`. -/
theorem relativeCupProduct_associative_commSq
    (K L M : ModuleDerived X) :
    CommSq
      (relativeCupProductAssociativityTopMap
        f tensorSource tensorTarget adj pullbackTensorComparison K L M)
      (relativeCupProductAssociativityLeftMap
        f tensorSource tensorTarget adj pullbackTensorComparison
        tensorAssocTarget K L M)
      (relativeCupProductAssociativityRightMap
        f tensorSource tensorTarget adj pullbackTensorComparison
        tensorAssocSource K L M)
      (relativeCupProductAssociativityBottomMap
        f tensorSource tensorTarget adj pullbackTensorComparison K L M) := sorry

end

end RingedSite.Hom

/-! ### Lemma_21_33_3 (from Chap21) -/
open CategoryTheory
open ComplexShape
open CategoryTheory.MonoidalCategory

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

/-- The abelian category of sheaves of modules on the ringed site `X`. -/
abbrev ModuleCat (X : RingedSite.{u, v}) :=
  SheafOfModules X.structureSheaf

/-- The unbounded derived category `D(\mathcal O_X)` of module sheaves on `X`. -/
abbrev ModuleDerived (X : RingedSite.{u, v}) :=
  DerivedCategory (ModuleCat X)

/-- The class of quasi-isomorphisms used to localize the homotopy category of module sheaves on
`X`. -/
abbrev ModuleQis (X : RingedSite.{u, v}) :=
  HomotopyCategory.quasiIso (ModuleCat X) (up ℤ)

/-- The direct-image functor on module sheaves attached to a morphism of ringed sites. -/
abbrev modulePushforward {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y) :
    ModuleCat X ⥤ ModuleCat Y :=
  SheafOfModules.pushforward f.structureSheafMap

/-- The functor on homotopy categories induced by direct image on module sheaves. -/
abbrev modulePushforwardToDerived {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [f.modulePushforward.Additive] :=
  mapHomotopyCategoryToDerived f.modulePushforward

/-- The functor on homotopy categories induced by inverse image on module sheaves. -/
abbrev modulePullbackToDerived {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [f.modulePullback.Additive] :=
  mapHomotopyCategoryToDerived f.modulePullback

/-- The unbounded right derived direct-image functor on module sheaves. -/
noncomputable abbrev modulePushforwardDerived {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [f.modulePushforward.Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)] :
    ModuleDerived X ⥤ ModuleDerived Y :=
  Functor.totalRightDerived (modulePushforwardToDerived f)
    (DerivedCategory.Qh :
      HomotopyCategory (ModuleCat X) (up ℤ) ⥤ DerivedCategory (ModuleCat X))
    (ModuleQis X)

/-- The unbounded left derived inverse-image functor on module sheaves. -/
noncomputable abbrev modulePullbackDerived {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [f.modulePullback.Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)] :
    ModuleDerived Y ⥤ ModuleDerived X :=
  Functor.totalLeftDerived (modulePullbackToDerived f)
    (DerivedCategory.Qh :
      HomotopyCategory (ModuleCat Y) (up ℤ) ⥤ DerivedCategory (ModuleCat Y))
    (ModuleQis Y)

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)

variable [MonoidalCategory (ModuleDerived X)]
variable [BraidedCategory (ModuleDerived X)]
variable [MonoidalCategory (ModuleDerived Y)]
variable [BraidedCategory (ModuleDerived Y)]

variable [f.modulePushforward.Additive]
variable [f.modulePullback.Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]

variable (adj : modulePullbackDerived f ⊣ modulePushforwardDerived f)

variable
  (pullbackTensorComparison :
    ∀ (K L : ModuleDerived Y),
      ((modulePullbackDerived f).obj (((curriedTensor (ModuleDerived Y)).obj L).obj K)) ≅
        (((curriedTensor (ModuleDerived X)).obj ((modulePullbackDerived f).obj L)).obj
          ((modulePullbackDerived f).obj K)))

/-- The morphism adjoint to the relative cup-product map, obtained from the pullback-tensor
comparison together with the counit `Lf^* Rf_* ⟶ \mathrm{id}` on each tensor factor. -/
noncomputable def relativeCupProductAdjointMap
    (K L : ModuleDerived X) :
    ((modulePullbackDerived f).obj
        (((curriedTensor (ModuleDerived Y)).obj ((modulePushforwardDerived f).obj L)).obj
          ((modulePushforwardDerived f).obj K))) ⟶
      (((curriedTensor (ModuleDerived X)).obj L).obj K) :=
  (pullbackTensorComparison
      ((modulePushforwardDerived f).obj K)
      ((modulePushforwardDerived f).obj L)).hom ≫
    (((curriedTensor (ModuleDerived X)).map (adj.counit.app L)).app
      ((modulePullbackDerived f).obj ((modulePushforwardDerived f).obj K))) ≫
    (((curriedTensor (ModuleDerived X)).obj L).map (adj.counit.app K))

/-- The relative cup-product morphism `Rf_* K \otimes^{\mathbf L} Rf_* L ⟶
Rf_*(K \otimes^{\mathbf L} L)`. -/
noncomputable def relativeCupProductMap
    (K L : ModuleDerived X) :
    (((curriedTensor (ModuleDerived Y)).obj ((modulePushforwardDerived f).obj L)).obj
      ((modulePushforwardDerived f).obj K)) ⟶
      (modulePushforwardDerived f).obj (((curriedTensor (ModuleDerived X)).obj L).obj K) :=
  (adj.homEquiv
      (((curriedTensor (ModuleDerived Y)).obj ((modulePushforwardDerived f).obj L)).obj
        ((modulePushforwardDerived f).obj K))
      (((curriedTensor (ModuleDerived X)).obj L).obj K))
    (relativeCupProductAdjointMap f adj pullbackTensorComparison K L)

-- Proof sketch: transpose both composites across the adjunction `Lf^* ⊣ Rf_*`. Naturality of the
-- pullback-tensor comparison with respect to the source and target braidings identifies the two
-- transposes with the same morphism `Lf^*(Rf_* K ⊗ Rf_* L) ⟶ L ⊗ K`, so the displayed square
-- commutes.
/-- Lemma 21.33.3: the relative cup product of Remark 21.19.7 is commutative. In `CommSq` form,
the top edge is the relative cup product
`Rf_* K \otimes^{\mathbf L} Rf_* L ⟶ Rf_*(K \otimes^{\mathbf L} L)`, the left edge is the target
derived-tensor braiding `\psi`, the right edge is `Rf_*` applied to the source derived-tensor
braiding `\psi`, and the bottom edge is the relative cup product with the factors reversed. -/
theorem relativeCupProduct_commutative_commSq
    (K L : ModuleDerived X) :
    CommSq
      (relativeCupProductMap f adj pullbackTensorComparison L K)
      (β_ ((modulePushforwardDerived f).obj K) ((modulePushforwardDerived f).obj L)).hom
      ((modulePushforwardDerived f).map (β_ K L).hom)
      (relativeCupProductMap f adj pullbackTensorComparison K L) := sorry

end

end RingedSite.Hom

/-! ### Lemma_21_33_4 (from Chap21) -/
open CategoryTheory
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

/-- The abelian category of sheaves of modules on the ringed site `X`. -/
abbrev ModuleCat (X : RingedSite.{u, v}) :=
  SheafOfModules X.structureSheaf

/-- The unbounded derived category `D(\mathcal O_X)` of module sheaves on `X`. -/
abbrev ModuleDerived (X : RingedSite.{u, v}) :=
  DerivedCategory (ModuleCat X)

/-- The class of quasi-isomorphisms used to localize the homotopy category of module sheaves on
`X`. -/
abbrev ModuleQis (X : RingedSite.{u, v}) :=
  HomotopyCategory.quasiIso (ModuleCat X) (up ℤ)

/-- The direct-image functor on module sheaves attached to a morphism of ringed sites. -/
abbrev modulePushforward {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y) :
    ModuleCat X ⥤ ModuleCat Y :=
  SheafOfModules.pushforward f.structureSheafMap

/-- Applying an additive functor termwise and then localizing gives a functor from the homotopy
category to the derived category. -/
abbrev mapHomotopyCategoryToDerived
    {A B : Type u} [Category A] [Category B] [Abelian A] [Abelian B] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] :
    HomotopyCategory A (up ℤ) ⥤ DerivedCategory B :=
  F.mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The functor on homotopy categories induced by direct image on module sheaves. -/
abbrev modulePushforwardToDerived {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [f.modulePushforward.Additive] :=
  mapHomotopyCategoryToDerived f.modulePushforward

/-- The functor on homotopy categories induced by inverse image on module sheaves. -/
abbrev modulePullbackToDerived {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [f.modulePullback.Additive] :=
  mapHomotopyCategoryToDerived f.modulePullback

/-- The unbounded right derived direct-image functor on module sheaves. -/
noncomputable abbrev modulePushforwardDerived {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [f.modulePushforward.Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)] :
    ModuleDerived X ⥤ ModuleDerived Y :=
  Functor.totalRightDerived (modulePushforwardToDerived f)
    (DerivedCategory.Qh :
      HomotopyCategory (ModuleCat X) (up ℤ) ⥤ DerivedCategory (ModuleCat X))
    (ModuleQis X)

/-- The unbounded left derived inverse-image functor on module sheaves. -/
noncomputable abbrev modulePullbackDerived {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [f.modulePullback.Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)] :
    ModuleDerived Y ⥤ ModuleDerived X :=
  Functor.totalLeftDerived (modulePullbackToDerived f)
    (DerivedCategory.Qh :
      HomotopyCategory (ModuleCat Y) (up ℤ) ⥤ DerivedCategory (ModuleCat Y))
    (ModuleQis Y)

/-- The morphism adjoint to the relative cup-product map, obtained from the pullback-tensor
comparison together with the counit `Lf^* Rf_* ⟶ \mathrm{id}` on each tensor factor. -/
noncomputable def relativeCupProductAdjointMap
    {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [f.modulePushforward.Additive] [f.modulePullback.Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
    (tensorSource : ModuleDerived X ⥤ ModuleDerived X ⥤ ModuleDerived X)
    (tensorTarget : ModuleDerived Y ⥤ ModuleDerived Y ⥤ ModuleDerived Y)
    (adj : modulePullbackDerived f ⊣ modulePushforwardDerived f)
    (pullbackTensorComparison :
      ∀ (K L : ModuleDerived Y),
        ((modulePullbackDerived f).obj ((tensorTarget.obj L).obj K)) ≅
          ((tensorSource.obj ((modulePullbackDerived f).obj L)).obj
            ((modulePullbackDerived f).obj K)))
    (K L : ModuleDerived X) :
    ((modulePullbackDerived f).obj
        ((tensorTarget.obj ((modulePushforwardDerived f).obj L)).obj
          ((modulePushforwardDerived f).obj K))) ⟶
      ((tensorSource.obj L).obj K) :=
  (pullbackTensorComparison
      ((modulePushforwardDerived f).obj K)
      ((modulePushforwardDerived f).obj L)).hom ≫
    ((tensorSource.map (adj.counit.app L)).app
      ((modulePullbackDerived f).obj ((modulePushforwardDerived f).obj K))) ≫
    ((tensorSource.obj L).map (adj.counit.app K))

/-- The relative cup-product morphism
`Rf_* K \otimes_{\mathcal O_Y}^{\mathbf L} Rf_* L ⟶ Rf_*(K \otimes_{\mathcal O_X}^{\mathbf L} L)`.
-/
noncomputable def relativeCupProductMap
    {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [f.modulePushforward.Additive] [f.modulePullback.Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
    (tensorSource : ModuleDerived X ⥤ ModuleDerived X ⥤ ModuleDerived X)
    (tensorTarget : ModuleDerived Y ⥤ ModuleDerived Y ⥤ ModuleDerived Y)
    (adj : modulePullbackDerived f ⊣ modulePushforwardDerived f)
    (pullbackTensorComparison :
      ∀ (K L : ModuleDerived Y),
        ((modulePullbackDerived f).obj ((tensorTarget.obj L).obj K)) ≅
          ((tensorSource.obj ((modulePullbackDerived f).obj L)).obj
            ((modulePullbackDerived f).obj K)))
    (K L : ModuleDerived X) :
    ((tensorTarget.obj ((modulePushforwardDerived f).obj L)).obj
      ((modulePushforwardDerived f).obj K)) ⟶
      (modulePushforwardDerived f).obj ((tensorSource.obj L).obj K) :=
  (adj.homEquiv
      ((tensorTarget.obj ((modulePushforwardDerived f).obj L)).obj
        ((modulePushforwardDerived f).obj K))
      ((tensorSource.obj L).obj K))
    (relativeCupProductAdjointMap
      f tensorSource tensorTarget adj pullbackTensorComparison K L)

/-- The canonical comparison isomorphism from iterated derived pushforward to the derived
pushforward of the composite morphism. -/
noncomputable abbrev modulePushforwardDerived_compIso
    {X Y Z : RingedSite.{u, v}} (f : RingedSite.Hom X Y) (g : RingedSite.Hom Y Z)
    [f.modulePushforward.Additive] [g.modulePushforward.Additive]
    [(RingedSite.Hom.comp f g).modulePushforward.Additive]
    [f.modulePullback.Additive] [g.modulePullback.Additive]
    [(RingedSite.Hom.comp f g).modulePullback.Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived g) (ModuleQis Y)]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived (RingedSite.Hom.comp f g)) (ModuleQis X)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis Z)]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived (RingedSite.Hom.comp f g)) (ModuleQis Z)]
    (hpull :
      modulePullbackDerived g ⋙ modulePullbackDerived f ≅
        modulePullbackDerived (RingedSite.Hom.comp f g))
    (adj_f : modulePullbackDerived f ⊣ modulePushforwardDerived f)
    (adj_g : modulePullbackDerived g ⊣ modulePushforwardDerived g)
    (adj_comp :
      modulePullbackDerived (RingedSite.Hom.comp f g) ⊣
        modulePushforwardDerived (RingedSite.Hom.comp f g)) :
    modulePushforwardDerived f ⋙ modulePushforwardDerived g ≅
      modulePushforwardDerived (RingedSite.Hom.comp f g) :=
  Adjunction.rightAdjointUniq
    (Adjunction.ofNatIsoLeft (adj_g.comp adj_f) hpull)
    adj_comp

section

variable {X Y Z : RingedSite.{u, v}} (f : RingedSite.Hom X Y) (g : RingedSite.Hom Y Z)

variable [f.modulePushforward.Additive]
variable [g.modulePushforward.Additive]
variable [(RingedSite.Hom.comp f g).modulePushforward.Additive]

variable [f.modulePullback.Additive]
variable [g.modulePullback.Additive]
variable [(RingedSite.Hom.comp f g).modulePullback.Additive]

variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived g) (ModuleQis Y)]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived (RingedSite.Hom.comp f g)) (ModuleQis X)]

variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis Z)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived (RingedSite.Hom.comp f g)) (ModuleQis Z)]

variable (tensorX : ModuleDerived X ⥤ ModuleDerived X ⥤ ModuleDerived X)
variable (tensorY : ModuleDerived Y ⥤ ModuleDerived Y ⥤ ModuleDerived Y)
variable (tensorZ : ModuleDerived Z ⥤ ModuleDerived Z ⥤ ModuleDerived Z)

variable (adj_f : modulePullbackDerived f ⊣ modulePushforwardDerived f)
variable (adj_g : modulePullbackDerived g ⊣ modulePushforwardDerived g)
variable
  (adj_comp :
    modulePullbackDerived (RingedSite.Hom.comp f g) ⊣
      modulePushforwardDerived (RingedSite.Hom.comp f g))

variable
  (hpull :
    modulePullbackDerived g ⋙ modulePullbackDerived f ≅
      modulePullbackDerived (RingedSite.Hom.comp f g))

variable
  (pullbackTensorComparison_f :
    ∀ (K L : ModuleDerived Y),
      ((modulePullbackDerived f).obj ((tensorY.obj L).obj K)) ≅
        ((tensorX.obj ((modulePullbackDerived f).obj L)).obj
          ((modulePullbackDerived f).obj K)))
  (pullbackTensorComparison_g :
    ∀ (K L : ModuleDerived Z),
      ((modulePullbackDerived g).obj ((tensorZ.obj L).obj K)) ≅
        ((tensorY.obj ((modulePullbackDerived g).obj L)).obj
          ((modulePullbackDerived g).obj K)))
  (pullbackTensorComparison_comp :
    ∀ (K L : ModuleDerived Z),
      ((modulePullbackDerived (RingedSite.Hom.comp f g)).obj ((tensorZ.obj L).obj K)) ≅
        ((tensorX.obj ((modulePullbackDerived (RingedSite.Hom.comp f g)).obj L)).obj
          ((modulePullbackDerived (RingedSite.Hom.comp f g)).obj K)))

/-- The top comparison morphism identifying
`R(g \circ f)_* K \otimes^{\mathbf L} R(g \circ f)_* L` with
`Rg_* Rf_* K \otimes^{\mathbf L} Rg_* Rf_* L` via the canonical comparison
`Rg_* \circ Rf_* ≅ R(g \circ f)_*`. -/
private noncomputable abbrev relativeCupProductCompositionTopMap
    (K L : ModuleDerived X) :
    ((tensorZ.obj ((modulePushforwardDerived (RingedSite.Hom.comp f g)).obj L)).obj
      ((modulePushforwardDerived (RingedSite.Hom.comp f g)).obj K)) ⟶
      ((tensorZ.obj ((modulePushforwardDerived g).obj ((modulePushforwardDerived f).obj L))).obj
        ((modulePushforwardDerived g).obj ((modulePushforwardDerived f).obj K))) :=
  let compIso := modulePushforwardDerived_compIso f g hpull adj_f adj_g adj_comp
  ((tensorZ.map (compIso.inv.app L)).app
      ((modulePushforwardDerived (RingedSite.Hom.comp f g)).obj K)) ≫
    ((tensorZ.obj ((modulePushforwardDerived g).obj ((modulePushforwardDerived f).obj L))).map
      (compIso.inv.app K))

/-- The bottom comparison morphism obtained by applying `Rg_*` to the relative cup product for
`f` and then identifying `Rg_* Rf_*` with `R(g \circ f)_*`. -/
private noncomputable abbrev relativeCupProductCompositionBottomMap
    (K L : ModuleDerived X) :
    ((modulePushforwardDerived g).obj
        ((tensorY.obj ((modulePushforwardDerived f).obj L)).obj
          ((modulePushforwardDerived f).obj K))) ⟶
      (modulePushforwardDerived (RingedSite.Hom.comp f g)).obj
        ((tensorX.obj L).obj K) :=
  let compIso := modulePushforwardDerived_compIso f g hpull adj_f adj_g adj_comp
  (modulePushforwardDerived g).map
      (relativeCupProductMap f tensorX tensorY adj_f pullbackTensorComparison_f K L) ≫
    compIso.hom.app ((tensorX.obj L).obj K)

/-- The pullback-side morphism obtained by identifying `L(g \circ f)^*` with `Lf^* Lg^*`,
applying the tensor comparison for `Lg^*`, using the counit for `Lg^* ⊣ Rg_*`, and finally using
the adjoint-side description of the relative cup product for `f`. -/
private noncomputable abbrev relativeCupProductCompositionAdjointMap
    (K L : ModuleDerived X) :
    ((modulePullbackDerived (RingedSite.Hom.comp f g)).obj
        ((tensorZ.obj ((modulePushforwardDerived (RingedSite.Hom.comp f g)).obj L)).obj
          ((modulePushforwardDerived (RingedSite.Hom.comp f g)).obj K))) ⟶
      ((tensorX.obj L).obj K) :=
  (modulePullbackDerived (RingedSite.Hom.comp f g)).map
      (relativeCupProductCompositionTopMap
        f g tensorZ adj_f adj_g adj_comp hpull K L) ≫
    hpull.inv.app
      (((tensorZ.obj ((modulePushforwardDerived g).obj ((modulePushforwardDerived f).obj L))).obj
        ((modulePushforwardDerived g).obj ((modulePushforwardDerived f).obj K)))) ≫
    (modulePullbackDerived f).map
      ((pullbackTensorComparison_g
          ((modulePushforwardDerived g).obj ((modulePushforwardDerived f).obj K))
          ((modulePushforwardDerived g).obj ((modulePushforwardDerived f).obj L))).hom) ≫
    (modulePullbackDerived f).map
      ((((tensorY.map (adj_g.counit.app ((modulePushforwardDerived f).obj L))).app
            ((modulePullbackDerived g).obj
              ((modulePushforwardDerived g).obj ((modulePushforwardDerived f).obj K)))) ≫
          ((tensorY.obj ((modulePushforwardDerived f).obj L)).map
            (adj_g.counit.app ((modulePushforwardDerived f).obj K))))) ≫
    relativeCupProductAdjointMap
      f tensorX tensorY adj_f pullbackTensorComparison_f K L

-- Proof sketch: apply the adjunction bijection for `adj_comp` to both sides. The left-hand side
-- becomes `relativeCupProductAdjointMap` for the composite morphism by
-- `relativeCupProductMap_spec`. The right-hand side becomes
-- `relativeCupProductCompositionAdjointMap`; the compatibility hypothesis identifies these two
-- adjoint-side morphisms, and Lemma `21.19.2` together with Categories, Lemma `4.24.9`, gives the
-- required identification of the counit for the composite adjunction with the composite of the
-- counits for `f` and `g`.
/-- Lemma 21.33.4: for composable morphisms of ringed topoi, formalized here by ringed-site
morphisms `f : X ⟶ Y` and `g : Y ⟶ Z`, the relative cup product of Remark 21.19.7 is compatible
with composition. Concretely, after identifying `R(g \circ f)_*` with `Rg_* \circ Rf_*` by the
comparison isomorphism of Lemma 21.19.2, the relative cup product for `g \circ f` agrees with the
composite obtained from the relative cup product for `g` followed by `Rg_*` applied to the
relative cup product for `f`. -/
theorem relativeCupProduct_comp_eq_iterated
    (hcompat :
      ∀ (K L : ModuleDerived X),
        relativeCupProductAdjointMap
            (RingedSite.Hom.comp f g) tensorX tensorZ adj_comp
            pullbackTensorComparison_comp K L =
          relativeCupProductCompositionAdjointMap
            f g tensorX tensorY tensorZ adj_f adj_g adj_comp hpull
            pullbackTensorComparison_f pullbackTensorComparison_g K L)
    (K L : ModuleDerived X) :
    relativeCupProductMap
        (RingedSite.Hom.comp f g) tensorX tensorZ adj_comp
        pullbackTensorComparison_comp K L =
      relativeCupProductCompositionTopMap
          f g tensorZ adj_f adj_g adj_comp hpull K L ≫
        relativeCupProductMap
          g tensorY tensorZ adj_g pullbackTensorComparison_g
          ((modulePushforwardDerived f).obj K)
          ((modulePushforwardDerived f).obj L) ≫
        relativeCupProductCompositionBottomMap
          f g tensorX tensorY adj_f adj_g adj_comp hpull pullbackTensorComparison_f K L := sorry

end

end RingedSite.Hom

/-! ### Lemma_21_33_5 (from Chap21) -/
open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory

section

variable {DX DX' DY DY' : Type u}
variable [Category.{v} DX] [Category.{v} DX'] [Category.{v} DY] [Category.{v} DY']

variable
  (Lf : DY ⥤ DX)
  (Lf' : DY' ⥤ DX')
  (Lg : DY ⥤ DY')
  (Lg' : DX ⥤ DX')
  (Rf : DX ⥤ DY)
  (Rf' : DX' ⥤ DY')

variable
  (tensorX : DX ⥤ DX ⥤ DX)
  (tensorX' : DX' ⥤ DX' ⥤ DX')
  (tensorY : DY ⥤ DY ⥤ DY)
  (tensorY' : DY' ⥤ DY' ⥤ DY')

variable
  (adj_f : Lf ⊣ Rf)
  (adj_f' : Lf' ⊣ Rf')
  (squareIso : Lg ⋙ Lf' ≅ Lf ⋙ Lg')

/-- The adjoint-side morphism whose transpose is the relative cup product. -/
noncomputable def relativeDerivedCupProductAdjoint
    (pullbackTensorIso :
      ∀ (A B : DY),
        Lf.obj ((tensorY.obj B).obj A) ≅
          ((tensorX.obj (Lf.obj B)).obj (Lf.obj A)))
    (K L : DX) :
    Lf.obj ((tensorY.obj (Rf.obj L)).obj (Rf.obj K)) ⟶
      ((tensorX.obj L).obj K) :=
  (pullbackTensorIso (Rf.obj K) (Rf.obj L)).hom ≫
    ((tensorX.map (adj_f.counit.app L)).app (Lf.obj (Rf.obj K))) ≫
    ((tensorX.obj L).map (adj_f.counit.app K))

/-- The relative cup product obtained by transposing the pullback-side morphism across the
adjunction `Lf^* ⊣ Rf_*`. -/
noncomputable def relativeDerivedCupProduct
    (pullbackTensorIso :
      ∀ (A B : DY),
        Lf.obj ((tensorY.obj B).obj A) ≅
          ((tensorX.obj (Lf.obj B)).obj (Lf.obj A)))
    (K L : DX) :
    ((tensorY.obj (Rf.obj L)).obj (Rf.obj K)) ⟶
      Rf.obj ((tensorX.obj L).obj K) :=
  (adj_f.homEquiv
      ((tensorY.obj (Rf.obj L)).obj (Rf.obj K))
      ((tensorX.obj L).obj K))
    (relativeDerivedCupProductAdjoint
      Lf Rf tensorX tensorY adj_f pullbackTensorIso K L)

/-- A morphism `Lg^* Rf_* K ⟶ R(f')_* L(g')^* K` is a derived base-change map if, after
transposing across the adjunction `L(f')^* ⊣ R(f')_*`, it is the pullback of the counit
`Lf^* Rf_* K ⟶ K` transported through the commutativity isomorphism
`Lg^* \circ L(f')^* ≅ Lf^* \circ L(g')^*`. -/
def IsDerivedBaseChangeMap
    (K : DX)
    (η : Lg.obj (Rf.obj K) ⟶ Rf'.obj (Lg'.obj K)) : Prop :=
  ((adj_f'.homEquiv (Lg.obj (Rf.obj K)) (Lg'.obj K)).symm η) =
    (squareIso.hom.app (Rf.obj K) ≫ Lg'.map (adj_f.counit.app K))

-- Proof sketch: transpose both routes across `adj_f'`. The hypotheses `hηK`, `hηL`, and `hηKL`
-- identify the three base-change morphisms with pullbacks of the counit for `adj_f` through
-- `squareIso`. Unfolding `relativeDerivedCupProduct` on both horizontal arrows then reduces both
-- transposes to the same morphism built from the pullback-tensor comparisons for `f`, `f'`, `g`,
-- and `g'` together with the two counits of `adj_f`.
/-- Lemma 21.33.5: for a commutative square of ringed topoi, the relative cup product is
compatible with base change. In the abstract derived-category formulation used here, after choosing
derived pullback and pushforward functors for the four corners, pullback-tensor comparison
isomorphisms for the four sides, and base-change morphisms for `K`, `L`, and
`K \otimes^{\mathbf L} L`, the two induced morphisms
`Lg^*(Rf_* K \otimes^{\mathbf L} Rf_* L) ⟶ R(f')_*(L(g')^* K \otimes^{\mathbf L} L(g')^* L)`
agree. -/
theorem relativeDerivedCupProduct_baseChange_commutes
    (pullbackTensorIso_f :
      ∀ (A B : DY),
        Lf.obj ((tensorY.obj B).obj A) ≅
          ((tensorX.obj (Lf.obj B)).obj (Lf.obj A)))
    (pullbackTensorIso_f' :
      ∀ (A B : DY'),
        Lf'.obj ((tensorY'.obj B).obj A) ≅
          ((tensorX'.obj (Lf'.obj B)).obj (Lf'.obj A)))
    (pullbackTensorIso_g :
      ∀ (A B : DY),
        Lg.obj ((tensorY.obj B).obj A) ≅
          ((tensorY'.obj (Lg.obj B)).obj (Lg.obj A)))
    (pullbackTensorIso_g' :
      ∀ (A B : DX),
        Lg'.obj ((tensorX.obj B).obj A) ≅
          ((tensorX'.obj (Lg'.obj B)).obj (Lg'.obj A)))
    (K L : DX)
    (ηK : Lg.obj (Rf.obj K) ⟶ Rf'.obj (Lg'.obj K))
    (ηL : Lg.obj (Rf.obj L) ⟶ Rf'.obj (Lg'.obj L))
    (ηKL : Lg.obj (Rf.obj ((tensorX.obj L).obj K)) ⟶
      Rf'.obj (Lg'.obj ((tensorX.obj L).obj K)))
    (hηK :
      IsDerivedBaseChangeMap
        Lf Lf' Lg Lg' Rf Rf' adj_f adj_f' squareIso K ηK)
    (hηL :
      IsDerivedBaseChangeMap
        Lf Lf' Lg Lg' Rf Rf' adj_f adj_f' squareIso L ηL)
    (hηKL :
      IsDerivedBaseChangeMap
        Lf Lf' Lg Lg' Rf Rf' adj_f adj_f' squareIso
        ((tensorX.obj L).obj K) ηKL) :
    Lg.map
        (relativeDerivedCupProduct
          Lf Rf tensorX tensorY adj_f pullbackTensorIso_f K L) ≫
      ηKL ≫
      Rf'.map ((pullbackTensorIso_g' K L).hom) =
    ((pullbackTensorIso_g (Rf.obj K) (Rf.obj L)).hom) ≫
      ((tensorY'.map ηL).app (Lg.obj (Rf.obj K))) ≫
      ((tensorY'.obj (Rf'.obj (Lg'.obj L))).map ηK) ≫
      relativeDerivedCupProduct
        Lf' Rf' tensorX' tensorY' adj_f' pullbackTensorIso_f'
        (Lg'.obj K) (Lg'.obj L) := sorry

end

end CategoryTheory
