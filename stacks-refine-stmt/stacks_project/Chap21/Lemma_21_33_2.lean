import Mathlib
import stacks_project.Chap13.Lemma_13_16_1
import stacks_project.Chap18.Definition_18_31_1

-- Declarations for this item will be appended below by the statement pipeline.

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
