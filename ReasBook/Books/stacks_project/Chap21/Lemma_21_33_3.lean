import Mathlib
import stacks_project.Chap13.Lemma_13_16_1
import stacks_project.Chap18.Definition_18_31_1

-- Declarations for this item will be appended below by the statement pipeline.

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
