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
    [(modulePushforward f).Additive] :=
  mapHomotopyCategoryToDerived (modulePushforward f)

/-- The functor on homotopy categories induced by inverse image on module sheaves. -/
abbrev modulePullbackToDerived {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [f.modulePullback.Additive] :=
  mapHomotopyCategoryToDerived f.modulePullback

/-- The unbounded right derived direct-image functor on module sheaves. -/
noncomputable abbrev modulePushforwardDerived {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [(modulePushforward f).Additive]
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

variable [(modulePushforward f).Additive]
variable [f.modulePullback.Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]

variable (tensorSource : ModuleDerived X ⥤ ModuleDerived X ⥤ ModuleDerived X)
variable (tensorTarget : ModuleDerived Y ⥤ ModuleDerived Y ⥤ ModuleDerived Y)
variable (adj : modulePullbackDerived f ⊣ modulePushforwardDerived f)

/- The chosen pullback-tensor comparison for `Lf^*`, expressing compatibility of the derived
pullback with the derived tensor products on the source and target. -/
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

/-- Remark 21.19.7: for a morphism of ringed topoi formalized by the ringed-site morphism `f`,
the relative cup-product morphism
`Rf_* K \otimes_{\mathcal O_Y}^{\mathbf L} Rf_* L ⟶
  Rf_* (K \otimes_{\mathcal O_X}^{\mathbf L} L)`
is the mate, under the derived adjunction `Lf^* ⊣ Rf_*`, of the pullback-tensor comparison
followed by the tensor of the counit maps `Lf^* Rf_* K ⟶ K` and `Lf^* Rf_* L ⟶ L`. -/
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

-- Proof sketch: unfold `relativeCupProductMap`; it is defined by applying `adj.homEquiv` to
-- `relativeCupProductAdjointMap`, so applying the inverse adjunction bijection recovers exactly
-- that composite.
/-- The relative cup-product morphism is adjoint to the map obtained from tensor compatibility of
`Lf^*` with derived tensor products and the counit `Lf^* Rf_* ⟶ \mathrm{id}`. -/
theorem relativeCupProductMap_spec
    (K L : ModuleDerived X) :
    ((adj.homEquiv
        ((tensorTarget.obj ((modulePushforwardDerived f).obj L)).obj
          ((modulePushforwardDerived f).obj K))
        ((tensorSource.obj L).obj K)).symm
      (relativeCupProductMap
        f tensorSource tensorTarget adj pullbackTensorComparison K L)) =
      relativeCupProductAdjointMap
        f tensorSource tensorTarget adj pullbackTensorComparison K L := sorry

end

end RingedSite.Hom
