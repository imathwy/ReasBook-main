import Mathlib
import stacks_project.Chap18.Definition_18_31_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
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

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)

variable [MonoidalCategory (ModuleDerived X)]
variable [BraidedCategory (ModuleDerived X)]
variable [MonoidalClosed (ModuleDerived X)]
variable [MonoidalCategory (ModuleDerived Y)]
variable [BraidedCategory (ModuleDerived Y)]
variable [MonoidalClosed (ModuleDerived Y)]

variable [f.modulePushforward.Additive]
variable [f.modulePullback.Additive]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]

variable (adj : modulePullbackDerived f ⊣ modulePushforwardDerived f)

variable
  (pullbackTensorComparison :
    ∀ (A B : ModuleDerived Y),
      ((modulePullbackDerived f).obj (((curriedTensor (ModuleDerived Y)).obj B).obj A)) ≅
        (((curriedTensor (ModuleDerived X)).obj ((modulePullbackDerived f).obj B)).obj
          ((modulePullbackDerived f).obj A)))

/-- The canonical evaluation morphism
`R\mathcal H\!\mathit{om}(L, K) \otimes_\mathcal O^{\mathbf L} L \to K` in the derived category
of module sheaves on `X`, expressed via the internal-Hom adjunction. -/
private noncomputable abbrev moduleDerivedInternalHomEvaluationMap
    (L K : ModuleDerived X) :
    ((ihom L).obj K ⊗ L) ⟶ K :=
  ((((ihom.adjunction L).homEquiv ((ihom L).obj K) K).symm.trans
      ((β_ ((ihom L).obj K) L).symm.homCongr (Iso.refl K))) :
    (((ihom L).obj K ⟶ (ihom L).obj K) ≃ ((ihom L).obj K ⊗ L ⟶ K)))
    (𝟙 ((ihom L).obj K))

/-- Remark 21.35.10: for a morphism of ringed topoi formalized by the ringed-site morphism `f`
and objects `L`, `K` of `D(\mathcal O_\mathcal C)`, there is a canonical morphism
`Rf_* R\mathcal H\!\mathit{om}(L, K) \to
  R\mathcal H\!\mathit{om}(Rf_* L, Rf_* K)`. It is the adjoint transpose of the composite
obtained by first applying the relative cup product to
`Rf_* R\mathcal H\!\mathit{om}(L, K) \otimes_{\mathcal O_\mathcal D}^{\mathbf L} Rf_* L` and
then applying `Rf_*` to the source-side evaluation map
`R\mathcal H\!\mathit{om}(L, K) \otimes_{\mathcal O_\mathcal C}^{\mathbf L} L \to K`. -/
noncomputable def derivedPushforwardInternalHomComparison
    (L K : ModuleDerived X) :
    (modulePushforwardDerived f).obj ((ihom L).obj K) ⟶
      (ihom ((modulePushforwardDerived f).obj L)).obj ((modulePushforwardDerived f).obj K) :=
  (((((ihom.adjunction ((modulePushforwardDerived f).obj L)).homEquiv
        ((modulePushforwardDerived f).obj ((ihom L).obj K))
        ((modulePushforwardDerived f).obj K)).symm.trans
          ((β_ ((modulePushforwardDerived f).obj ((ihom L).obj K))
              ((modulePushforwardDerived f).obj L)).symm.homCongr
            (Iso.refl ((modulePushforwardDerived f).obj K))))).symm)
    (relativeCupProductMap
        f (curriedTensor (ModuleDerived X)) (curriedTensor (ModuleDerived Y))
        adj pullbackTensorComparison L ((ihom L).obj K) ≫
      (modulePushforwardDerived f).map (moduleDerivedInternalHomEvaluationMap L K))

-- Proof sketch: apply the target-side internal-Hom adjunction `21.35.0.1`. By construction,
-- `derivedPushforwardInternalHomComparison` is defined as the inverse adjoint transpose of the
-- composite consisting of the relative cup product of Remark `21.19.7` followed by `Rf_*`
-- applied to the source-side evaluation map.
/-- The canonical map
`Rf_* R\mathcal H\!\mathit{om}(L, K) \to R\mathcal H\!\mathit{om}(Rf_* L, Rf_* K)` is adjoint to
the composite
`Rf_* R\mathcal H\!\mathit{om}(L, K) \otimes^{\mathbf L} Rf_* L \to
  Rf_*(R\mathcal H\!\mathit{om}(L, K) \otimes^{\mathbf L} L) \to Rf_* K`
described in Remark `21.35.10`. -/
theorem derivedPushforwardInternalHomComparison_spec
    (L K : ModuleDerived X) :
    ((((ihom.adjunction ((modulePushforwardDerived f).obj L)).homEquiv
          ((modulePushforwardDerived f).obj ((ihom L).obj K))
          ((modulePushforwardDerived f).obj K)).symm.trans
        ((β_ ((modulePushforwardDerived f).obj ((ihom L).obj K))
            ((modulePushforwardDerived f).obj L)).symm.homCongr
          (Iso.refl ((modulePushforwardDerived f).obj K))))
      (derivedPushforwardInternalHomComparison f adj pullbackTensorComparison L K)) =
      relativeCupProductMap
          f (curriedTensor (ModuleDerived X)) (curriedTensor (ModuleDerived Y))
          adj pullbackTensorComparison L ((ihom L).obj K) ≫
        (modulePushforwardDerived f).map (moduleDerivedInternalHomEvaluationMap L K) :=
  sorry

end

end RingedSite.Hom
