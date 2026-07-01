import Mathlib
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
