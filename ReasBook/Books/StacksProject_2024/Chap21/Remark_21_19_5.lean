import Mathlib
import StacksProject_2024.Chap13.Lemma_13_16_1
import StacksProject_2024.Chap18.Definition_18_31_1

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

/-- A morphism `Lg^* Rf_* K ⟶ R(f')_* L(g')^* K` is an unbounded derived base-change map if, after
transposing along the derived adjunction `L(f')^* ⊣ R(f')_*`, it is the pullback along `Lg'^*` of
the counit `Lf^* Rf_* K ⟶ K`, transported across the canonical commutativity isomorphism
`L(f')^* ∘ Lg^* ≅ L(g')^* ∘ Lf^*`. -/
def IsUnboundedBaseChangeMap
    {X' X Y' Y : RingedSite.{u, v}}
    (g' : RingedSite.Hom X' X) (f' : RingedSite.Hom X' Y')
    (f : RingedSite.Hom X Y) (g : RingedSite.Hom Y' Y)
    [f.modulePushforward.Additive]
    [f'.modulePushforward.Additive]
    [f.modulePullback.Additive]
    [f'.modulePullback.Additive]
    [g.modulePullback.Additive]
    [g'.modulePullback.Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f') (ModuleQis X')]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis Y)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g') (ModuleQis X)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f') (ModuleQis Y')]
    (hpull :
      modulePullbackDerived g ⋙ modulePullbackDerived f' ≅
        modulePullbackDerived f ⋙ modulePullbackDerived g')
    (adj_f : modulePullbackDerived f ⊣ modulePushforwardDerived f)
    (adj_f' : modulePullbackDerived f' ⊣ modulePushforwardDerived f')
    (K : ModuleDerived X)
    (η :
      ((modulePullbackDerived g).obj ((modulePushforwardDerived f).obj K)) ⟶
        ((modulePushforwardDerived f').obj ((modulePullbackDerived g').obj K))) : Prop :=
  ((adj_f'.homEquiv
      ((modulePullbackDerived g).obj ((modulePushforwardDerived f).obj K))
      ((modulePullbackDerived g').obj K)).symm η) =
    (hpull.app ((modulePushforwardDerived f).obj K)).hom ≫
      (modulePullbackDerived g').map (adj_f.counit.app K)

section

variable {X2 X1 X0 Y2 Y1 Y0 : RingedSite.{u, v}}
variable (g1 : RingedSite.Hom X2 X1) (g0 : RingedSite.Hom X1 X0)
variable (f2 : RingedSite.Hom X2 Y2) (f1 : RingedSite.Hom X1 Y1) (f0 : RingedSite.Hom X0 Y0)
variable (h1 : RingedSite.Hom Y2 Y1) (h0 : RingedSite.Hom Y1 Y0)

variable [f0.modulePushforward.Additive]
variable [f1.modulePushforward.Additive]
variable [f2.modulePushforward.Additive]

variable [f0.modulePullback.Additive]
variable [f1.modulePullback.Additive]
variable [f2.modulePullback.Additive]
variable [g0.modulePullback.Additive]
variable [g1.modulePullback.Additive]
variable [h0.modulePullback.Additive]
variable [h1.modulePullback.Additive]
variable [(RingedSite.Hom.comp g1 g0).modulePullback.Additive]
variable [(RingedSite.Hom.comp h1 h0).modulePullback.Additive]

variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f0) (ModuleQis X0)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f1) (ModuleQis X1)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f2) (ModuleQis X2)]

variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f0) (ModuleQis Y0)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f1) (ModuleQis Y1)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f2) (ModuleQis Y2)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g0) (ModuleQis X0)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g1) (ModuleQis X1)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived h0) (ModuleQis Y0)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived h1) (ModuleQis Y1)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived (RingedSite.Hom.comp g1 g0)) (ModuleQis X0)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived (RingedSite.Hom.comp h1 h0)) (ModuleQis Y0)]

/-- The pullback commutativity isomorphisms for two horizontally composable squares combine to the
pullback commutativity isomorphism for the outer rectangle. -/
noncomputable def horizontalCompositePullbackIso
    (hpull0 :
      modulePullbackDerived h0 ⋙ modulePullbackDerived f1 ≅
        modulePullbackDerived f0 ⋙ modulePullbackDerived g0)
    (hpull1 :
      modulePullbackDerived h1 ⋙ modulePullbackDerived f2 ≅
        modulePullbackDerived f1 ⋙ modulePullbackDerived g1)
    (hcomp :
      modulePullbackDerived (RingedSite.Hom.comp h1 h0) ≅
        modulePullbackDerived h0 ⋙ modulePullbackDerived h1)
    (gcomp :
      modulePullbackDerived (RingedSite.Hom.comp g1 g0) ≅
        modulePullbackDerived g0 ⋙ modulePullbackDerived g1) :
    modulePullbackDerived (RingedSite.Hom.comp h1 h0) ⋙ modulePullbackDerived f2 ≅
      modulePullbackDerived f0 ⋙ modulePullbackDerived (RingedSite.Hom.comp g1 g0) :=
  Functor.isoWhiskerRight hcomp (modulePullbackDerived f2) ≪≫
    Functor.associator (modulePullbackDerived h0) (modulePullbackDerived h1)
      (modulePullbackDerived f2) ≪≫
    Functor.isoWhiskerLeft (modulePullbackDerived h0) hpull1 ≪≫
    (Functor.associator (modulePullbackDerived h0) (modulePullbackDerived f1)
      (modulePullbackDerived g1)).symm ≪≫
    Functor.isoWhiskerRight hpull0 (modulePullbackDerived g1) ≪≫
    Functor.associator (modulePullbackDerived f0) (modulePullbackDerived g0)
      (modulePullbackDerived g1) ≪≫
    Functor.isoWhiskerLeft (modulePullbackDerived f0) gcomp.symm

/-- The composite of the two base-change morphisms associated to adjacent squares, rewritten as a
morphism from the outer pullback of `Rf0_*` to the outer pushforward of the iterated pullback. -/
noncomputable def horizontalCompositeUnboundedBaseChangeMap
    (K : ModuleDerived X0)
    (η0 :
      ((modulePullbackDerived h0).obj ((modulePushforwardDerived f0).obj K)) ⟶
        ((modulePushforwardDerived f1).obj ((modulePullbackDerived g0).obj K)))
    (η1 :
      ((modulePullbackDerived h1).obj
          ((modulePushforwardDerived f1).obj ((modulePullbackDerived g0).obj K))) ⟶
        ((modulePushforwardDerived f2).obj
          ((modulePullbackDerived g1).obj ((modulePullbackDerived g0).obj K))))
    (hcomp :
      modulePullbackDerived (RingedSite.Hom.comp h1 h0) ≅
        modulePullbackDerived h0 ⋙ modulePullbackDerived h1)
    (gcomp :
      modulePullbackDerived (RingedSite.Hom.comp g1 g0) ≅
        modulePullbackDerived g0 ⋙ modulePullbackDerived g1) :
    ((modulePullbackDerived (RingedSite.Hom.comp h1 h0)).obj
        ((modulePushforwardDerived f0).obj K)) ⟶
      ((modulePushforwardDerived f2).obj
        ((modulePullbackDerived (RingedSite.Hom.comp g1 g0)).obj K)) :=
  (hcomp.app ((modulePushforwardDerived f0).obj K)).hom ≫
    (modulePullbackDerived h1).map η0 ≫
    η1 ≫
    (modulePushforwardDerived f2).map ((gcomp.symm.app K).hom)

-- Proof sketch: expand the outer pullback commutativity isomorphism by composing the two square
-- isomorphisms with associators, then transpose the composite morphism along the adjunction
-- `L(f2)^* ⊣ R(f2)_*`. The hypotheses `hη0` and `hη1` identify the two intermediate pieces with
-- the counits for the right and left squares, and the resulting composite is exactly the mate for
-- the outer rectangle.
/-- Remark 21.19.5: for two horizontally composable squares of ringed topoi, the composition of
the base-change maps from Remark `21.19.3` is the base-change map for the outer rectangle. -/
theorem horizontalComposite_isUnboundedBaseChangeMap
    (hpull0 :
      modulePullbackDerived h0 ⋙ modulePullbackDerived f1 ≅
        modulePullbackDerived f0 ⋙ modulePullbackDerived g0)
    (hpull1 :
      modulePullbackDerived h1 ⋙ modulePullbackDerived f2 ≅
        modulePullbackDerived f1 ⋙ modulePullbackDerived g1)
    (hcomp :
      modulePullbackDerived (RingedSite.Hom.comp h1 h0) ≅
        modulePullbackDerived h0 ⋙ modulePullbackDerived h1)
    (gcomp :
      modulePullbackDerived (RingedSite.Hom.comp g1 g0) ≅
        modulePullbackDerived g0 ⋙ modulePullbackDerived g1)
    (adj_f0 : modulePullbackDerived f0 ⊣ modulePushforwardDerived f0)
    (adj_f1 : modulePullbackDerived f1 ⊣ modulePushforwardDerived f1)
    (adj_f2 : modulePullbackDerived f2 ⊣ modulePushforwardDerived f2)
    (K : ModuleDerived X0)
    (η0 :
      ((modulePullbackDerived h0).obj ((modulePushforwardDerived f0).obj K)) ⟶
        ((modulePushforwardDerived f1).obj ((modulePullbackDerived g0).obj K)))
    (η1 :
      ((modulePullbackDerived h1).obj
          ((modulePushforwardDerived f1).obj ((modulePullbackDerived g0).obj K))) ⟶
        ((modulePushforwardDerived f2).obj
          ((modulePullbackDerived g1).obj ((modulePullbackDerived g0).obj K))))
    (hη0 : IsUnboundedBaseChangeMap g0 f1 f0 h0 hpull0 adj_f0 adj_f1 K η0)
    (hη1 :
      IsUnboundedBaseChangeMap g1 f2 f1 h1 hpull1 adj_f1 adj_f2
        ((modulePullbackDerived g0).obj K) η1) :
    IsUnboundedBaseChangeMap
      (RingedSite.Hom.comp g1 g0)
      f2
      f0
      (RingedSite.Hom.comp h1 h0)
      (horizontalCompositePullbackIso g1 g0 f2 f1 f0 h1 h0 hpull0 hpull1 hcomp gcomp)
      adj_f0
      adj_f2
      K
      (horizontalCompositeUnboundedBaseChangeMap
        g1 g0 f2 f1 f0 h1 h0 K η0 η1 hcomp gcomp) := sorry

end

end RingedSite.Hom
