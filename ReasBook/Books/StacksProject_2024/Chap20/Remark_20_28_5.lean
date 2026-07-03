import Mathlib
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import StacksProject_2024.Chap20.«20_3_0_4»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

attribute [local instance] HasDerivedCategory.standard

/-- The pullback functor on `\mathcal O_Y`-modules attached to a morphism of ringed spaces. -/
noncomputable abbrev ringedSpaceModulePullback {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    SheafOfModules ((RingedSpace.ringCatSheaf Y)) ⥤
      SheafOfModules ((RingedSpace.ringCatSheaf X)) :=
  SheafOfModules.pullback (ringedSpacePushforwardStructureSheafHom f)

/-- The category of sheaves of `\mathcal O_X`-modules on a ringed space. -/
/-- The quasi-isomorphisms in the homotopy category of unbounded complexes of
`\mathcal O_X`-modules on a ringed space. -/
abbrev ModuleQis (X : RingedSpace.{u}) :=
  HomotopyCategory.quasiIso (RingedSpace.Modules X) (up ℤ)

/-- The unbounded derived category `D(\mathcal O_X)` of a ringed space. -/
abbrev ModuleDerived (X : RingedSpace.{u}) :=
  DerivedCategory (RingedSpace.Modules X)

/-- The functor on homotopy categories induced by direct image on module sheaves. -/
abbrev modulePushforwardToDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(ringedSpaceModulePushforward f).Additive] :
    HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ ModuleDerived Y :=
  (ringedSpaceModulePushforward f).mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The functor on homotopy categories induced by inverse image on module sheaves. -/
abbrev modulePullbackToDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(ringedSpaceModulePullback f).Additive] :
    HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ ModuleDerived X :=
  (ringedSpaceModulePullback f).mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The unbounded derived direct image functor `Rf_*` on module sheaves over ringed spaces. -/
abbrev modulePushforwardDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(ringedSpaceModulePushforward f).Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)] :
    ModuleDerived X ⥤ ModuleDerived Y :=
  Functor.totalRightDerived (modulePushforwardToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ ModuleDerived X)
    (ModuleQis X)

/-- The unbounded derived inverse-image functor `Lf^*`. -/
abbrev modulePullbackDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(ringedSpaceModulePullback f).Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)] :
    ModuleDerived Y ⥤ ModuleDerived X :=
  Functor.totalLeftDerived (modulePullbackToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ ModuleDerived Y)
    (ModuleQis Y)

/-- The source object `Lg^* Rf_* K` of an unbounded derived base-change morphism. -/
abbrev derivedBaseChangeSource {X S S' : RingedSpace.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [(ringedSpaceModulePushforward f).Additive]
    [(ringedSpaceModulePullback g).Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis S)]
    (K : ModuleDerived X) : ModuleDerived S' :=
  (modulePullbackDerived g).obj ((modulePushforwardDerived f).obj K)

/-- The target object `R(f')_* L(g')^* K` of an unbounded derived base-change morphism. -/
abbrev derivedBaseChangeTarget {X X' S' : RingedSpace.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
    [(ringedSpaceModulePullback g').Additive]
    [(ringedSpaceModulePushforward f').Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g') (ModuleQis X)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f') (ModuleQis X')]
    (K : ModuleDerived X) : ModuleDerived S' :=
  (modulePushforwardDerived f').obj ((modulePullbackDerived g').obj K)

/-- A morphism `Lg^* Rf_* K ⟶ R(f')_* L(g')^* K` is an unbounded derived base-change map if,
after transposing across `L(f')^* ⊣ R(f')_*`, it is the pullback of the counit
`Lf^* Rf_* K ⟶ K` transported along the chosen pullback-commutativity isomorphism. -/
def IsUnboundedBaseChangeMap
    {X' X Y' Y : RingedSpace.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y)
    [(ringedSpaceModulePushforward f).Additive]
    [(ringedSpaceModulePushforward f').Additive]
    [(ringedSpaceModulePullback f).Additive]
    [(ringedSpaceModulePullback f').Additive]
    [(ringedSpaceModulePullback g).Additive]
    [(ringedSpaceModulePullback g').Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f') (ModuleQis X')]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis Y)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g') (ModuleQis X)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f') (ModuleQis Y')]
    (hpull : modulePullbackDerived g ⋙ modulePullbackDerived f' ≅
      modulePullbackDerived f ⋙ modulePullbackDerived g')
    (adj_f : modulePullbackDerived f ⊣ modulePushforwardDerived f)
    (adj_f' : modulePullbackDerived f' ⊣ modulePushforwardDerived f')
    (K : ModuleDerived X)
    (η : derivedBaseChangeSource f g K ⟶ derivedBaseChangeTarget g' f' K) : Prop :=
  ((adj_f'.homEquiv (derivedBaseChangeSource f g K) ((modulePullbackDerived g').obj K)).symm η) =
    (hpull.hom.app ((modulePushforwardDerived f).obj K) ≫
      (modulePullbackDerived g').map (adj_f.counit.app K))

section

variable {X'' X' X Y'' Y' Y : RingedSpace.{u}}
variable (g' : X'' ⟶ X') (g : X' ⟶ X)
variable (f'' : X'' ⟶ Y'') (f' : X' ⟶ Y') (f : X ⟶ Y)
variable (h' : Y'' ⟶ Y') (h : Y' ⟶ Y)

variable [(ringedSpaceModulePullback g').Additive]
variable [(ringedSpaceModulePullback g).Additive]
variable [(ringedSpaceModulePullback (g' ≫ g)).Additive]
variable [(ringedSpaceModulePullback h').Additive]
variable [(ringedSpaceModulePullback h).Additive]
variable [(ringedSpaceModulePullback (h' ≫ h)).Additive]
variable [(ringedSpaceModulePullback f'').Additive]
variable [(ringedSpaceModulePullback f').Additive]
variable [(ringedSpaceModulePullback f).Additive]
variable [(ringedSpaceModulePushforward f'').Additive]
variable [(ringedSpaceModulePushforward f').Additive]
variable [(ringedSpaceModulePushforward f).Additive]

variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g') (ModuleQis X')]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis X)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived (g' ≫ g)) (ModuleQis X)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived h') (ModuleQis Y')]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived h) (ModuleQis Y)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived (h' ≫ h)) (ModuleQis Y)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f'') (ModuleQis Y'')]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f') (ModuleQis Y')]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f'') (ModuleQis X'')]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f') (ModuleQis X')]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]

/-- The pullback commutativity isomorphisms for two horizontally composable squares combine to
the pullback commutativity isomorphism for the outer rectangle. -/
def horizontalCompositePullbackIso
    (hpull₀ : modulePullbackDerived h ⋙ modulePullbackDerived f' ≅
      modulePullbackDerived f ⋙ modulePullbackDerived g)
    (hpull₁ : modulePullbackDerived h' ⋙ modulePullbackDerived f'' ≅
      modulePullbackDerived f' ⋙ modulePullbackDerived g')
    (hcomp : modulePullbackDerived (h' ≫ h) ≅
      modulePullbackDerived h ⋙ modulePullbackDerived h')
    (gcomp : modulePullbackDerived (g' ≫ g) ≅
      modulePullbackDerived g ⋙ modulePullbackDerived g') :
    modulePullbackDerived (h' ≫ h) ⋙ modulePullbackDerived f'' ≅
      modulePullbackDerived f ⋙ modulePullbackDerived (g' ≫ g) :=
  Functor.isoWhiskerRight hcomp (modulePullbackDerived f'') ≪≫
    Functor.associator (modulePullbackDerived h) (modulePullbackDerived h')
      (modulePullbackDerived f'') ≪≫
    Functor.isoWhiskerLeft (modulePullbackDerived h) hpull₁ ≪≫
    (Functor.associator (modulePullbackDerived h) (modulePullbackDerived f')
      (modulePullbackDerived g')).symm ≪≫
    Functor.isoWhiskerRight hpull₀ (modulePullbackDerived g') ≪≫
    Functor.associator (modulePullbackDerived f) (modulePullbackDerived g)
      (modulePullbackDerived g') ≪≫
    Functor.isoWhiskerLeft (modulePullbackDerived f) gcomp.symm

/-- The composite of the two base-change maps associated to adjacent squares, rewritten as a
morphism from the outer pullback of `Rf_*` to the outer pushforward of the iterated pullback. -/
def horizontalCompositeUnboundedBaseChangeMap
    (K : ModuleDerived X)
    (η₀ : derivedBaseChangeSource f h K ⟶ derivedBaseChangeTarget g f' K)
    (η₁ :
      derivedBaseChangeSource f' h' ((modulePullbackDerived g).obj K) ⟶
        derivedBaseChangeTarget g' f'' ((modulePullbackDerived g).obj K))
    (hcomp : modulePullbackDerived (h' ≫ h) ≅
      modulePullbackDerived h ⋙ modulePullbackDerived h')
    (gcomp : modulePullbackDerived (g' ≫ g) ≅
      modulePullbackDerived g ⋙ modulePullbackDerived g') :
    derivedBaseChangeSource f (h' ≫ h) K ⟶ derivedBaseChangeTarget (g' ≫ g) f'' K :=
  (hcomp.hom.app ((modulePushforwardDerived f).obj K)) ≫
    (modulePullbackDerived h').map η₀ ≫
    η₁ ≫
    (modulePushforwardDerived f'').map (gcomp.inv.app K)

-- Proof sketch: expand the outer pullback commutativity isomorphism by composing the two square
-- isomorphisms with associators, then transpose the composite morphism along the adjunction
-- `L(f'')^* ⊣ R(f'')_*`. The hypotheses identifying `η₀` and `η₁` as base-change maps reduce the
-- transpose to the counit expression for the outer rectangle.
/-- Remark 20.28.5: for two composable squares of ringed spaces, the base-change maps of Remark
20.28.3 for the two inner squares compose to the base-change map for the outer rectangle. -/
theorem horizontalComposite_isUnboundedBaseChangeMap
    (hpull₀ : modulePullbackDerived h ⋙ modulePullbackDerived f' ≅
      modulePullbackDerived f ⋙ modulePullbackDerived g)
    (hpull₁ : modulePullbackDerived h' ⋙ modulePullbackDerived f'' ≅
      modulePullbackDerived f' ⋙ modulePullbackDerived g')
    (hcomp : modulePullbackDerived (h' ≫ h) ≅
      modulePullbackDerived h ⋙ modulePullbackDerived h')
    (gcomp : modulePullbackDerived (g' ≫ g) ≅
      modulePullbackDerived g ⋙ modulePullbackDerived g')
    (adj_f : modulePullbackDerived f ⊣ modulePushforwardDerived f)
    (adj_f' : modulePullbackDerived f' ⊣ modulePushforwardDerived f')
    (adj_f'' : modulePullbackDerived f'' ⊣ modulePushforwardDerived f'')
    (K : ModuleDerived X)
    (η₀ : derivedBaseChangeSource f h K ⟶ derivedBaseChangeTarget g f' K)
    (η₁ :
      derivedBaseChangeSource f' h' ((modulePullbackDerived g).obj K) ⟶
        derivedBaseChangeTarget g' f'' ((modulePullbackDerived g).obj K))
    (hη₀ : IsUnboundedBaseChangeMap g f' f h hpull₀ adj_f adj_f' K η₀)
    (hη₁ :
      IsUnboundedBaseChangeMap g' f'' f' h' hpull₁ adj_f' adj_f''
        ((modulePullbackDerived g).obj K) η₁) :
    IsUnboundedBaseChangeMap
      (g' ≫ g)
      f''
      f
      (h' ≫ h)
      (horizontalCompositePullbackIso g' g f'' f' f h' h hpull₀ hpull₁ hcomp gcomp)
      adj_f
      adj_f''
      K
      (horizontalCompositeUnboundedBaseChangeMap g' g f'' f' f h' h K η₀ η₁ hcomp gcomp) := sorry

end

end AlgebraicGeometry.RingedSpace
