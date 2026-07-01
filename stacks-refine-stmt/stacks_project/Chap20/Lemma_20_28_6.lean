import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The structure sheaf of a ringed space, regarded as a sheaf of not-necessarily-commutative
rings. -/
/-- The category of sheaves of `\mathcal O_X`-modules on a ringed space `X`. -/
/-- The structure-sheaf morphism `\mathcal O_Y \to f_*\mathcal O_X` attached to a morphism of
ringed spaces. -/
noncomputable abbrev commRingSheafPushforwardMap {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf :=
  ⟨f.hom.c⟩

/-- The structure-sheaf morphism of a ringed-space morphism after forgetting commutativity. -/
noncomputable abbrev pushforwardStructureSheafHom {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (RingedSpace.ringCatSheaf Y) ⟶
      (TopCat.Sheaf.pushforward RingCat.{u} f.hom.base).obj (RingedSpace.ringCatSheaf X) :=
  (sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat.{u})).map
    (commRingSheafPushforwardMap f)

/-- The direct-image functor on module sheaves induced by a morphism of ringed spaces. -/
noncomputable abbrev modulePushforward {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (RingedSpace.Modules X) ⥤ (RingedSpace.Modules Y) :=
  SheafOfModules.pushforward (pushforwardStructureSheafHom f)

/-- The pullback functor on module sheaves induced by a morphism of ringed spaces. -/
noncomputable abbrev modulePullback {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (RingedSpace.Modules Y) ⥤ (RingedSpace.Modules X) :=
  SheafOfModules.pullback (pushforwardStructureSheafHom f)

/-- The quasi-isomorphisms used to localize the homotopy category of `\mathcal O_X`-modules. -/
abbrev ModuleQis (X : RingedSpace.{u}) :=
  HomotopyCategory.quasiIso (RingedSpace.Modules X) (up ℤ)

/-- The unbounded derived category `D(\mathcal O_X)` of `\mathcal O_X`-module sheaves. -/
abbrev ModuleDerived (X : RingedSpace.{u}) :=
  DerivedCategory (RingedSpace.Modules X)

/-- The localization functor from complexes to the homotopy category. -/
abbrev complexToHomotopy (X : RingedSpace.{u}) :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤ HomotopyCategory (RingedSpace.Modules X) (up ℤ) :=
  HomotopyCategory.quotient (RingedSpace.Modules X) (up ℤ)

/-- The functor on homotopy categories induced by pullback on module sheaves. -/
abbrev modulePullbackHomotopy {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePullback f).Additive] :
    HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ HomotopyCategory (RingedSpace.Modules X) (up ℤ) :=
  (modulePullback f).mapHomotopyCategory (up ℤ)

/-- The functor on homotopy categories induced by pushforward on module sheaves. -/
abbrev modulePushforwardHomotopy {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePushforward f).Additive] :
    HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ HomotopyCategory (RingedSpace.Modules Y) (up ℤ) :=
  (modulePushforward f).mapHomotopyCategory (up ℤ)

/-- The functor on homotopy categories followed by localization that models the underived
pullback on complexes in the derived category. -/
abbrev modulePullbackToDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePullback f).Additive] :
    HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ ModuleDerived X :=
  modulePullbackHomotopy f ⋙ DerivedCategory.Qh

/-- The functor on homotopy categories followed by localization that models the underived
direct image on complexes in the derived category. -/
abbrev modulePushforwardToDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePushforward f).Additive] :
    HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ ModuleDerived Y :=
  modulePushforwardHomotopy f ⋙ DerivedCategory.Qh

/-- The derived pullback functor `Lf^* : D(\mathcal O_Y) ⥤ D(\mathcal O_X)`. -/
abbrev modulePullbackDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)] :
    ModuleDerived Y ⥤ ModuleDerived X :=
  Functor.totalLeftDerived (modulePullbackToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ ModuleDerived Y)
    (ModuleQis Y)

/-- The derived direct-image functor `Rf_* : D(\mathcal O_X) ⥤ D(\mathcal O_Y)`. -/
abbrev moduleDerivedPushforward {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePushforward f).Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)] :
    ModuleDerived X ⥤ ModuleDerived Y :=
  Functor.totalRightDerived (modulePushforwardToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ ModuleDerived X)
    (ModuleQis X)

/-- The canonical comparison `Lf^* \to f^*` on homotopy-category representatives of complexes. -/
noncomputable abbrev derivedPullbackCounit {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)] :
    (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ ModuleDerived Y) ⋙
      modulePullbackDerived f ⟶ modulePullbackToDerived f :=
  Functor.totalLeftDerivedCounit (modulePullbackToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ ModuleDerived Y)
    (ModuleQis Y)

/-- The canonical comparison `f_* \to Rf_*` on homotopy-category representatives of complexes. -/
noncomputable abbrev derivedPushforwardUnit {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePushforward f).Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)] :
    modulePushforwardToDerived f ⟶
      (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ ModuleDerived X) ⋙
        moduleDerivedPushforward f :=
  Functor.totalRightDerivedUnit (modulePushforwardToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ ModuleDerived X)
    (ModuleQis X)

/-- The canonical counit `Lf^* Rf_* \to \mathrm{id}` induced by a chosen homotopy-level adjunction
between pullback and pushforward. -/
noncomputable abbrev derivedPullbackPushforwardCounit
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive] [(modulePushforward f).Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
    (adj : modulePullbackHomotopy f ⊣ modulePushforwardHomotopy f)
    [((moduleDerivedPushforward f) ⋙ (modulePullbackDerived f)).IsRightDerivedFunctor
      (Functor.whiskerRight (derivedPushforwardUnit f) (modulePullbackDerived f) ≫
        (Functor.associator
          (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ ModuleDerived X)
          (moduleDerivedPushforward f) (modulePullbackDerived f)).hom) (ModuleQis X)] :
    moduleDerivedPushforward f ⋙ modulePullbackDerived f ⟶ 𝟭 (ModuleDerived X) :=
  adj.derivedε (ModuleQis X) (derivedPullbackCounit f) (derivedPushforwardUnit f)

-- Proof sketch: specialize `Adjunction.derivedε_fac_app` to the pullback-pushforward adjunction on
-- homotopy categories. The left vertical arrow is `Lf^*` applied to the canonical map
-- `f_* K^\bullet \to Rf_* K^\bullet`, the top horizontal arrow is the counit
-- `Lf^*(f_* K^\bullet) \to f^* f_* K^\bullet`, and the right vertical arrow is the image of the
-- underived adjunction counit `f^* f_* K^\bullet \to K^\bullet` in the derived category.
/-- Lemma 20.28.6: for a morphism of ringed spaces and a complex `K^\bullet`, the square in the
derived category obtained from the comparison `Lf^* \to f^*` on complexes, the comparison
`f_* \to Rf_*` on complexes, and the counit `Lf^* Rf_* \to \mathrm{id}` of the derived adjunction
commutes. The underived right edge is taken with respect to a chosen adjunction on homotopy
categories representing `f^* \dashv f_*`. -/
theorem derived_pullback_pushforward_counit_square_commutes
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive] [(modulePushforward f).Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
    (adj : modulePullbackHomotopy f ⊣ modulePushforwardHomotopy f)
    [((moduleDerivedPushforward f) ⋙ (modulePullbackDerived f)).IsRightDerivedFunctor
      (Functor.whiskerRight (derivedPushforwardUnit f) (modulePullbackDerived f) ≫
        (Functor.associator
          (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ ModuleDerived X)
          (moduleDerivedPushforward f) (modulePullbackDerived f)).hom) (ModuleQis X)]
    (K : CochainComplex (RingedSpace.Modules X) ℤ) :
    (modulePullbackDerived f).map ((derivedPushforwardUnit f).app ((complexToHomotopy X).obj K)) ≫
        (derivedPullbackPushforwardCounit f adj).app
          ((DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ ModuleDerived X).obj
            ((complexToHomotopy X).obj K)) =
      (derivedPullbackCounit f).app
          ((modulePushforwardHomotopy f).obj ((complexToHomotopy X).obj K)) ≫
        (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ ModuleDerived X).map
          (adj.counit.app ((complexToHomotopy X).obj K)) := sorry

end AlgebraicGeometry.RingedSpace
