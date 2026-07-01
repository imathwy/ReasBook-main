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
/-- The category of sheaves of `\mathcal O_X`-modules on a ringed space. -/
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

/-- The direct-image functor on `\mathcal O_X`-modules attached to a morphism of ringed spaces. -/
noncomputable abbrev modulePushforward {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (RingedSpace.Modules X) ⥤ (RingedSpace.Modules Y) :=
  SheafOfModules.pushforward (pushforwardStructureSheafHom f)

/-- The pullback functor on `\mathcal O_Y`-modules attached to a morphism of ringed spaces. -/
noncomputable abbrev modulePullback {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (RingedSpace.Modules Y) ⥤ (RingedSpace.Modules X) :=
  SheafOfModules.pullback (pushforwardStructureSheafHom f)

/-- Applying an additive functor termwise and then localizing gives a functor from the homotopy
category to the derived category. -/
abbrev mapHomotopyCategoryToDerived
    {𝒜 : Type u} {ℬ : Type u}
    [Category 𝒜] [Category ℬ]
    [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory ℬ]
    (F : 𝒜 ⥤ ℬ) [F.Additive] :
    HomotopyCategory 𝒜 (up ℤ) ⥤ DerivedCategory ℬ :=
  F.mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The quasi-isomorphisms in the homotopy category of `\mathcal O_X`-module complexes. -/
abbrev ModuleQis (X : RingedSpace.{u}) :=
  HomotopyCategory.quasiIso (RingedSpace.Modules X) (up ℤ)

/-- The homotopy-category functor used to define the total left derived pullback. -/
abbrev modulePullbackToDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePullback f).Additive] :=
  mapHomotopyCategoryToDerived (modulePullback f)

/-- The derived pullback functor `Lf^* : D(\mathcal O_Y) ⥤ D(\mathcal O_X)`. -/
abbrev modulePullbackDerived
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)] :
    DerivedCategory (RingedSpace.Modules Y) ⥤ DerivedCategory (RingedSpace.Modules X) :=
  Functor.totalLeftDerived (modulePullbackToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules Y))
    (ModuleQis Y)

/-- The cochain-level pushforward functor followed by localization to the derived category. -/
abbrev modulePushforwardToDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePushforward f).Additive] :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules Y) :=
  (modulePushforward f).mapHomologicalComplex (up ℤ) ⋙
    (DerivedCategory.Q : CochainComplex (RingedSpace.Modules Y) ℤ ⥤ DerivedCategory (RingedSpace.Modules Y))

/-- The derived pushforward functor `Rf_* : D(\mathcal O_X) ⥤ D(\mathcal O_Y)`. -/
abbrev moduleDerivedPushforward {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePushforward f).Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f)
      (HomologicalComplex.quasiIso (RingedSpace.Modules X) (up ℤ))] :
    DerivedCategory (RingedSpace.Modules X) ⥤ DerivedCategory (RingedSpace.Modules Y) :=
  (modulePushforwardToDerived f).totalRightDerived
    (DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules X))
    (HomologicalComplex.quasiIso (RingedSpace.Modules X) (up ℤ))

-- Proof sketch: the underived adjunction `f^* ⊣ f_*` for sheaves of modules is
-- `SheafOfModules.pullbackPushforwardAdjunction`. Lemma `20.27.1` gives the total left derived
-- functor `Lf^*`, and the earlier construction of `Rf_*` gives the total right derived functor.
-- Apply the general derived-adjunction formalism to these two derived functors.
/-- Derived pullback and derived pushforward along a morphism of ringed spaces form an adjoint
pair. -/
theorem modulePullbackDerived_pushforward_adjunction
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive] [(modulePushforward f).Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f)
      (HomologicalComplex.quasiIso (RingedSpace.Modules X) (up ℤ))] :
    Nonempty
      ((modulePullbackDerived f : DerivedCategory (RingedSpace.Modules Y) ⥤ DerivedCategory (RingedSpace.Modules X)) ⊣
        (moduleDerivedPushforward f :
          DerivedCategory (RingedSpace.Modules X) ⥤ DerivedCategory (RingedSpace.Modules Y))) := sorry

-- Proof sketch: choose an adjunction from
-- `modulePullbackDerived_pushforward_adjunction f` and apply its `homEquiv` to the pair
-- `(𝒢, ℱ)`. This is exactly the bifunctorial Hom-set identification expressing that
-- `Lf^*` is left adjoint to `Rf_*`.
/-- Lemma 20.28.1: the derived pullback `Lf^*` and derived pushforward `Rf_*` induce a
bifunctorial equivalence
`Hom_{D(\mathcal O_X)}(Lf^* \mathcal G^\bullet, \mathcal F^\bullet) ≃
Hom_{D(\mathcal O_Y)}(\mathcal G^\bullet, Rf_* \mathcal F^\bullet)`. -/
theorem modulePullbackDerived_pushforward_homEquiv
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive] [(modulePushforward f).Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f)
      (HomologicalComplex.quasiIso (RingedSpace.Modules X) (up ℤ))]
    (ℱ : DerivedCategory (RingedSpace.Modules X)) (𝒢 : DerivedCategory (RingedSpace.Modules Y)) :
    Nonempty
      (((modulePullbackDerived f).obj 𝒢 ⟶ ℱ) ≃
        (𝒢 ⟶ (moduleDerivedPushforward f).obj ℱ)) := sorry

end AlgebraicGeometry.RingedSpace
