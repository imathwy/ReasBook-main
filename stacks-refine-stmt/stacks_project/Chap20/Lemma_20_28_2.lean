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

/-- Lemma 20.28.2: for composable morphisms of ringed spaces `f : X ⟶ Y` and `g : Y ⟶ Z`, once
the canonical comparison `Lg^* ⋙ Lf^* ≅ L(g \circ f)^*` and the derived adjunctions are fixed,
the composite derived pushforward `Rf_* ⋙ Rg_*` is canonically isomorphic to the derived
pushforward of the composite morphism `R(g \circ f)_*`. This formalizes the equality
`Rg_* \circ Rf_* = R(g \circ f)_*` on `D(\mathcal O_X)`. -/
noncomputable abbrev moduleDerivedPushforward_compIso
    {X Y Z : RingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [CategoryWithHomology (RingedSpace.Modules Z)]
    [(modulePushforward f).Additive] [(modulePushforward g).Additive]
    [(modulePushforward (f ≫ g)).Additive]
    [(modulePullback f).Additive] [(modulePullback g).Additive]
    [(modulePullback (f ≫ g)).Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f)
      (HomologicalComplex.quasiIso (RingedSpace.Modules X) (up ℤ))]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived g)
      (HomologicalComplex.quasiIso (RingedSpace.Modules Y) (up ℤ))]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived (f ≫ g))
      (HomologicalComplex.quasiIso (RingedSpace.Modules X) (up ℤ))]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis Z)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived (f ≫ g)) (ModuleQis Z)]
    (hpull : modulePullbackDerived g ⋙ modulePullbackDerived f ≅
      modulePullbackDerived (f ≫ g))
    (adj_f : modulePullbackDerived f ⊣ moduleDerivedPushforward f)
    (adj_g : modulePullbackDerived g ⊣ moduleDerivedPushforward g)
    (adj_comp : modulePullbackDerived (f ≫ g) ⊣ moduleDerivedPushforward (f ≫ g)) :
    moduleDerivedPushforward f ⋙ moduleDerivedPushforward g ≅
      moduleDerivedPushforward (f ≫ g) :=
  Adjunction.rightAdjointUniq
    (Adjunction.ofNatIsoLeft (adj_g.comp adj_f) hpull)
    adj_comp

-- Proof sketch: unfold `moduleDerivedPushforward_compIso` and apply the standard formula
-- `Adjunction.rightAdjointUniq_hom_counit` for the uniqueness isomorphism of right adjoints.
/-- The comparison isomorphism from iterated derived pushforward to the derived pushforward of the
composite is characterized by compatibility with the counits of the chosen derived adjunctions. -/
theorem moduleDerivedPushforward_compIso_hom_counit
    {X Y Z : RingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [CategoryWithHomology (RingedSpace.Modules Z)]
    [(modulePushforward f).Additive] [(modulePushforward g).Additive]
    [(modulePushforward (f ≫ g)).Additive]
    [(modulePullback f).Additive] [(modulePullback g).Additive]
    [(modulePullback (f ≫ g)).Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f)
      (HomologicalComplex.quasiIso (RingedSpace.Modules X) (up ℤ))]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived g)
      (HomologicalComplex.quasiIso (RingedSpace.Modules Y) (up ℤ))]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived (f ≫ g))
      (HomologicalComplex.quasiIso (RingedSpace.Modules X) (up ℤ))]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis Z)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived (f ≫ g)) (ModuleQis Z)]
    (hpull : modulePullbackDerived g ⋙ modulePullbackDerived f ≅
      modulePullbackDerived (f ≫ g))
    (adj_f : modulePullbackDerived f ⊣ moduleDerivedPushforward f)
    (adj_g : modulePullbackDerived g ⊣ moduleDerivedPushforward g)
    (adj_comp : modulePullbackDerived (f ≫ g) ⊣ moduleDerivedPushforward (f ≫ g)) :
    Functor.whiskerRight
        (moduleDerivedPushforward_compIso f g hpull adj_f adj_g adj_comp).hom
        (modulePullbackDerived (f ≫ g)) ≫
      adj_comp.counit =
        (Adjunction.ofNatIsoLeft (adj_g.comp adj_f) hpull).counit :=
  sorry

end AlgebraicGeometry.RingedSpace
