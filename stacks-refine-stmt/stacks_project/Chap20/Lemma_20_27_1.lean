import Mathlib
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Localization.Triangulated

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

/-- The pullback functor on module sheaves induced by a morphism of ringed spaces. -/
noncomputable abbrev modulePullback {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (RingedSpace.Modules Y) ⥤ (RingedSpace.Modules X) :=
  SheafOfModules.pullback (pushforwardStructureSheafHom f)

/-- The functor `K(\mathcal A) ⥤ D(\mathcal B)` obtained by applying an additive functor termwise
and then passing to the derived category. -/
abbrev mapHomotopyCategoryToDerived
    {𝒜 : Type u} {ℬ : Type u}
    [Category 𝒜] [Category ℬ]
    [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory ℬ]
    (F : 𝒜 ⥤ ℬ) [F.Additive] :
    HomotopyCategory 𝒜 (up ℤ) ⥤ DerivedCategory ℬ :=
  F.mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The quasi-isomorphisms used to localize the homotopy category of `\mathcal O_X`-modules. -/
abbrev ModuleQis (X : RingedSpace.{u}) :=
  HomotopyCategory.quasiIso (RingedSpace.Modules X) (up ℤ)

/-- The unbounded derived category `D(\mathcal O_X)` of `\mathcal O_X`-module sheaves on a
ringed space `X`, formalized as the localization of the homotopy category at quasi-isomorphisms.
-/
abbrev ModuleDerived (X : RingedSpace.{u}) :=
  (ModuleQis X).Localization

/-- The functor `K(\mathcal O_Y) ⥤ D(\mathcal O_X)` obtained by applying `f^*` termwise and then
passing to the derived category. -/
abbrev modulePullbackToDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePullback f).Additive] :=
  mapHomotopyCategoryToDerived (modulePullback f)

-- Proof sketch: apply Lemma `13.14.15` to the triangulated functor
-- `modulePullbackToDerived f : K(\mathcal O_Y) ⥤ D(\mathcal O_X)` with the subset of K-flat
-- complexes. Lemma `20.26.12` gives enough K-flat resolutions, Lemma `20.26.8` shows pullback
-- preserves K-flatness, and Lemma `20.26.13` shows pullback sends quasi-isomorphisms between
-- K-flat complexes to quasi-isomorphisms. Equation `13.14.9.1` then identifies the resulting
-- total left derived functor with the desired `Lf^*`.
/-- Lemma 20.27.1: the pullback functor on homotopy categories
`K(\mathcal O_Y) ⥤ D(\mathcal O_X)` obtained from `f^*` has an everywhere defined total left
derived functor with respect to quasi-isomorphisms. Equivalently, the construction via K-flat
resolutions is independent of choices and defines the derived pullback functor
`Lf^* : D(\mathcal O_Y) ⥤ D(\mathcal O_X)`. -/
theorem modulePullbackToDerived_hasLeftDerivedFunctor
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive] :
    Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y) := sorry

/-- The canonical left-derived-functor instance for homotopy-category pullback. -/
instance instHasLeftDerivedFunctorModulePullbackToDerived
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive] :
    Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y) :=
  modulePullbackToDerived_hasLeftDerivedFunctor f

/-- The derived pullback functor `Lf^* : D(\mathcal O_Y) ⥤ D(\mathcal O_X)`. -/
abbrev modulePullbackDerived
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive] :
    ModuleDerived Y ⥤ DerivedCategory (RingedSpace.Modules X) :=
  Functor.totalLeftDerived (modulePullbackToDerived f)
    (ModuleQis Y).Q
    (ModuleQis Y)

/-- The canonical functor from cochain complexes of `\mathcal O_X`-modules to the derived
category `D(\mathcal O_X)`. -/
abbrev complexToDerived (X : RingedSpace.{u}) :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules X) :=
  HomotopyCategory.quotient (RingedSpace.Modules X) (up ℤ) ⋙
    (DerivedCategory.Qh :
      HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules X))

/-- Short notation for the derived pullback functor `Lf^*`. -/
abbrev Lf
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive] :
    ModuleDerived Y ⥤ DerivedCategory (RingedSpace.Modules X) :=
  modulePullbackDerived f

-- Proof sketch: the underived functor `modulePullbackToDerived f` commutes with the shift on the
-- homotopy category, and the universal property of total left derived functors transports this
-- shift compatibility to `modulePullbackDerived f`.
/-- The derived pullback functor commutes with the triangulated shift. -/
noncomputable instance modulePullbackDerived_commShift
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [HasShift (ModuleDerived Y) ℤ]
    [(modulePullback f).Additive] :
    (modulePullbackDerived f).CommShift ℤ := sorry

-- Proof sketch: `modulePullbackToDerived f` is an exact functor of triangulated categories from
-- the homotopy category to the derived category, and the exactness comparison for total left
-- derived functors upgrades this to the derived pullback `modulePullbackDerived f`.
/-- The derived pullback functor is exact in the triangulated sense. -/
theorem modulePullbackDerived_isTriangulated
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [HasShift (ModuleDerived Y) ℤ]
    [Preadditive (ModuleDerived Y)]
    [∀ n : ℤ, (shiftFunctor (ModuleDerived Y) n).Additive]
    [Pretriangulated (ModuleDerived Y)]
    [IsTriangulated (ModuleDerived Y)]
    [(modulePullback f).Additive] :
    (modulePullbackDerived f).IsTriangulated := sorry

end AlgebraicGeometry.RingedSpace
