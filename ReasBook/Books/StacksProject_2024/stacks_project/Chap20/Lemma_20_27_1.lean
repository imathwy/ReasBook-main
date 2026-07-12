import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Localization.Triangulated
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap13.Situation_13_15_1
import StacksProject_2024.Chap18.Definition_18_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open AlgebraicGeometry
open scoped RingedSpace.Hom

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The quasi-isomorphisms used to localize the homotopy category of `𝒪_X`-modules. -/
abbrev ModuleQis (X : RingedSpace.{u}) :=
  HomotopyCategory.quasiIso (RingedSpace.Modules X) (up ℤ)

/-- The functor `K(𝒪_Y) ⥤ D(𝒪_X)` obtained by applying `f^*` termwise and then
passing to the derived category. -/
abbrev modulePullbackToDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(f^*).Additive] :
    HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules X) :=
  CategoryTheory.mapHomotopyCategoryToDerived (f^*)

-- Proof sketch: apply Lemma `13.14.15` to the triangulated functor
-- `modulePullbackToDerived f : K(𝒪_Y) ⥤ D(𝒪_X)` with the subset of K-flat
-- complexes. Lemma `20.26.12` gives enough K-flat resolutions, Lemma `20.26.8` shows pullback
-- preserves K-flatness, and Lemma `20.26.13` shows pullback sends quasi-isomorphisms between
-- K-flat complexes to quasi-isomorphisms. Equation `13.14.9.1` then identifies the resulting
-- total left derived functor with the desired `Lf^*`.
/-- Lemma 20.27.1: the pullback functor on homotopy categories
`K(𝒪_Y) ⥤ D(𝒪_X)` obtained from `f^*` has an everywhere defined total left
derived functor with respect to quasi-isomorphisms. Equivalently, the construction via K-flat
resolutions is independent of choices and defines the derived pullback functor
`Lf^* : D(𝒪_Y) ⥤ D(𝒪_X)`. -/
@[stacks 06YJ]
theorem modulePullbackToDerived_hasLeftDerivedFunctor
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(f^*).Additive] :
    (modulePullbackToDerived f).HasLeftDerivedFunctor (ModuleQis Y) := sorry

instance instModulePullbackToDerivedHasLeftDerivedFunctor
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(f^*).Additive] :
    Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y) :=
  modulePullbackToDerived_hasLeftDerivedFunctor f

/-- The derived pullback functor `Lf^* : D(𝒪_Y) ⥤ D(𝒪_X)`. -/
def modulePullbackDerived
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(f^*).Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)] :
    DerivedCategory (RingedSpace.Modules Y) ⥤ DerivedCategory (RingedSpace.Modules X) :=
  (modulePullbackToDerived f).totalLeftDerived DerivedCategory.Qh (ModuleQis Y)

end AlgebraicGeometry.RingedSpace

namespace RingedSpaceDerivedPullback

/- Lean surface notation for the derived pullback functor `Lf^*`, written as `L(f)^*` so it does
not conflict with the existing module-pullback notation `f^*`. -/
scoped notation:max "L(" f:max ")" "^*" =>
  AlgebraicGeometry.RingedSpace.modulePullbackDerived f

end RingedSpaceDerivedPullback

open scoped RingedSpaceDerivedPullback
