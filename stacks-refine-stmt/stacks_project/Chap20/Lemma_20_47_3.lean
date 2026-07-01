import Mathlib
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import stacks_project.Chap20.Definition_20_47_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

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

/-- The pullback functor on `\mathcal O_Y`-modules attached to a morphism of ringed spaces. -/
noncomputable abbrev modulePullback {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (RingedSpace.Modules Y) ⥤ (RingedSpace.Modules X) :=
  SheafOfModules.pullback (pushforwardStructureSheafHom f)

/-- The quasi-isomorphisms in the homotopy category of `\mathcal O_X`-module complexes. -/
abbrev ModuleQis (X : RingedSpace.{u}) :=
  HomotopyCategory.quasiIso (RingedSpace.Modules X) (up ℤ)

/-- The homotopy-category functor used to define the total left derived pullback. -/
abbrev modulePullbackToDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePullback f).Additive] :
    HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules X) :=
  (modulePullback f).mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

-- Proof sketch: choose K-flat resolutions on `Y`, use preservation of K-flatness by pullback,
-- and invoke the universal property of the total left derived functor.
/-- Pullback on homotopy categories admits a total left derived functor. -/
theorem modulePullbackToDerived_hasLeftDerivedFunctor
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive] :
    Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y) := sorry

/-- The canonical left-derived-functor instance for module pullback. -/
instance instHasLeftDerivedFunctorModulePullbackToDerived
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive] :
    Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y) :=
  modulePullbackToDerived_hasLeftDerivedFunctor f

/-- The derived pullback functor `Lf^* : D(\mathcal O_Y) \to D(\mathcal O_X)`. -/
abbrev modulePullbackDerived
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive] :
    DerivedCategory (RingedSpace.Modules Y) ⥤ DerivedCategory (RingedSpace.Modules X) :=
  Functor.totalLeftDerived (modulePullbackToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules Y))
    (ModuleQis Y)

section

variable {X Y : RingedSpace.{u}}

-- Proof sketch: represent `E` by an `m`-pseudo-coherent complex on `Y`, pull back the local
-- strictly perfect approximation data along `f`, use Lemma `20.46.4` to preserve strict
-- perfectness and the derived-functor cohomology-vanishing argument from Lemma `13.16.1` to keep
-- the cone acyclic in degrees `≥ m`, and then apply Lemma `20.47.2` to conclude.
/-- Lemma 20.47.3: if an object `E` of `D(\mathcal O_Y)` is `m`-pseudo-coherent, then the
derived pullback `Lf^*E` is `m`-pseudo-coherent. -/
theorem modulePullbackDerived_isMPseudoCoherent
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    (f : X ⟶ Y) [(modulePullback f).Additive]
    (E : DerivedCategory (RingedSpace.Modules Y)) (m : ℤ)
    (hE : IsMPseudoCoherent E m) :
    IsMPseudoCoherent ((modulePullbackDerived f).obj E) m := sorry

end

end AlgebraicGeometry.RingedSpace
