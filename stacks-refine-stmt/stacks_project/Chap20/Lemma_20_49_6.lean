import Mathlib
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import stacks_project.Chap20.Definition_20_49_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open ComplexShape
open TopologicalSpace

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X Y : RingedSpace.{u}}

local notation "DModY" => DerivedCategory (RingedSpace.Modules Y)

/-- The structure-sheaf morphism `\mathcal O_Y \to f_*\mathcal O_X` attached to a morphism of
ringed spaces. -/
noncomputable abbrev commRingSheafPushforwardMap (f : X ⟶ Y) :
    Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf :=
  ⟨f.hom.c⟩

/-- The structure-sheaf morphism of a ringed-space morphism after forgetting commutativity. -/
noncomputable abbrev pushforwardStructureSheafHom (f : X ⟶ Y) :
    (RingedSpace.ringCatSheaf Y) ⟶
      (TopCat.Sheaf.pushforward RingCat.{u} f.hom.base).obj (RingedSpace.ringCatSheaf X) :=
  (sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat.{u})).map
    (commRingSheafPushforwardMap f)

/-- The pullback functor on `\mathcal O_Y`-modules attached to a morphism of ringed spaces. -/
noncomputable abbrev modulePullback (f : X ⟶ Y) :
    (RingedSpace.Modules Y) ⥤ (RingedSpace.Modules X) :=
  SheafOfModules.pullback (pushforwardStructureSheafHom f)

/-- The quasi-isomorphisms in the homotopy category of `\mathcal O_X`-module complexes. -/
abbrev ModuleQis (X : RingedSpace.{u}) :=
  HomotopyCategory.quasiIso (RingedSpace.Modules X) (up ℤ)

/-- The homotopy-category functor used to define the total left derived pullback. -/
abbrev modulePullbackToDerived (f : X ⟶ Y) [(modulePullback f).Additive] :
    HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules X) :=
  (modulePullback f).mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

-- Proof sketch: choose K-flat resolutions on `Y`, use preservation of K-flatness by pullback,
-- and invoke the universal property of the total left derived functor.
/-- Pullback on homotopy categories admits a total left derived functor. -/
theorem modulePullbackToDerived_hasLeftDerivedFunctor
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    (f : X ⟶ Y) [(modulePullback f).Additive] :
    Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y) := sorry

/-- The canonical left-derived-functor instance for module pullback. -/
instance instHasLeftDerivedFunctorModulePullbackToDerived
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    (f : X ⟶ Y) [(modulePullback f).Additive] :
    Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y) :=
  modulePullbackToDerived_hasLeftDerivedFunctor f

/-- The derived pullback functor `Lf^* : D(\mathcal O_Y) \to D(\mathcal O_X)`. -/
abbrev modulePullbackDerived
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    (f : X ⟶ Y) [(modulePullback f).Additive] :
    DModY ⥤ DerivedCategory (RingedSpace.Modules X) :=
  Functor.totalLeftDerived (modulePullbackToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ DModY)
    (ModuleQis Y)

-- Proof sketch: combine the characterization of perfect objects by pseudo-coherence and local
-- finite tor dimension with Lemmas `20.47.3` and `20.48.4`, which show that derived pullback
-- preserves these two properties. Then apply the same characterization on `X`.
/-- Lemma 20.49.6: let `f : (X, \mathcal O_X) ⟶ (Y, \mathcal O_Y)` be a morphism of ringed
spaces and let `E` be an object of `D(\mathcal O_Y)`. If `E` is perfect in `D(\mathcal O_Y)`,
then the derived pullback `Lf^*E` is perfect in `D(\mathcal O_X)`. -/
theorem modulePullbackDerived_isPerfect
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    (f : X ⟶ Y) [(modulePullback f).Additive]
    (E : DModY) (hE : DerivedCategory.IsPerfect E) :
    DerivedCategory.IsPerfect ((modulePullbackDerived f).obj E) := sorry

end

end AlgebraicGeometry.RingedSpace
