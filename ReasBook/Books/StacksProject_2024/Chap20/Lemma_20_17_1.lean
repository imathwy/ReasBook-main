import Mathlib
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap13.Definition_13_15_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The category of sheaves of modules over the structure sheaf of a ringed space. -/
abbrev ringedSpaceSheafModules (X : RingedSpace.{u}) :=
  SheafOfModules ((RingedSpace.ringCatSheaf X))

/-- The category of `\mathcal O_X`-modules on a ringed space carries the standard derived
category. -/
instance ringedSpaceSheafModules_hasDerivedCategory (X : RingedSpace.{u}) :
    HasDerivedCategory (ringedSpaceSheafModules X) :=
  HasDerivedCategory.standard (ringedSpaceSheafModules X)

section BaseChange

variable {X X' S S' : RingedSpace.{u}}
variable (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)

local notation "ModX" => ringedSpaceSheafModules X
local notation "ModX'" => ringedSpaceSheafModules X'
local notation "ModS" => ringedSpaceSheafModules S
local notation "ModS'" => ringedSpaceSheafModules S'

variable [(RingedSpace.Hom.pushforward f).Additive]
variable [(RingedSpace.Hom.pushforward f').Additive]
variable [(RingedSpace.Hom.pullback g).Additive]
variable [(RingedSpace.Hom.pullback g').Additive]

/-- The canonical localization `K^+(X) ⥤ D^+(X)` is a localization at quasi-isomorphisms. -/
instance ringedSpace_boundedBelowLocalization_ModX :
    Functor.IsLocalization
      (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow (𝟭 ModX))
      (CategoryTheory.boundedBelowHomotopyQuasiIso ModX) := sorry

/-- The canonical localization `K^+(X') ⥤ D^+(X')` is a localization at quasi-isomorphisms. -/
instance ringedSpace_boundedBelowLocalization_ModX' :
    Functor.IsLocalization
      (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow (𝟭 ModX'))
      (CategoryTheory.boundedBelowHomotopyQuasiIso ModX') := sorry

/-- The canonical localization `K^+(S) ⥤ D^+(S)` is a localization at quasi-isomorphisms. -/
instance ringedSpace_boundedBelowLocalization_ModS :
    Functor.IsLocalization
      (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow (𝟭 ModS))
      (CategoryTheory.boundedBelowHomotopyQuasiIso ModS) := sorry

/-- The canonical localization `K^+(S') ⥤ D^+(S')` is a localization at quasi-isomorphisms. -/
instance ringedSpace_boundedBelowLocalization_ModS' :
    Functor.IsLocalization
      (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow (𝟭 ModS'))
      (CategoryTheory.boundedBelowHomotopyQuasiIso ModS') := sorry

/-- The bounded-below right derived functor of module pushforward along `f` exists. -/
instance ringedSpace_hasRightDerivedFunctor_pushforward_f :
    Functor.HasRightDerivedFunctor
      (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow (RingedSpace.Hom.pushforward f))
      (CategoryTheory.boundedBelowHomotopyQuasiIso ModX) := sorry

/-- The bounded-below right derived functor of module pushforward along `f'` exists. -/
instance ringedSpace_hasRightDerivedFunctor_pushforward_f' :
    Functor.HasRightDerivedFunctor
      (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow (RingedSpace.Hom.pushforward f'))
      (CategoryTheory.boundedBelowHomotopyQuasiIso ModX') := sorry

/-- The bounded-below right derived functor of module pullback along `g` exists. -/
instance ringedSpace_hasRightDerivedFunctor_pullback_g :
    Functor.HasRightDerivedFunctor
      (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow (RingedSpace.Hom.pullback g))
      (CategoryTheory.boundedBelowHomotopyQuasiIso ModS) := sorry

/-- The bounded-below right derived functor of module pullback along `g'` exists. -/
instance ringedSpace_hasRightDerivedFunctor_pullback_g' :
    Functor.HasRightDerivedFunctor
      (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow (RingedSpace.Hom.pullback g'))
      (CategoryTheory.boundedBelowHomotopyQuasiIso ModX) := sorry

/-- The bounded-below right derived functor of module pushforward along `f`. -/
abbrev ringedSpaceDerivedPushforward :
    CategoryTheory.boundedBelowDerivedCategory ModX ⥤
      CategoryTheory.boundedBelowDerivedCategory ModS :=
  Functor.totalRightDerived
    (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow (RingedSpace.Hom.pushforward f))
    (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow (𝟭 ModX))
    (CategoryTheory.boundedBelowHomotopyQuasiIso ModX)

/-- The bounded-below right derived functor of module pullback along `g`. For flat `g` this
formalizes the exact pullback on `D^+`. -/
abbrev ringedSpaceDerivedPullback :
    CategoryTheory.boundedBelowDerivedCategory ModS ⥤
      CategoryTheory.boundedBelowDerivedCategory ModS' :=
  Functor.totalRightDerived
    (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow (RingedSpace.Hom.pullback g))
    (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow (𝟭 ModS))
    (CategoryTheory.boundedBelowHomotopyQuasiIso ModS)

/-- The source object of the bounded-below base-change morphism. -/
abbrev ringedSpaceBaseChangeSource (ℱ : CategoryTheory.boundedBelowDerivedCategory ModX) :
    CategoryTheory.boundedBelowDerivedCategory ModS' :=
  ((ringedSpaceDerivedPushforward f) ⋙
    (ringedSpaceDerivedPullback g)).obj ℱ

/-- The target object of the bounded-below base-change morphism. -/
abbrev ringedSpaceBaseChangeTarget (ℱ : CategoryTheory.boundedBelowDerivedCategory ModX) :
    CategoryTheory.boundedBelowDerivedCategory ModS' :=
  ((Functor.totalRightDerived
      (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow
        (RingedSpace.Hom.pullback g'))
      (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow (𝟭 ModX))
      (CategoryTheory.boundedBelowHomotopyQuasiIso ModX)) ⋙
    (Functor.totalRightDerived
      (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow
        (RingedSpace.Hom.pushforward f'))
      (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow (𝟭 ModX'))
      (CategoryTheory.boundedBelowHomotopyQuasiIso ModX'))).obj ℱ

-- Proof sketch: resolve a bounded-below representative of `\mathcal F^\bullet`, pull it back
-- along `g'`, resolve again on `X'`, and use adjunction to produce a morphism of complexes from
-- the pullback of a representative of `Rf_* \mathcal F^\bullet` to a representative of
-- `Rf'_* (g')^* \mathcal F^\bullet`. Passing to the bounded-below derived category yields the
-- base-change morphism.
/-- Lemma 20.17.1: for a commutative square of ringed spaces
`X' \xrightarrow{g'} X`, `S' \xrightarrow{g} S` with vertical maps `f' : X' \to S'` and
`f : X \to S`, if `g` and `g'` are flat, then for every bounded-below derived object
`\mathcal F^\bullet \in D^+(X)` there exists a canonical base-change morphism from the derived
pullback of `Rf_* \mathcal F^\bullet` to the derived pushforward of the derived pullback of
`\mathcal F^\bullet` along `g'`. In this statement the exact pullbacks `g^*` and `(g')^*` are
formalized by their bounded-below right derived functors. -/
theorem ringedSpace_boundedBelow_derived_baseChange_exists
    (hcomm : g' ≫ f = f' ≫ g)
    (hg : ∀ s' : S', (g.hom.stalkMap s').hom.Flat)
    (hg' : ∀ x' : X', (g'.hom.stalkMap x').hom.Flat)
    (ℱ : CategoryTheory.boundedBelowDerivedCategory ModX) :
    ∃ τ :
        (ringedSpaceBaseChangeSource f g ℱ) ⟶
          (ringedSpaceBaseChangeTarget g' f' ℱ),
      True := sorry

end BaseChange

end AlgebraicGeometry
