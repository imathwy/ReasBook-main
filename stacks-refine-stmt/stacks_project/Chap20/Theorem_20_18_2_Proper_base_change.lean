import Mathlib
import stacks_project.Chap06.Definition_6_8_1
import stacks_project.Chap13.Situation_13_15_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open TopCat
open scoped TopCat

noncomputable section

universe u

namespace CategoryTheory.Sheaf

/-- Sheaves of abelian groups on a topological space carry the standard derived category. -/
instance sheafAddCommGrp_hasDerivedCategory (X : TopCat.{u}) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  HasDerivedCategory.standard _

section ProperBaseChange

variable {X Y Y' : TopCat.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- The bounded-below derived category `D^+(X)` of abelian sheaves on `X`. -/
abbrev abelianSheafDplus (X : TopCat.{u}) :=
  CategoryTheory.boundedBelowDerivedCategory (Ab(X))

/-- The pullback space `X' = Y' ×[Y] X` in the proper base change square. -/
abbrev properBaseChangePullback : TopCat.{u} := pullback f g

/-- The projection `g' : X' ⟶ X` from the proper base change pullback. -/
abbrev properBaseChangeFst : properBaseChangePullback f g ⟶ X := pullback.fst f g

/-- The projection `f' : X' ⟶ Y'` from the proper base change pullback. -/
abbrev properBaseChangeSnd : properBaseChangePullback f g ⟶ Y' := pullback.snd f g

variable [(TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).Additive]
variable [(TopCat.Sheaf.pullback AddCommGrpCat.{u} g).Additive]
variable [(TopCat.Sheaf.pullback AddCommGrpCat.{u} (properBaseChangeFst f g)).Additive]
variable [(TopCat.Sheaf.pushforward AddCommGrpCat.{u} (properBaseChangeSnd f g)).Additive]

variable [Functor.IsLocalization
  (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow (𝟭 (Ab(X))))
  (CategoryTheory.boundedBelowHomotopyQuasiIso (Ab(X)))]
variable [Functor.IsLocalization
  (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow (𝟭 (Ab(Y))))
  (CategoryTheory.boundedBelowHomotopyQuasiIso (Ab(Y)))]
variable [Functor.IsLocalization
  (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow
    (𝟭 (Ab(properBaseChangePullback f g))))
  (CategoryTheory.boundedBelowHomotopyQuasiIso (Ab(properBaseChangePullback f g)))]
variable [Functor.IsLocalization
  (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow (𝟭 (Ab(Y'))))
  (CategoryTheory.boundedBelowHomotopyQuasiIso (Ab(Y')))]

variable [Functor.HasRightDerivedFunctor
  (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f))
  (CategoryTheory.boundedBelowHomotopyQuasiIso (Ab(X)))]
variable [Functor.HasRightDerivedFunctor
  (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} g))
  (CategoryTheory.boundedBelowHomotopyQuasiIso (Ab(Y)))]
variable [Functor.HasRightDerivedFunctor
  (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} (properBaseChangeFst f g)))
  (CategoryTheory.boundedBelowHomotopyQuasiIso (Ab(X)))]
variable [Functor.HasRightDerivedFunctor
  (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (properBaseChangeSnd f g)))
  (CategoryTheory.boundedBelowHomotopyQuasiIso (Ab(properBaseChangePullback f g)))]

/-- The bounded-below derived direct image functor on abelian sheaves. -/
abbrev abelianSheafDerivedPushforward : abelianSheafDplus X ⥤ abelianSheafDplus Y :=
  Functor.totalRightDerived
    (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f))
    (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow (𝟭 (Ab(X))))
    (CategoryTheory.boundedBelowHomotopyQuasiIso (Ab(X)))

/-- The bounded-below derived inverse-image functor on abelian sheaves, formalized as the
bounded-below right derived functor of the exact pullback functor. -/
abbrev abelianSheafDerivedPullback : abelianSheafDplus Y ⥤ abelianSheafDplus Y' :=
  Functor.totalRightDerived
    (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow
      (TopCat.Sheaf.pullback AddCommGrpCat.{u} g))
    (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow (𝟭 (Ab(Y))))
    (CategoryTheory.boundedBelowHomotopyQuasiIso (Ab(Y)))

/-- The source object `g^{-1} Rf_* E` of the proper base change comparison. -/
abbrev properBaseChangeSource (E : abelianSheafDplus X) : abelianSheafDplus Y' :=
  ((abelianSheafDerivedPushforward f) ⋙ (abelianSheafDerivedPullback g)).obj E

/-- The target object `Rf'_* (g')^{-1} E` of the proper base change comparison. -/
abbrev properBaseChangeTarget (E : abelianSheafDplus X) : abelianSheafDplus Y' :=
  (((abelianSheafDerivedPullback (properBaseChangeFst f g)) ⋙
      (abelianSheafDerivedPushforward (properBaseChangeSnd f g))).obj E)

-- Proof sketch: reduce to stalks at points of `Y'`. Properness implies that `f` is closed and has
-- compact fibers, and the same remains true after base change. Apply the stalk/fiber comparison of
-- Lemma `20.18.1` to both sides, identify the fibers of `f` and `f'` over corresponding points by
-- the pullback square, and transport the restricted complex along that homeomorphism.
/-- Theorem 20.18.2 (Proper base change): for a cartesian square of topological spaces with
`X' = Y' ×[Y] X`, a proper map `f : X ⟶ Y`, and a bounded-below derived abelian sheaf
`E ∈ D^+(X)`, the objects `g^{-1} Rf_* E` and `Rf'_* (g')^{-1} E` are isomorphic in `D^+(Y')`,
where `g' : X' ⟶ X` and `f' : X' ⟶ Y'` are the pullback projections. -/
theorem proper_base_change_boundedBelowDerived_isomorphic
    (hf : IsProperMap f) (E : abelianSheafDplus X) :
    IsIsomorphic (properBaseChangeSource f g E) (properBaseChangeTarget f g E) := sorry

end ProperBaseChange

end CategoryTheory.Sheaf
