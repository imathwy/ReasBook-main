import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_20_18_1 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The fiber ringed space of `f : X ⟶ Y` over the point ringed space `({y}, \mathcal O_{Y, y})`.
-/
abbrev pointFiber {X Y : RingedSpace.{u}} (f : X ⟶ Y) (y : Y)
    [HasPullback f (pointInclusion y)] : RingedSpace.{u} :=
  pullback f (pointInclusion y)

/-- The projection from the fiber over `y` back to `X`. -/
abbrev pointFiberToSource {X Y : RingedSpace.{u}} (f : X ⟶ Y) (y : Y)
    [HasPullback f (pointInclusion y)] :
    pointFiber f y ⟶ X :=
  pullback.fst f (pointInclusion y)

/-- The structural morphism from the fiber over `y` to the point ringed space
`({y}, \mathcal O_{Y, y})`. -/
abbrev pointFiberToPoint {X Y : RingedSpace.{u}} (f : X ⟶ Y) (y : Y)
    [HasPullback f (pointInclusion y)] :
    pointFiber f y ⟶ pointRingedSpace y :=
  pullback.snd f (pointInclusion y)

-- Proof sketch: specialize the base-change comparison of Lemma `20.17.1` to the cartesian square
-- obtained by pulling `f` back along the point inclusion `({y}, \mathcal O_{Y, y}) ⟶ Y`. The
-- resulting pullback object models the fiber `f^{-1}(y)`, and the assumptions that `f` is closed,
-- separated, and has quasi-compact fiber over `y` identify the base-change morphism with the
-- comparison from the stalk of `Rf_* E` at `y` to the derived global sections of the restricted
-- complex on the fiber.
/-- Lemma 20.18.1: if `f : (X, \mathcal O_X) ⟶ (Y, \mathcal O_Y)` is a closed and separated
morphism of ringed spaces, `y : Y`, and the fiber `f^{-1}(y)` is quasi-compact, then for every
bounded-below derived object `E ∈ D^+(\mathcal O_X)` the pullback of `Rf_* E` to the point ringed
space `({y}, \mathcal O_{Y, y})` is canonically isomorphic to the derived pushforward of the
restriction of `E` to the fiber `f^{-1}(y)`. This models the equality
`(Rf_* E)_y = RΓ(f^{-1}(y), E|_{f^{-1}(y)})` in `D^+(\mathcal O_{Y, y})`. -/
theorem derived_pushforward_stalk_isomorphic_fiber_derived_global_sections
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    (hclosed : IsClosedMap f.hom.base)
    (hseparated : IsSeparatedMap f.hom.base)
    (y : Y)
    (hyqc : IsCompact (f.hom.base ⁻¹' ({y} : Set Y)))
    [HasPullback f (pointInclusion y)]
    [(RingedSpace.Hom.pushforward f).Additive]
    [(RingedSpace.Hom.pushforward (pointFiberToPoint f y)).Additive]
    [(RingedSpace.Hom.pullback (pointInclusion y)).Additive]
    [(RingedSpace.Hom.pullback (pointFiberToSource f y)).Additive]
    (E : CategoryTheory.boundedBelowDerivedCategory
      (SheafOfModules ((RingedSpace.ringCatSheaf X)))) :
    IsIsomorphic
      (ringedSpaceBaseChangeSource f (pointInclusion y) E)
      (ringedSpaceBaseChangeTarget (pointFiberToSource f y) (pointFiberToPoint f y) E) := sorry

end AlgebraicGeometry

/-! ### Theorem_20_18_2_Proper_base_change (from Chap20) -/
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

/-! ### Lemma_20_18_3_Proper_base_change_for_sheaves_of_sets (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open TopCat

noncomputable section

universe u

namespace TopCat.Sheaf

variable {X Y Y' : TopCat.{u}}

/-- The source sheaf `g^{-1} f_* \mathcal F` in the proper base change comparison for sheaves of
sets. -/
abbrev properBaseChangeSetSheafSource (f : X ⟶ Y) (g : Y' ⟶ Y) (ℱ : X.Sheaf (Type u)) :
    Y'.Sheaf (Type u) :=
  (TopCat.Sheaf.pullback (Type u) g).obj ((TopCat.Sheaf.pushforward (Type u) f).obj ℱ)

/-- The target sheaf `f'_* (g')^{-1} \mathcal F` in the proper base change comparison for sheaves
of sets. -/
abbrev properBaseChangeSetSheafTarget (f : X ⟶ Y) (g : Y' ⟶ Y) (ℱ : X.Sheaf (Type u)) :
    Y'.Sheaf (Type u) :=
  (TopCat.Sheaf.pushforward (Type u) (pullback.snd f g)).obj
    ((TopCat.Sheaf.pullback (Type u) (pullback.fst f g)).obj ℱ)

section ProperBaseChangeForSheavesOfSets

variable (f : X ⟶ Y) (g : Y' ⟶ Y)

-- Proof sketch: reduce to stalks at points of `Y'`, as in the abelian proper base change theorem.
-- Identify both stalks with sections of the restriction of `\mathcal F` to the fiber over the
-- image point, then apply the set-valued version of the fiberwise description from
-- Lemmas `20.18.1` and `20.16.3`.
/-- Lemma 20.18.3 (Proper base change for sheaves of sets): for a cartesian square of topological
spaces with `X' = Y' ×[Y] X`, a proper map `f : X ⟶ Y`, and a sheaf of sets `\mathcal F` on `X`,
the inverse image `g^{-1} f_* \mathcal F` is canonically isomorphic to
`f'_* (g')^{-1} \mathcal F`, where `g' : X' ⟶ X` and `f' : X' ⟶ Y'` are the pullback
projections. -/
theorem proper_base_change_set_sheaf_isomorphic
    (hf : IsProperMap f) (ℱ : X.Sheaf (Type u)) :
    IsIsomorphic (properBaseChangeSetSheafSource f g ℱ) (properBaseChangeSetSheafTarget f g ℱ) :=
  sorry

end ProperBaseChangeForSheavesOfSets

end TopCat.Sheaf
