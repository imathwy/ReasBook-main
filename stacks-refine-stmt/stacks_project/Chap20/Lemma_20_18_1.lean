import Mathlib
import stacks_project.Chap06.Definition_6_27_1
import stacks_project.Chap20.Lemma_20_17_1

-- Declarations for this item will be appended below by the statement pipeline.

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
