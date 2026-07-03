import Mathlib
import stacks_project.Chap13.Lemma_13_22_1
import stacks_project.Chap20.«20_14_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Functor

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y Z : RingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable [(mapBoundedBelowHomotopyToDerivedBelow (𝟭 (RingedSpace.Modules Y))).IsLocalization
  (boundedBelowHomotopyQuasiIso (RingedSpace.Modules Y))]
variable [Functor.HasRightDerivedFunctor
  (mapBoundedBelowHomotopyCategory (RingedSpace.Hom.pushforward f) ⋙
    mapBoundedBelowHomotopyToDerivedBelow (RingedSpace.Hom.pushforward g))
  (boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))]
variable [Functor.HasRightDerivedFunctor
  (mapBoundedBelowHomotopyCategory (RingedSpace.Hom.pushforward f) ⋙
    mapBoundedBelowHomotopyToDerivedBelow (𝟭 (RingedSpace.Modules Y)))
  (boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))]
variable [Functor.HasRightDerivedFunctor
  (mapBoundedBelowHomotopyToDerivedBelow (RingedSpace.Hom.pushforward g))
  (boundedBelowHomotopyQuasiIso (RingedSpace.Modules Y))]
variable [Functor.HasRightDerivedFunctor
  (mapHomotopyCategoryToDerived (RingedSpace.Hom.pushforward g))
  (HomotopyCategory.quasiIso (RingedSpace.Modules Y) (ComplexShape.up ℤ))]

-- Proof sketch: the ordinary pushforwards compose, so the canonical comparison morphism from
-- `R(g ∘ f)_* ⟶ Rg_* ∘ Rf_*`. Apply Lemma `13.22.1`; by Lemma `20.11.10`, `f_*` sends injectives
-- to sheaves whose higher cohomology on opens vanishes for `g`, and Lemma `20.7.3` identifies
-- the higher direct images of `g_*` with those cohomology sheaves, giving the required
-- right-acyclicity.
/-- Lemma 20.13.7: for composable morphisms of ringed spaces `f : X ⟶ Y` and `g : Y ⟶ Z`, the
canonical comparison morphism from the right derived direct image of the composite to the
composite of the right derived direct images is an isomorphism; this formalizes
`R(g \circ f)_* = Rg_* \circ Rf_*` on `D^{+}`. -/
lemma modulePushforward_rightDerivedCompComparison_isIso :
    IsIso (rightDerivedCompComparison
      (boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))
      (boundedBelowHomotopyQuasiIso (RingedSpace.Modules Y))
      (RingedSpace.Hom.pushforward f) (RingedSpace.Hom.pushforward g)) := sorry

end AlgebraicGeometry.RingedSpace
