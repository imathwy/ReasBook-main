import Mathlib
import StacksProject_2024.stacks_project.Chap29.HasFiniteIrreducibleComponentsOnCompactOpens

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` was unavailable here due HTTP 429, so this file uses the
-- installed mathlib owners `Scheme.PartialMap` and `genericPoints` together with the local
-- finiteness owner on quasi-compact opens.

variable {X Y : Scheme.{u}}

/-- Remark 29.49.13 (2): a partial map belongs to the intended morphism class when the induced map
on topological points sends the generic
points of irreducible components of its dense open domain onto those of the target scheme. -/
def PartialMap.MapsGenericPoints (f : X.PartialMap Y) : Prop :=
  Set.SurjOn f.hom.base (genericPoints f.domain) (genericPoints Y)

/-- Unfold `PartialMap.MapsGenericPoints` as the canonical constrained-surjectivity condition on
generic points. -/
theorem PartialMap.MapsGenericPoints_def (f : X.PartialMap Y) :
    f.MapsGenericPoints =
      Set.SurjOn f.hom.base (genericPoints f.domain) (genericPoints Y) := rfl

/-- Unfold `PartialMap.MapsGenericPoints` into the equality of generic-point images. -/
theorem PartialMap.mapsGenericPoints_iff (f : X.PartialMap Y) :
    f.MapsGenericPoints ↔ f.hom.base '' genericPoints f.domain = genericPoints Y := sorry

namespace TopologicalSpace.Opens

/-- The generic points of an open subset of a scheme, viewed as points of the ambient scheme. -/
def genericPointsInAmbient (U : X.Opens) : Set X :=
  Subtype.val '' genericPoints U

/-- Unfold `U.genericPointsInAmbient` as the image of `genericPoints U` in the ambient scheme. -/
theorem genericPointsInAmbient_def (U : X.Opens) :
    genericPointsInAmbient U = Subtype.val '' genericPoints U := rfl

end TopologicalSpace.Opens

/-- Remark 29.49.13 (3): for a dense open subset `U ⊆ X`, the generic points of irreducible
components of `U` coincide with those of `X`. This bridge is a general sober-space fact for
schemes, so it does not require the Chapter 29 finiteness hypothesis. -/
theorem genericPoints_image_eq_of_dense_open (X : Scheme.{u}) (U : X.Opens)
    (hU : Dense (U : Set X)) :
    TopologicalSpace.Opens.genericPointsInAmbient U = genericPoints X := sorry

end AlgebraicGeometry.Scheme
