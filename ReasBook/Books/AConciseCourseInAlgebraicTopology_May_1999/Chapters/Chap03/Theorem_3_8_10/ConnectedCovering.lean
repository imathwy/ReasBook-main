import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Separation.Connected
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Definition_3_1_5

universe u

open CategoryTheory

variable {B : Type u} [TopologicalSpace B]

/-- The category of connected covering spaces over `B`, realized as the full subcategory of the
over-category `Over (TopCat.of B)` on path-connected covering maps with path-connected total
space. -/
abbrev ConnectedCoveringSpace (B : Type u) [TopologicalSpace B] : Type (u + 1) :=
  ObjectProperty.FullSubcategory
    (fun X : Over (TopCat.of B) ↦
      IsPathConnectedCoveringMap X.hom ∧ PathConnectedSpace X.left)

namespace ConnectedCoveringSpace

/-- The underlying map of an object of `ConnectedCoveringSpace B` is a path-connected covering
map over `B`. -/
theorem isPathConnectedCoveringMap (X : ConnectedCoveringSpace B) :
    IsPathConnectedCoveringMap X.obj.hom :=
  X.2.1

/-- The total space of an object of `ConnectedCoveringSpace B` is path connected. -/
instance (X : ConnectedCoveringSpace B) : PathConnectedSpace X.obj.left :=
  X.2.2

/-- The total space of an object of `ConnectedCoveringSpace B` is path connected. -/
theorem pathConnectedSpace (X : ConnectedCoveringSpace B) :
    PathConnectedSpace X.obj.left :=
  inferInstance

end ConnectedCoveringSpace
