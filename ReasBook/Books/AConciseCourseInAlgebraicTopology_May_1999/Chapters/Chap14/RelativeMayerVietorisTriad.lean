import Mathlib.Topology.Category.TopCat.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_7_1

universe u

namespace Triad

/-- The triad on the subspace `X ⊆ Y` induced by subsets `A, B ⊆ Y`, used in the relative
Mayer-Vietoris sequences for the pair `(Y, X)`. -/
def relativeMayerVietoris {Y : TopCat.{u}} (X A B : Set Y) : Triad X where
  subspaceA := Subtype.val ⁻¹' A
  subspaceB := Subtype.val ⁻¹' B

end Triad
