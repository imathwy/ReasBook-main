import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Topology.CWComplex.Abstract.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Definition_2_4_1

universe u

/-- A based space is a based CW complex when its underlying topological space admits a
`TopCat.CWComplex` structure. -/
def IsBasedCWComplex (X : BasedSpace.{u}) : Prop :=
  Nonempty (TopCat.CWComplex X.right)

/-- The full subcategory of based spaces whose underlying spaces admit CW-complex structures. -/
abbrev BasedCWComplex := CategoryTheory.ObjectProperty.FullSubcategory IsBasedCWComplex
