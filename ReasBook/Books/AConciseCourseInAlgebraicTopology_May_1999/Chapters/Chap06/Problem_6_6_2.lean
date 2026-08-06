import Mathlib.Topology.Homotopy.Contractible
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Definition_6_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap11.Theorem_11_1_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Theorem_10_3_5

open CategoryTheory.HomRel
open scoped ContinuousMap

universe u v

noncomputable section

variable {A : Type u} {X : Type v} [TopologicalSpace A] [TopologicalSpace X]

-- Semantic recall via `lean_leansearch`: `ContinuousMap.HomotopyEquiv` is the canonical owner
-- for homotopy equivalences in the current environment. Local Chapter 11/13 precedent models
-- the quotient `X/A` by the collapse quotient `collapseSubsetType X A`, with quotient map owner
-- `collapseSubsetQuotientMap`.

/-- The quotient space `X/A` attached to a map `i : A → X`, modeled by collapsing the image
`Set.range i` to a single point. -/
abbrev cofibrationQuotientSpace (i : C(A, X)) :=
  collapseSubsetType X (Set.range i)

/-- The canonical quotient map `X → X/A` attached to `i : A → X`, where `X/A` is modeled by
`cofibrationQuotientSpace i`. This is the generic collapse quotient map for `Set.range i`. -/
abbrev cofibrationQuotientMap (i : C(A, X)) : C(X, cofibrationQuotientSpace i) :=
  collapseSubsetQuotientMap (Set.range i)

/-- If `i : A → X` is a cofibration and `A` is contractible, then the quotient map
`cofibrationQuotientMap i`, viewed as a morphism of `TopCat`, is a homotopy equivalence in the
repository's canonical quotient-by-homotopy owner. -/
instance cofibrationQuotientMap.instIsHomotopyEquivalence_of_contractible {i : C(A, X)}
    (hi : IsCofibration i) [ContractibleSpace A] :
    IsHomotopyEquivalence topCatHomotopyRel (TopCat.ofHom (cofibrationQuotientMap i)) := by
  sorry

/-- Problem 6.6.2. If `i : A → X` is a cofibration and `A` is contractible, then the quotient map
`X → X/A`, modeled here by `cofibrationQuotientMap i : C(X, cofibrationQuotientSpace i)`, is a
homotopy equivalence. -/
theorem cofibrationQuotientMap_exists_homotopyEquiv_of_contractible {i : C(A, X)}
    (hi : IsCofibration i) [ContractibleSpace A] :
    ∃ e : X ≃ₕ cofibrationQuotientSpace i, e.toFun = cofibrationQuotientMap i := by
  let _ := cofibrationQuotientMap.instIsHomotopyEquivalence_of_contractible hi
  exact exists_homotopyEquiv_of_isHomotopyEquivalence (cofibrationQuotientMap i)
