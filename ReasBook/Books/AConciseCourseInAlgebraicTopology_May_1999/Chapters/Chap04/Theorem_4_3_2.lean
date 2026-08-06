import Mathlib.Topology.Homotopy.Equiv
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Corollary_2_8_2.WedgeOfCircles
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Theorem_4_3_2.QuotientContext

open scoped ContinuousMap

noncomputable section

namespace SimpleGraph

namespace MaximalTreeQuotientContext

variable {V : Type}

/-- Theorem 4.3.2 (1). If `X` is a connected graph with maximal tree `T`, then the quotient
`X / T`, modeled here by `X.quotientTopCat`, is homeomorphic to the wedge of one circle for each
edge of `X.graph` not contained in `X.tree`, encoded by `(wedge_of_circles X.nonTreeEdges).right`.
-/
theorem quotientTopCat_nonempty_homeomorph_wedgeOfCircles (X : MaximalTreeQuotientContext V) :
    Nonempty (X.quotientTopCat ≃ₜ (wedge_of_circles X.nonTreeEdges).right) := sorry

/-- Theorem 4.3.2 (2). For a connected graph with maximal tree `T`, the quotient map collapsing
the realized maximal tree,
`X.quotientMap : X.realization ⟶ X.quotientTopCat`, is a homotopy equivalence. -/
theorem quotientMap_exists_homotopyEquiv (X : MaximalTreeQuotientContext V) :
    ∃ e : X.realization ≃ₕ X.quotientTopCat, e.toFun = X.quotientMap := sorry

end MaximalTreeQuotientContext

end SimpleGraph
