import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Theorem_4_3_2.QuotientContext

namespace SimpleGraph
namespace MaximalTreeQuotientContext

variable {V : Type}

-- Semantic recall via `lean_leansearch`: `IsFreeGroup`, `FreeGroup`, and the chapter-local
-- `wedge_of_circles_fundamental_group_comparison_bijective` match the standard free-group surface,
-- while `SimpleGraph.MaximalTreeQuotientContext` from Theorem 4.3.2 is the local owner for a
-- connected graph equipped with a chosen maximal tree.

/-- Corollary 4.4.3: if `X` is a connected graph, then `π_1(X)` is a free group with one
generator for each edge not in a chosen maximal tree. For the chosen realization `X.realization`
and a vertex basepoint `graphVertex X.boundary v`, this is recorded here by the existence of a
multiplicative equivalence
`FreeGroup X.nonTreeEdges ≃* FundamentalGroup X.realization (graphVertex X.boundary v)`. -/
theorem freeGroupNonTreeEdgesEquivFundamentalGroup
    (X : MaximalTreeQuotientContext V) (v : V) :
    Nonempty
      (FreeGroup X.nonTreeEdges ≃*
        FundamentalGroup X.realization (graphVertex X.boundary v)) := sorry

/-- A vertex-based fundamental group of the chosen graph realization is free. -/
instance instIsFreeGroupFundamentalGroupGraphVertex
    (X : MaximalTreeQuotientContext V) (v : V) :
    IsFreeGroup (FundamentalGroup X.realization (graphVertex X.boundary v)) := by
  classical
  let e := Classical.choice (freeGroupNonTreeEdgesEquivFundamentalGroup X v)
  exact IsFreeGroup.ofMulEquiv e

end MaximalTreeQuotientContext
end SimpleGraph
