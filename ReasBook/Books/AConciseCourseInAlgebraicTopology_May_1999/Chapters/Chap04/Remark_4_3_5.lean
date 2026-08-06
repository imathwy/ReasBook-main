import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Theorem_4_3_2.QuotientContext
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Problem_6_6_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.CollapseSubsetPair

open scoped ContinuousMap

noncomputable section

namespace SimpleGraph

namespace MaximalTreeQuotientContext

variable {V : Type}

-- Semantic recall via `lean_leansearch`: `ContinuousMap.HomotopyEquiv` is the canonical owner for
-- homotopy equivalences, and local Chapter 6 precedent packages the later quotient theorem as
-- `cofibrationQuotientMap_exists_homotopyEquiv_of_contractible`.

/-- The collapse-quotient model attached to the realized maximal-tree inclusion
`subsetInclusion X.treeSubspace` is the graph quotient space `X.quotientSpace`. -/
theorem cofibrationQuotientSpace_treeSubspace_eq
    (X : MaximalTreeQuotientContext V) :
    cofibrationQuotientSpace (subsetInclusion X.treeSubspace) = X.quotientSpace := by
  simp [cofibrationQuotientSpace, subsetInclusion, MaximalTreeQuotientContext.quotientSpace]

/-- After identifying the generic collapse quotient with `X.quotientSpace`, the specialized
cofibration quotient map for `subsetInclusion X.treeSubspace` is `X.quotientMap`. -/
theorem cofibrationQuotientMap_treeSubspace_heq
    (X : MaximalTreeQuotientContext V) :
    HEq (cofibrationQuotientMap (subsetInclusion X.treeSubspace)) X.quotientMap := sorry

/-- Remark 4.3.5. The homotopy-equivalence conclusion of Theorem 4.3.2 is recovered by
specializing `cofibrationQuotientMap_exists_homotopyEquiv_of_contractible` to
`subsetInclusion X.treeSubspace`: if the realized maximal tree is a contractible cofibration
subspace of `X.realization`, then the induced quotient map `X.quotientMap` is a homotopy
equivalence. -/
theorem quotientMap_exists_homotopyEquiv_of_contractible_cofibration
    (X : MaximalTreeQuotientContext V) (hi : IsCofibration (subsetInclusion X.treeSubspace))
    [ContractibleSpace X.treeSubspace] :
    ∃ e : X.realization ≃ₕ X.quotientTopCat, e.toFun = X.quotientMap := sorry

end MaximalTreeQuotientContext

end SimpleGraph
