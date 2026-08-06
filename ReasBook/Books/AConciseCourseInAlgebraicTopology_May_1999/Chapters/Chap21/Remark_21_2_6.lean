import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap21.Definition_21_2_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap21.Lemma_21_2_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap21.Lemma_21_2_5

-- Semantic recall via Chapter 21 precedent: the source-facing owner for the signature index is
-- `manifoldIndex`, while the immediately relevant structural companions already formalized in this
-- chapter are its additivity under disjoint union and multiplicativity under products. The current
-- repository still has no canonical oriented-cobordism owner or bordism-invariance theorem for
-- `manifoldIndex`, so this remark remains a labeled recall block around those Chapter 21 surfaces.

/- Remark 21.2.6. The index `I(M)` from Definition 21.2.2 is presented as an additive and
multiplicative invariant of compact oriented manifolds. In this repository, that content is
formalized by the owner `manifoldIndex` together with Lemma 21.2.4
`manifoldIndex_disjointUnion` and the product-comparison bridge Lemma 21.2.5
`manifoldIndex_prod`. Since there is not yet a canonical oriented-cobordism owner, a
distinguished Chapter 20 product comparison on integral singular chains, or a bordism-invariance
theorem for `manifoldIndex`, the remark is recorded as a labeled recall block centered on those
existing Chapter 21 APIs. -/

#check manifoldIndex
#check manifoldIndex_disjointUnion
#check manifoldIndex_prod
