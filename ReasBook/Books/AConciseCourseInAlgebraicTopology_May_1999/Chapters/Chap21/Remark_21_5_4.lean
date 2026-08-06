import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap21.Proposition_21_4_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap21.Lemma_21_5_2

-- Semantic recall via Chapter 21 precedent: the untainted surfaces available for the cobordism
-- mechanism are the induced-boundary orientation bridge
-- `ROrientedManifoldWithBoundary.toBoundaryROrientedManifoldSucc`, the relative boundary-morphism
-- specification surface from Proposition 21.4.3 together with its
-- relative-fundamental-class existence theorem, and the signature-zero step
-- `sigPos_eq_sigNeg_of_exists_isotropic_finrank_eq_half`.

/- Remark 21.5.4. The vanishing statement of Theorem 21.5.1 is the prototype for the cobordism
invariance of signature-type characteristic numbers. In the current repository there is still no
untainted canonical manifold-side owner for the signature-defined index `I(M)` from
Definition 21.2.2, because the current owner `manifoldIndex` still factors through the
choice-built fundamental-class surface from Proposition 20.1.3. Nor is there yet a general
bordism-invariance theorem for signature-type characteristic numbers. Accordingly, this expository
source item is formalized as a labeled recall block at the safe cobordism-mechanism layer:
the induced-boundary orientation bridge, the relative boundary-morphism specification
surface from Proposition 21.4.3, and the linear-algebra
signature-zero lemma used by the boundary-vanishing argument. -/

#check ROrientedManifoldWithBoundary.toBoundaryROrientedManifoldSucc
#check IsBoundaryRelativeSingularHomologyBoundary
#check existsUnique_boundaryRelativeFundamentalClass_of_rOrientedManifoldWithBoundary
#check sigPos_eq_sigNeg_of_exists_isotropic_finrank_eq_half
