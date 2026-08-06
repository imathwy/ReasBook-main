import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_3_1

noncomputable section

-- Semantic recall via `lean_leansearch`: `MvPolynomial.esymm` together with
-- `MvPolynomial.aeval_esymm_eq_multiset_esymm` is the canonical mathlib owner for expressing an
-- elementary symmetric polynomial evaluated on a finite family of classes as the corresponding
-- elementary symmetric function of those classes. Combined with the Chapter 23 Whitney-sum
-- expansion API, this gives the source-faithful interpretation of the classes produced by
-- Construction 23.6.2 on a split Whitney sum of line bundles.

/- Remark 23.6.4. The construction shows why the Stiefel-Whitney classes `w_i` of a split real
vector bundle are the elementary symmetric functions in the degree-`1` classes of the split line
summands. In this development, that explanation is recalled by the Chapter 23 Whitney-sum
expansion owner together with the canonical elementary-symmetric polynomial owner
`MvPolynomial.esymm`. -/
#check whitneySumExpansion
#check IsStiefelWhitneyTheory.whitneySum
#check MvPolynomial.esymm
#check MvPolynomial.aeval_esymm_eq_multiset_esymm
