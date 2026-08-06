import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Theorem_25_1_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap25.Theorem_25_1_4

-- This remark is expository rather than a new mathematical owner: the preceding Chapter 25 files
-- already expose the intrinsic cobordism invariant
-- `normalStiefelWhitneyNumbersAgree`, its cobordism-detection theorem, and the Thom polynomial
-- presentation owner `ThomUnorientedCobordismPolynomialAlgebra`.

/- Remark 25.1.5. Cobordism turns geometric boundary questions into computable algebraic
invariants because Theorem 25.1.4 identifies `cobordant n M N` with agreement of the normal
Stiefel-Whitney-number invariant `normalStiefelWhitneyNumbersAgree M N`, while Theorem 25.1.3
packages the total unoriented cobordism object `N_*` by the polynomial `ZMod 2`-algebra owner
`ThomUnorientedCobordismPolynomialAlgebra`. The source sentence is therefore formalized as a
labeled recall block pointing to those existing detection and algebra-presentation owners rather
than as a new wrapper theorem. -/
#check normalStiefelWhitneyNumbersAgree
#check cobordant_iff_normalStiefelWhitneyNumbersAgree
#check normalStiefelWhitneyNumbersAgree.iff_tangential
#check ThomUnorientedCobordismPolynomialAlgebra
#check thomUnorientedCobordismPolynomialAlgebra_spec
#check thomUnorientedCobordismPolynomialAlgebra_exists
