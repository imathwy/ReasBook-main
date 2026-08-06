import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Theorem_10_7_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Theorem_10_7_10

-- Semantic recall via `lean_leansearch`: no separate canonical owner surfaced for a conclusion
-- whose content is that the CW-approximation theorem for excisive triads follows from earlier
-- ingredients. The source-faithful item surface is therefore a labeled recall block pointing
-- directly to the existing theorem `exists_cwTriadApproximation` and the weak-equivalence input
-- `Triad.isWeakEquivalence_of_excisiveTriadMap`.

/- Conclusion 10.7.14: the CW approximation theorem for excisive triads is formalized by
`exists_cwTriadApproximation`, and the weak-equivalence theorem for excisive triad maps used in
its derivation is `Triad.isWeakEquivalence_of_excisiveTriadMap`. Since the source sentence records
this deduction rather than introducing a new mathematical owner, the faithful formalization here
is a labeled recall block rather than a duplicate theorem wrapper. -/
#check exists_cwTriadApproximation
#check Triad.isWeakEquivalence_of_excisiveTriadMap
