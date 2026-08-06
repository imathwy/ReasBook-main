import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Tactic.Recall
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap17.Theorem_17_1_3

universe u

-- Semantic recall via `lean_leansearch`: `CategoryTheory.ShortComplex.Splitting` is the canonical
-- split-short-exact owner in the current environment, while `Theorem_17_1_3` already packages the
-- naturality of the universal coefficient sequence by `UniversalCoefficientHomologyNaturality`.
-- Since the source remark does not specify a formal counterexample or universal negation for
-- canonical splitness, this item is recorded as a labeled recall block rather than as a new
-- theorem wrapper.

/- Remark 17.1.5. The naturality of the universal coefficient sequence is formalized by
`UniversalCoefficientHomologyNaturality`. For each coefficient module, the corresponding short
exact sequence is the short complex `UniversalCoefficientHomologySequence.toShortComplex`, and a
chosen splitting of that short complex would be expressed by
`CategoryTheory.ShortComplex.Splitting`. The textbook remark only records that such a splitting is
not canonical in general, so the source-faithful formalization here is a recall block pointing to
the existing naturality and splitting owners rather than a stronger theorem asserting a uniform
splitting. -/
recall UniversalCoefficientHomologyNaturality
    (R : Type u) [CommRing R] (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ) : Type _

#check UniversalCoefficientHomologyNaturality.map
#check UniversalCoefficientHomologySequence.toShortComplex
#check CategoryTheory.ShortComplex.Splitting
