import Mathlib.Tactic.Recall
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap12.Lemma_12_2_4

-- Semantic recall: the canonical mathlib homotopy-invariance theorem is
-- `Homotopy.homologyMap_eq`, and `homologyMap_eq_of_chainHomotopy` is its
-- `ChainComplex (ModuleCat R) ℕ` specialization already recorded in Lemma 12.2.4.

/- Remark 12.2.5. Chain homotopy is the algebraic shadow of topological homotopy because
chain-homotopic chain maps induce the same morphism on homology. In this chapter, that
homotopy-invariance mechanism is the specialized theorem
`homologyMap_eq_of_chainHomotopy`; its canonical mathlib source is `Homotopy.homologyMap_eq`. -/
recall homologyMap_eq_of_chainHomotopy
recall Homotopy.homologyMap_eq
