import Mathlib.Tactic.Recall
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Theorem_13_1_1

universe u

-- Semantic recall via `lean_leansearch` only surfaced unrelated `groupHomology.H0` API. Local
-- Chapter 13 precedent and the `PairHomologyTheory` owner itself show that this item is already
-- packaged canonically by the fields checked below.

/- Axiom 13.1.2. The dimension axiom says that `SpacePair.point` has degree-`0` homology
isomorphic to the coefficient group `π` and higher homology zero. In this workspace this is
exactly the pair of fields `PairHomologyTheory.dimensionZero` and
`PairHomologyTheory.dimensionHigher` on `PairHomologyTheory`. -/
recall PairHomologyTheory.dimensionZero {π : Type u} [AddCommGroup π]
    (H : PairHomologyTheory π) :
    Nonempty ((H 0).obj SpacePair.point ≅ ModuleCat.of ℤ π)

recall PairHomologyTheory.dimensionHigher {π : Type u} [AddCommGroup π]
    (H : PairHomologyTheory π) (q : ℤ) (hq : q ≠ 0) :
    CategoryTheory.Limits.IsZero ((H q).obj SpacePair.point)

recall SpacePair.point : SpacePair
