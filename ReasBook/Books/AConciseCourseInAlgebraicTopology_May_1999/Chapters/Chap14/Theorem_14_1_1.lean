import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Theorem_13_1_7

open CategoryTheory

universe u

-- Semantic recall via `lean_leansearch` surfaced only generic homological-complex restriction
-- lemmas, not a canonical owner for this uniqueness theorem. Local Chapter 13 precedent already
-- provides the bundled source-facing owner `CWPairHomologyTheory` together with
-- `restrictPairHomologyTheoryToCWPairs` and the direct comparison API
-- `HasCWPairTheoryComparison H E.2 e`, so this item should compare two pair homology theories
-- through a common bundled restricted CW-pair theory and conclude uniqueness up to
-- `PairHomologyTheory.Iso`.

/-- Theorem 14.1.1: a generalized homology theory on pairs of spaces is determined by its
restriction to CW pairs. Concretely, if two Chapter 13 pair homology theories induce the same
bundled restricted CW-pair homology theory up to degreewise natural isomorphism compatible with
the bundled CW-pair theory structure on `E`, then they are isomorphic as pair homology theories
in a way that respects those supplied comparison isomorphisms. -/
theorem pairHomologyTheory_iso_of_restrictToCWPairs
    {π : Type u} [AddCommGroup π] (H K : PairHomologyTheory π)
    (E : CWPairHomologyTheory π)
    (eH : ∀ q : ℤ, restrictPairHomologyTheoryToCWPairs H q ≅ E q)
    (hH : HasCWPairTheoryComparison H E.2 eH)
    (eK : ∀ q : ℤ, restrictPairHomologyTheoryToCWPairs K q ≅ E q)
    (hK : HasCWPairTheoryComparison K E.2 eK) :
    ∃ i : PairHomologyTheory.Iso H K,
      PairHomologyTheory.Iso.RespectsCWPairComparison i eH eK := sorry
