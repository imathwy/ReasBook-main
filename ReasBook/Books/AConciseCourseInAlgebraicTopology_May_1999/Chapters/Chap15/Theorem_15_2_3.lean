import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap15.Theorem_15_2_3.Comparison

noncomputable section

open CategoryTheory Limits
open Topology

/-- Theorem 15.2.3: relative cellular homology with coefficients in `π` determines a bundled
CW-pair homology theory `E` together with explicit relative cellular models for every
nonnegative degree `q` and CW pair `P`, vanishes in negative degrees, and every pair homology
theory `H` restricts to `E` through a degreewise natural isomorphism compatible with the
connecting morphisms. This keeps the relative cellular construction visible through
`CWPairHomologyTheory.RelativeCellularHomologyModel` while placing the comparison on the
canonical Chapter 13 surface `CWPairHomologyTheory` / `HasCWPairTheoryComparison`. -/
theorem exists_relativeCellularCWPairTheoryComparison
    (π : Type) [AddCommGroup π] :
    ∃ E : CWPairHomologyTheory π,
      ∃ models : E.RelativeCellularModels,
        E.VanishesInNegativeDegrees ∧
        ∀ H : PairHomologyTheory π,
          ∃ e : E.ComparisonIso H,
            E.HasComparison H e := by
  sorry

/-- Companion to Theorem 15.2.3: the cellular comparison can be chosen so that, for each degree
`q` and CW pair `P`, the boundary square commutes as an equality of composites. -/
theorem exists_relativeCellularCWPairTheoryBoundaryComm
    (π : Type) [AddCommGroup π] :
    ∃ E : CWPairHomologyTheory π,
      ∃ _ : E.RelativeCellularModels,
        E.VanishesInNegativeDegrees ∧
        ∀ H : PairHomologyTheory π,
          ∃ e : E.ComparisonIso H,
            ∀ q : ℤ, ∀ P : CWPair,
              ((e q).hom.app P) ≫ (CWPairHomologyTheory.boundary E q).app P =
                ((H.boundary q).app (IsCWPair.toSpacePair P)) ≫
                  ((e (q - 1)).hom.app (IsCWPair.subspacePair P)) := by
  rcases exists_relativeCellularCWPairTheoryComparison π with ⟨E, model, hNeg, hE⟩
  refine ⟨E, model, hNeg, ?_⟩
  intro H
  rcases hE H with ⟨e, he⟩
  refine ⟨e, ?_⟩
  intro q P
  exact CWPairHomologyTheory.hasComparison_boundary_comm he q P
