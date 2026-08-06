import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_3_1

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall via `lean_leansearch` did not surface a finer imported owner for the Section
-- 23.6 construction than the Chapter 23 pair
-- `StandardStiefelWhitneyNormalization` / `existsUnique_stiefelWhitneyTheory`. In this
-- development, the Thom-class input from Lemma 23.6.1 and Theorem 23.5.4 is represented by the
-- standard degree-`1` normalization datum on `RealProjectiveInfinity`, so this construction is
-- a direct bridge from that normalization datum to the canonical Chapter 23 existence theorem.

noncomputable section

/- Construction 23.6.2. Once the Thom class of the universal line bundle determines a standard
degree-`1` normalization datum on `RealProjectiveInfinity`, the splitting principle together with
the Whitney formula yields a Stiefel-Whitney theory whose degree-`1` class on the universal line
bundle is the standard generator of `H¹(RP^∞; ZMod 2)`. In this development, the Thom-class input
from Lemma 23.6.1 and Theorem 23.5.4 is represented by
`StandardStiefelWhitneyNormalization H2`. -/
theorem exists_stiefelWhitneyTheory_with_standard_degreeOneClass
    (H2 : ModTwoCohomologyTheory) (normalizationData : StandardStiefelWhitneyNormalization H2) :
    ∃ w : StiefelWhitneyClassFamily H2,
      IsStiefelWhitneyTheory H2 normalizationData.toStiefelWhitneyNormalization w ∧
        IsStandardRealProjectiveGenerator
          ((H2.comparison 1 (TopCat.of RealProjectiveInfinity)).hom
            ((w 1 1)
              ((RealPlaneBundle.classOf 1 normalizationData.tautologicalLineBundle) :
                RealPlaneBundle.classes 1 (TopCat.of RealProjectiveInfinity)))) := by
  rcases exists_stiefelWhitneyTheory H2 normalizationData with ⟨w, hw⟩
  refine ⟨w, hw, ?_⟩
  simpa [StandardStiefelWhitneyNormalization.degreeOneGenerator, hw.normalization] using
    StandardStiefelWhitneyNormalization.degreeOneGenerator_isStandard normalizationData
