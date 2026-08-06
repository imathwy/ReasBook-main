import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.Theorem_19_4_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.Lemma_19_4_4

open CategoryTheory CategoryTheory.Limits

universe u

-- Semantic recall via `lean_leansearch` only surfaced general Mittag-Leffler APIs, so this file
-- uses the shared `ExpandingUnion` owner together with the Chapter 19 continuity API
-- `ExpandingUnion.cohomologyInverseSequence` and `ExpandingUnion.restrictionToLimit`.

namespace ExpandingUnion

/-- Corollary 19.4.5: if the inverse sequence
`U.cohomologyInverseSequence (PairCohomologyTheory.absoluteCohomology E) (q - 1)` of the stagewise
absolute cohomology groups of an expanding union `U` satisfies the Mittag-Leffler condition, then
the canonical comparison morphism
`U.restrictionToLimit (PairCohomologyTheory.absoluteCohomology E) q` from the absolute cohomology
of `X` to the inverse limit of the stage cohomology groups is an isomorphism. -/
theorem restrictionToLimitAbsoluteCohomology_isIso_of_mittagLeffler
    {X : TopCat.{u}} (U : ExpandingUnion X) {π : Type u} [AddCommGroup π]
    (E : PairCohomologyTheory π) (q : ℤ)
    (hU :
      (U.cohomologyInverseSequence
        (PairCohomologyTheory.absoluteCohomology E) (q - 1)).MittagLeffler) :
    IsIso (U.restrictionToLimit (PairCohomologyTheory.absoluteCohomology E) q) := by
  rcases U.milnorShortExactSequence E q with ⟨δ, hδ⟩
  let T : ShortComplex Ab.{u} :=
    ShortComplex.mk δ (U.restrictionToLimit (PairCohomologyTheory.absoluteCohomology E) q) hδ.zero
  have hT : T.ShortExact := by
    simpa [T] using hδ.shortExact
  have hzero : IsZero T.X₁ := by
    change IsZero
      ((U.cohomologyInverseSequence (PairCohomologyTheory.absoluteCohomology E) (q - 1)).limOne)
    simpa using
      InverseSequence.isZero_limOne_of_mittagLeffler
        (U.cohomologyInverseSequence (PairCohomologyTheory.absoluteCohomology E) (q - 1)) hU
  change IsIso T.g
  exact (ShortComplex.ShortExact.isIso_g_iff hT).2 hzero

instance instIsIsoRestrictionToLimitAbsoluteCohomologyOfMittagLeffler
    {X : TopCat.{u}} (U : ExpandingUnion X) {π : Type u} [AddCommGroup π]
    (E : PairCohomologyTheory π) (q : ℤ)
    (hU :
      (U.cohomologyInverseSequence
        (PairCohomologyTheory.absoluteCohomology E) (q - 1)).MittagLeffler) :
    IsIso (U.restrictionToLimit (PairCohomologyTheory.absoluteCohomology E) q) :=
  restrictionToLimitAbsoluteCohomology_isIso_of_mittagLeffler U E q hU

end ExpandingUnion
