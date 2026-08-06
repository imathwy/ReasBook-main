import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.ComplexVectorBundle

-- Declarations for this item will be appended below by the statement pipeline.

open ComplexVectorBundle

universe u v

-- Semantic recall: `lean_leansearch` surfaced `Bundle.Trivial.vectorBundle` as the canonical
-- trivial-bundle owner, and local Chapter 24 precedent uses `ComplexVectorBundle.Presentation`,
-- `ComplexVectorBundle.trivialRank`, `ComplexVectorBundle.whitneySum`, and
-- `ComplexVectorBundle.Iso` for honest bundle statements.

section

variable {X : Type u} [TopologicalSpace X]

/-- Proposition 24.1.3: every honest finite-rank complex vector bundle over a compact space admits
a complementary honest finite-rank complex vector bundle and a bundle isomorphism from their
Whitney sum to a trivial complex vector bundle of some finite rank. -/
theorem ComplexVectorBundle.Presentation.exists_complementary_whitneySum_trivial
    [CompactSpace X] (V : Presentation.{u, v} X) :
    ∃ (W : Presentation.{u, v} X) (m : ℕ),
      Nonempty (Iso (whitneySum V W) (trivialRank.{u, v} X m)) := sorry

end
