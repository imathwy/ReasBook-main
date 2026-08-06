import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_1_10

universe u

-- Semantic recall: following Convention 5.2.14, Chapter 6 reuses the Chapter 5 textbook owner
-- for compactly generated spaces, namely the weak Hausdorff + k-space class
-- `CompactlyGeneratedWeakHausdorffSpace`.

/- Assumption 6.1.3: following Convention 5.2.14, the ambient spaces in this chapter are taken
to be compactly generated in the Chapter 5 textbook sense, so the canonical standing hypothesis
for a space `X` is `[CompactlyGeneratedWeakHausdorffSpace X]`. -/
#check (CompactlyGeneratedWeakHausdorffSpace : (X : Type u) → [TopologicalSpace X] → Prop)
