import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_1_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {X : Type u} [TopologicalSpace X]
variable [WeaklyHausdorffSpace X] (s : Set X)

-- The canonical source-facing owner already lives in `Definition_5_1_4` as the subtype instance
-- `Subtype.weaklyHausdorffSpace`, so this problem file reuses that owner directly.

/- Problem 5.3.1: every subspace of a weak Hausdorff space is weak Hausdorff. -/
#check (Subtype.weaklyHausdorffSpace : WeaklyHausdorffSpace s)
