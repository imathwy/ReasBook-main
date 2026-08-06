import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Definition_24_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Proposition_24_1_3

open ComplexVectorBundle

universe u

-- Semantic recall: `lean_leansearch` surfaced `Algebra.GrothendieckAddGroup` as the canonical
-- owner for formal differences, and local Chapter 24 precedent uses `complexKTheory` together
-- with `ComplexVectorBundle.toVirtualPresentation` for honest bundle classes.

section

variable {X : Type u} [TopologicalSpace X] [CompactSpace X]

/-- Corollary 24.1.4: every virtual bundle class in `complexKTheory X` can be written as the
class of an honest complex vector bundle minus a nonnegative integer multiple of the trivial
line-bundle class. -/
theorem complexKTheory_eq_toVirtualPresentation_sub_nsmul_one
    (x : complexKTheory X) :
    ∃ V : Presentation X, ∃ q : ℕ,
      x = toVirtualPresentation V - q • (1 : complexKTheory X) := sorry

/-- Corollary 24.1.4 in the equivalent nat-cast form used elsewhere in this chapter. -/
theorem complexKTheory_eq_toVirtualPresentation_sub_nat
    (x : complexKTheory X) :
    ∃ V : Presentation X, ∃ q : ℕ,
      x = toVirtualPresentation V - (q : complexKTheory X) := by
  simpa using complexKTheory_eq_toVirtualPresentation_sub_nsmul_one x

end
