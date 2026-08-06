import Mathlib.Algebra.Ring.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.ComplexKTheoryAdams

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped ComplexKTheoryAdams

/-- Every complex line-bundle class is a unit in `complexKTheory X`. -/
theorem complexKTheoryLineBundle_isUnit
    (X : Type u) [TopologicalSpace X] [CompactSpace X]
    (L : ComplexPlaneBundle 1 X) :
    IsUnit (lineBundleKTheoryClass L) := sorry

/-- Every complex line-bundle class admits a unit lift. -/
theorem complexKTheoryLineBundle_existsLift
    (X : Type u) [TopologicalSpace X] [CompactSpace X]
    (L : ComplexPlaneBundle 1 X) :
    ∃ u : Units (complexKTheory X), IsLineBundleKTheoryLift L u := by
  simpa [IsLineBundleKTheoryLift] using complexKTheoryLineBundle_isUnit X L

/-- Theorem 24.5.1. There exists a family of Adams operations `ψ^k : K(X) → K(X)`, indexed by
the nonzero integers, consisting of natural ring endomorphisms satisfying `ψ^1 = id`,
`ψ^k ∘ ψ^l = ψ^(k * l)`, and `ψ^k(L) = L ^ k` on line-bundle classes. -/
theorem complexKTheoryAdams_exists :
    ∃ ψ : ComplexKTheoryAdamsFamily, IsComplexKTheoryAdams ψ := sorry
