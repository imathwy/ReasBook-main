import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Immersion
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Definition_23_4_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.RealProjectiveSpaceManifold
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Problem_23_9_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_3_1

open scoped Manifold

/-
Problem 23.9.2 uses the nonzero top dual Stiefel–Whitney class of
`RealProjectiveSpace (2 ^ k)`: an immersion in the stated target would provide a normal bundle of
rank `2 ^ k - 2`, so its class in degree `2 ^ k` would vanish by the dimension axiom, contradicting
the projective-space computation.  The current Chapter 23 API does not yet package the required
normal-bundle Whitney-sum comparison, so the source-faithful proof is kept as one explicit gap.
-/

/-- Problem 23.9.2: `RealProjectiveSpace (2 ^ k)` with its standard smooth manifold structure does
not immerse into `EuclideanSpace ℝ (Fin (2 ^ (k + 1) - 2))`. -/
theorem realProjectiveSpace_pow_two_not_immerses
    (k : ℕ) :
    ¬ ∃ f : RealProjectiveSpace (2 ^ k) → EuclideanSpace ℝ (Fin (2 ^ (k + 1) - 2)),
        Manifold.IsImmersion (𝓡 (2 ^ k)) (𝓡 (2 ^ (k + 1) - 2)) ⊤ f := by
  sorry
