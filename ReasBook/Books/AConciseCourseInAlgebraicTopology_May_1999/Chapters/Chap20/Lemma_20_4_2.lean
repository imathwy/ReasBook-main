import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.Sets.Opens
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Construction_9_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Construction_14_1_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap15.IntegralReducedHomology
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Proposition_20_1_3

open CategoryTheory
open CategoryTheory.Limits
open scoped Topology

noncomputable section

-- Semantic recall via local Chapter 20 precedent: `rSingularHomology` is the chapter-local
-- ordinary singular-homology owner, and Chapter 15 already exposes the canonical reduced owner
-- `integralReducedHomology`. For this item, the source-facing labeled statement is the ordinary
-- homology vanishing theorem on `rSingularHomology ℤ`, with the explicit exceptional
-- `(n, i) = (0, 0)` case excluded; the reduced-homology/basepoint statement is a companion bridge
-- on the reduced owner.

/-- Lemma 20.4.2: if `U` is open in `ℝ^n`, then the ordinary singular homology of `U` with
integral coefficients vanishes in degrees `i ≥ n`, away from the exceptional case
`(n, i) = (0, 0)`. -/
theorem isZero_rSingularHomology_openSubsetEuclideanSpace_of_le_of_not_both_zero
    {n i : ℕ} (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))) (hi : n ≤ i)
    (h_not_both_zero : n ≠ 0 ∨ i ≠ 0) :
    IsZero (rSingularHomology ℤ i (TopCat.of U)) := sorry

/-- Open subsets of `ℝ^n` have trivial ordinary singular homology with integral coefficients in
degrees strictly above `n`. This companion isolates the dimension-only vanishing that does not
require the top-degree noncompactness input. -/
theorem isZero_rSingularHomology_openSubsetEuclideanSpace_of_lt
    {n i : ℕ} (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))) (hi : n < i) :
    IsZero (rSingularHomology ℤ i (TopCat.of U)) := by
  have hi_pos : 0 < i := lt_of_le_of_lt (Nat.zero_le n) hi
  exact isZero_rSingularHomology_openSubsetEuclideanSpace_of_le_of_not_both_zero U
    (Nat.le_of_lt hi) (Or.inr (Nat.pos_iff_ne_zero.mp hi_pos))

/-- Companion bridge: if `U` is open in `ℝ^n`, then for every basepoint `u : U` and every
Chapter 13 integral pair-homology theory `H`, the canonical reduced integral homology of `U`
vanishes in degrees `i ≥ n`. -/
theorem isZero_basedReducedHomology_openSubsetEuclideanSpace_of_le
    (H : PairHomologyTheory ℤ) {n i : ℕ}
    (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n))) (hi : n ≤ i) (u : U) :
    IsZero (integralReducedHomology H i (underTopOfPoint U u)) :=
  sorry

/-- Positive ambient dimension rules out the lone ordinary-homology exception in
`isZero_rSingularHomology_openSubsetEuclideanSpace_of_le_of_not_both_zero`. -/
theorem isZero_rSingularHomology_openSubsetEuclideanSpace_of_pos_of_le
    {n i : ℕ} (hn : 0 < n) (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)))
    (hi : n ≤ i) :
    IsZero (rSingularHomology ℤ i (TopCat.of U)) :=
  isZero_rSingularHomology_openSubsetEuclideanSpace_of_le_of_not_both_zero U hi
    (Or.inl (Nat.pos_iff_ne_zero.mp hn))
