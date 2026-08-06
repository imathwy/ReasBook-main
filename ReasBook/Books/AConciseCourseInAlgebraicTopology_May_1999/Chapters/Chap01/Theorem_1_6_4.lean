import Mathlib.Dynamics.FixedPoints.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.ClosedUnitDisk
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Construction_1_6_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ClosedUnitDisk
open scoped ContinuousMap

/-- Theorem 1.6.4: every continuous self-map of the closed unit disk `D²` has a fixed point. -/
-- Proof sketch: argue by contradiction. If `f` had no fixed point, then
-- `fixedPointFreeDiskRetraction` would give a continuous retraction of the disk onto its boundary
-- circle, contradicting `no_continuous_retraction_closed_unit_disk_to_circle`.
theorem brouwer_fixed_point_closed_unit_disk
    (f : C(D², D²)) :
    ∃ x : D², Function.IsFixedPt f x := by
  by_contra hf
  have hf' : ∀ x : D², f x ≠ x := by
    simpa [Function.IsFixedPt] using hf
  exact no_continuous_retraction_closed_unit_disk_to_circle
    ⟨fixedPointFreeDiskRetraction f hf',
      fixedPointFreeDiskRetraction_comp_circleBoundaryInclusion f hf'⟩

/-- The canonical fixed-point set of a continuous self-map of `D²` is nonempty. -/
theorem brouwer_fixed_point_closed_unit_disk_fixedPoints_nonempty
    (f : C(D², D²)) :
    (Function.fixedPoints f).Nonempty := by
  rcases brouwer_fixed_point_closed_unit_disk f with ⟨x, hx⟩
  exact ⟨x, hx⟩
