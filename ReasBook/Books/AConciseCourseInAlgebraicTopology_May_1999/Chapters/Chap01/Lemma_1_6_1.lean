import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.ClosedUnitDisk

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ClosedUnitDisk

/-- Lemma 1.6.1: the fundamental group of the closed unit disk `D²` is trivial at any basepoint. -/
-- Proof sketch: `D²` is contractible, hence simply connected, so the quotient of loops at `x` up
-- to homotopy is subsingleton.
instance fundamental_group_closed_unit_disk_subsingleton (x : D²) :
    Subsingleton (FundamentalGroup D² x) := by
  change Subsingleton (Path.Homotopic.Quotient x x)
  infer_instance

/-- Every element of the fundamental group of the closed unit disk is the identity. -/
-- Proof sketch: once `π₁(D², x)` is subsingleton, every loop class coincides with `1`.
theorem fundamental_group_closed_unit_disk_eq_one (x : D²) (γ : FundamentalGroup D² x) :
    γ = 1 := by
  exact Subsingleton.elim _ _
