import Mathlib.Tactic.Recall
import SmoothManifolds_Lee_2012.Chap06.Sec06_39.Corollary_6_11

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain sampling for this refine pass checked the Section 6.38 owner
-- `has_measure_zero_in_manifold`, its preferred-chart consequence
-- `has_measure_zero_in_manifold.extChartAt_volume_eq_zero`, and Corollary 6.11's canonical
-- chartwise bridge theorem.

/- Problem 6-1 is a bridge/view item.
Source-facing content: the chartwise measure-zero conclusion for `Set.range F`.
Core/canonical owner: `has_measure_zero_in_manifold`.
Bridge/view owner already present upstream: the canonical theorem
`range_has_measure_zero_in_manifold_of_contMDiff_of_model_finrank_lt_chartwise`.
This file therefore recalls that existing bridge directly instead of introducing a parallel local
wrapper with a presentation-branded name.
-/
recall range_has_measure_zero_in_manifold_of_contMDiff_of_model_finrank_lt_chartwise
