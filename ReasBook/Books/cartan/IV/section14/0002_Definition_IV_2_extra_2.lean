import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: the dedicated `lean_leansearch` tool was unavailable in this runner, so
-- the canonical notion was verified directly in `Mathlib/Analysis/Analytic/Basic.lean`.

/- Definition IV.2-extra-2: for a function on an open set `D`, the canonical owner for the
textbook phrase “analytic in `D`” is `AnalyticOnNhd`; it requires analyticity at each point of
`D`. The within-set variant `AnalyticOn` is only a bridge here, and on open sets it coincides with
`AnalyticOnNhd` via `IsOpen.analyticOn_iff_analyticOnNhd`. -/
recall AnalyticOnNhd
