import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: the dedicated `lean_leansearch` tool was unavailable in this runner, so
-- the canonical notion was verified directly in `Mathlib/Analysis/Analytic/Basic.lean`.

/- Definition IV.2-extra-1: for a two-variable map viewed as `f : 𝕜 × 𝕜 → F`, the textbook phrase
that `f` has a power series expansion at `(x₀, y₀)` is the canonical owner notion
`AnalyticAt 𝕜 f (x₀, y₀)`. The primitive witness data is a `FormalMultilinearSeries` packaged by
`HasFPowerSeriesAt`; `AnalyticAt` is the correct public abstraction, and `AnalyticOnNhd` is the
derived pointwise-on-a-set notion used in the next item. -/
recall AnalyticAt
