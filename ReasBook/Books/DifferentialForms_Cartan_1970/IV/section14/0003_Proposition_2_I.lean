import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: the dedicated `lean_leansearch` tool was unavailable in this runner, so
-- the canonical owner theorem was verified directly in
-- `Mathlib/Analysis/Analytic/ChangeOrigin.lean`.

/- Proposition 2.I is a core/canonical recall item in several-variable analytic theory. The
primitive data is a formal multilinear series `p`; the derived owner statement is
`FormalMultilinearSeries.analyticOnNhd`, asserting that `p.sum` is analytic on its domain of
convergence `Metric.eball 0 p.radius`. No parallel local wrapper is needed here. -/
recall FormalMultilinearSeries.analyticOnNhd
