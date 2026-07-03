import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 2.20: the function equal to `exp (-1 / t)` for `t > 0` and `0` for `t ≤ 0` is smooth.
Mathlib's canonical owner theorem for this cutoff is `expNegInvGlue.contDiff`; manifold
smoothness is the standard derived `ContDiff`-to-`ContMDiff` bridge, so no local wrapper is
needed here. -/
recall expNegInvGlue.contDiff
