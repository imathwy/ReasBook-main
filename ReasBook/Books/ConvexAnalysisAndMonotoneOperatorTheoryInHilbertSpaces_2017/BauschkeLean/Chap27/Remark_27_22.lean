import Mathlib.Tactic.Recall
import BauschkeLean.Chap27.Proposition_27_21

namespace ERealFunction

/- Source/core/bridge triage:
- `source-facing`: Remark 27.22 is terminological only: the displayed system `(27.52)` is the
  standard Karush--Kuhn--Tucker system attached to the constrained problem `(27.51)`.
- `core/canonical`: the project already owns that displayed differentiable system as
  `ConvexInequalityGradientKKTSystem` in `Proposition_27_21`.
- `bridge/view`: this file is therefore recall-only and does not introduce a parallel wrapper or
  synonym.
-/

/- Remark 27.22: the system `(27.52)`, formalized by the canonical owner
`ConvexInequalityGradientKKTSystem`, is the standard Karush--Kuhn--Tucker system associated with
the constrained minimization problem `(27.51)`. -/
recall ConvexInequalityGradientKKTSystem

end ERealFunction
