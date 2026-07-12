import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Remark 3.15-extra-5: in Lean, the coordinate vectors attached to a local coordinate system are
encoded by the differential of the inverse chart map on the tangent bundle. Thus the vector
corresponding to the `i`-th coordinate direction is determined by the whole inverse chart, not by
the single coordinate function `x^i` alone; changing the remaining coordinate functions can change
the resulting tangent vector. This chart-level dependence is expressed by the canonical mathlib
theorem `tangentMap_chart_symm`. -/
recall tangentMap_chart_symm
