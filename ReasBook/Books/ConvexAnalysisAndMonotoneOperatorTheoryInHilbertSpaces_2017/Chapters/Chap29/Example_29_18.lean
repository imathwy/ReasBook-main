import Mathlib.Tactic.Recall
import BauschkeLean.Chap03.Example_3_23

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall: `lean_leansearch` surfaced generic affine-projection owners, while local
-- Chapter 3 precedent supplies the exact hyperplane projector owner
-- `projectionPoint_hyperplane_eq_explicit`.

/- Example 29.18 is exactly `projectionPoint_hyperplane_eq_explicit`: for
`C = innerProductLevelSet u η = {z | ⟪z, u⟫_ℝ = η}` and
`P_C = projectionPoint C (hyperplane_isChebyshev u η hu)`, one has
`P_C x = x + ((η - ⟪x, u⟫_ℝ) / ‖u‖ ^ 2) • u`. -/
recall projectionPoint_hyperplane_eq_explicit
