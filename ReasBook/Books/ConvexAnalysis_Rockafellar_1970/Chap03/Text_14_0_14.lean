import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_14_0_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

open scoped Rockafellar

local notation "R2" => EuclideanSpace ℝ (Fin 2)
local notation "e1" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "D" => (Metric.closedBall e1 1 : Set R2)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 14.0.14 gives an explicit planar example, identifying the polar of the
  closed unit disk centered at `(1, 0)` by a coordinate inequality.
- `core/canonical`: the owner abstractions are the set polar `Set.polar` and the metric closed
  ball `Metric.closedBall a r`, with `supportFunction_closedBall` giving the owner-side support
  function formula for that disk.
- `bridge/view`: the textbook coordinates `(ξ₁, ξ₂)` and `(ξ₁⋆, ξ₂⋆)` are rendered directly by the
  two coordinates of `R2 = EuclideanSpace ℝ (Fin 2)`, while the phrase “closed unit disk centered
  at `(1, 0)`” is rendered canonically by `Metric.closedBall e1 1`; the displayed coordinate
  parabola is the coordinate form of the owner inequality `xStar 0 + ‖xStar‖ ≤ 1`.

Domain-style sampling used here:
- the source-facing owner `Set.polar`;
- the membership reformulation `Set.mem_polar_iff`;
- the canonical Euclidean-ball owner `Metric.closedBall a r`;
- the nearby chapter support-function owner theorem `supportFunction_closedBall`.

Primitive data vs derived API:
- primitive data: the canonical closed disk `D = Metric.closedBall e1 1`, i.e. the closed unit
  disk centered at `e1`;
- derived API: the owner-side polar equality
  `Dᵒ = {xStar | xStar 0 + ‖xStar‖ ≤ 1}` and its coordinate parabola reformulation.

Layer target: `source-facing`; the main theorem keeps the intrinsic owner inequality for the
polar of the canonical closed ball, while the displayed coordinate parabola appears only as a
derived `bridge/view` reformulation.
-/

-- Proof sketch: unfold `Set.polar`, so the claim becomes the support-function sublevel condition
-- for the closed ball, then evaluate that support function with
-- `supportFunction_closedBall e1 1 (by positivity)`. Since `⟪xStar, e1⟫ = xStar 0`, this yields
-- the
-- owner inequality `xStar 0 + ‖xStar‖ ≤ 1`.
/-- Text 14.0.14, owner form: the polar of the closed unit disk centered at `(1, 0)`,
formalized canonically as `D = Metric.closedBall e1 1`, is the set of `xStar` satisfying the
intrinsic inequality `xStar 0 + ‖xStar‖ ≤ 1`. -/
theorem polar_unit_disk_centered_at_one_zero_eq :
    Dᵒ[ℝ] = {xStar : R2 | xStar 0 + ‖xStar‖ ≤ (1 : ℝ)} := sorry

-- Proof sketch: start from the owner-form theorem above. The inequality `xStar 0 + ‖xStar‖ ≤ 1`
-- is equivalent to `‖xStar‖ ≤ 1 - xStar 0`, which forces `xStar 0 ≤ 1` and can therefore be
-- squared without changing its meaning. Expanding `‖xStar‖ ^ 2 = (xStar 0) ^ 2 + (xStar 1) ^ 2`
-- then simplifies the owner inequality to the displayed coordinate parabola.
/-- Text 14.0.14, coordinate reformulation: the owner inequality
`xStar 0 + ‖xStar‖ ≤ 1` for the polar of the shifted unit disk is equivalent to the parabola
equation `xStar 0 ≤ (1 - (xStar 1)^2) / 2`. -/
theorem polar_unit_disk_centered_at_one_zero_eq_parabola :
    Dᵒ[ℝ] = {xStar : R2 | xStar 0 ≤ (1 - (xStar 1) ^ 2) / 2} := sorry

end
