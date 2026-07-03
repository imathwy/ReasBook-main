import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_16_8 (from Chap16) -/
open scoped EuclideanSpace InnerProductSpace

namespace ERealFunction

noncomputable section

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "B" => Metric.closedBall (0 : ℝ²) 1
local notation "x₀" => (!₂[(1 : ℝ), 0] : ℝ²)

-- Proof sketch: Example 16.13 rewrites the subdifferential of `ι[B]` as the normal cone of `B`,
-- and Example 6.39 identifies that normal cone at the boundary point `x₀ = (1,0)` with the
-- nonnegative ray through `x₀`, i.e. `ℝ₊ × {0}`.
/-- The subdifferential of the closed-unit-ball indicator at the boundary point `(1,0)` is
`ℝ₊ × {0}`. -/
theorem subdifferential_indicator_closedUnitBall_boundary_eq :
    (∂ ι[B]) x₀ =
      {u : ℝ² | 0 ≤ u 0 ∧ u 1 = 0} := sorry

-- Proof sketch: the slice `coordinateSliceEuclidean x₀ 0 : t ↦ (t,0)` pulls `ι[B]` back to the
-- indicator of the interval `[-1,1]`; at the endpoint `1`, its subdifferential is `ℝ₊`.
/-- The first coordinate slice through `(1,0)` has subdifferential `ℝ₊` at the boundary point
`1`. -/
theorem subdifferential_indicator_closedUnitBall_firstCoordinateSlice_eq :
    (∂ ((ι[B]) ∘ coordinateSliceEuclidean x₀ 0)) (1 : ℝ) = Set.Ici (0 : ℝ) := sorry

-- Proof sketch: the slice `coordinateSliceEuclidean x₀ 1 : t ↦ (1,t)` pulls `ι[B]` back to the
-- indicator of `{0}`, whose subdifferential at `0` is all of `ℝ`.
/-- The second coordinate slice through `(1,0)` has full subdifferential at `0`. -/
theorem subdifferential_indicator_closedUnitBall_secondCoordinateSlice_eq :
    (∂ ((ι[B]) ∘ coordinateSliceEuclidean x₀ 1)) (0 : ℝ) = (Set.univ : Set ℝ) := sorry

-- Proof sketch: the two one-dimensional slice computations identify the coordinatewise owner from
-- Proposition 16.7 with `ℝ₊ × ℝ = {u | 0 ≤ u 0}`.
/-- At `(1,0)`, the coordinatewise slice subdifferentials from Proposition 16.7 identify with
`ℝ₊ × ℝ`. -/
theorem coordinatewise_subdifferential_indicator_closedUnitBall_boundary_eq :
    {u : ℝ² |
        ∀ i, u i ∈ (∂ ((ι[B]) ∘ coordinateSliceEuclidean x₀ i)) (x₀ i)} =
      {u : ℝ² | 0 ≤ u 0} := sorry

-- Proof sketch: Proposition 16.7 gives the ambient inclusion into the coordinatewise slice
-- subdifferentials. The companion equality above rewrites that right-hand side as `ℝ₊ × ℝ`, while
-- `subdifferential_indicator_closedUnitBall_boundary_eq` identifies the left-hand side with the
-- smaller ray `ℝ₊ × {0}`.
/-- Remark 16.8: for the indicator of the closed unit ball in the canonical Euclidean model of
`ℝ²`, the coordinatewise subdifferential inclusion from Proposition 16.7 is strict at `(1,0)`. -/
theorem indicator_closedUnitBall_strict_subset_coordinatewise_subdifferential :
    (∂ ι[B]) x₀ ⊂
      {u : ℝ² |
        ∀ i, u i ∈ (∂ ((ι[B]) ∘ coordinateSliceEuclidean x₀ i)) (x₀ i)} := sorry

end

end ERealFunction
