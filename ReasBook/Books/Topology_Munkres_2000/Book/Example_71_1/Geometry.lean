module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.PNat.Basic

public section

namespace InfiniteEarring

/-- The Euclidean plane containing the infinite earring. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The center `(1 / n, 0)` of the `n`th circle of the infinite earring. -/
noncomputable def center (n : ℕ+) : Plane :=
  WithLp.toLp 2 ![(n : ℝ)⁻¹, 0]

/-- Helper for Example 71.1: the coordinates of the center of the `n`th circle. -/
lemma center_apply (n : ℕ+) (i : Fin 2) :
    center n i = ![(n : ℝ)⁻¹, 0] i := by
  -- The `WithLp` wrapper preserves the underlying coordinate function.
  rfl

/-- The circle of radius `1 / n` centered at `(1 / n, 0)`. -/
def circle (n : ℕ+) : Set Plane :=
  Metric.sphere (center n) (n : ℝ)⁻¹

/-- Helper for Example 71.1: membership in a component circle is its defining
metric sphere equation. -/
lemma mem_circle_iff (x : Plane) (n : ℕ+) :
    x ∈ circle n ↔ dist x (center n) = (n : ℝ)⁻¹ := by
  -- Unfold the circle once and use the standard sphere membership theorem.
  rw [circle, Metric.mem_sphere]

end InfiniteEarring
