module

public import Topology_Munkres_2000.Book.Example_51_1.Homotopy

@[expose] public section

universe u

variable {X : Type u} [TopologicalSpace X]

/- Example 51.1 (1): Straight-line interpolation gives a homotopy between continuous maps
from `X` to `ℝ × ℝ`. -/
#check fun (f g : C(X, ℝ × ℝ)) ↦ ContinuousMap.Homotopy.affine f g

/- Example 51.1 (2): Straight-line interpolation gives a fixed-endpoint homotopy between paths
in `ℝ × ℝ`. -/
#check fun {x₀ x₁ : ℝ × ℝ} (p q : Path x₀ x₁) ↦ Path.Homotopy.affine p q

namespace Convex

variable {E : Type u} [AddCommGroup E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [Module ℝ E] [ContinuousSMul ℝ E]
  {s : Set E} (hconv : Convex ℝ s) {x₀ x₁ : s} (p q : Path x₀ x₁)

include hconv

/-- Example 51.1: Any two paths with common endpoints in a convex set are path homotopic. -/
theorem pathsHomotopic : p.Homotopic q := by
  -- Package the straight-line path homotopy as the required witness.
  exact Nonempty.intro (pathHomotopy hconv p q)

end Convex
