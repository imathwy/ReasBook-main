import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open Metric Set

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The distance-based potential `x ↦ (‖x‖² - d_C(x)²) / 2` associated to a set in a real inner
product space. -/
noncomputable def euclidean_distance_potential (C : Set E) : E → ℝ :=
  fun x ↦ (‖x‖ ^ 2 - infDist x C ^ 2) / 2

-- Proof sketch: expand `Metric.infDist` as the infimum of the distance function, use the identity
-- `‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * inner ℝ y x + ‖y‖ ^ 2`, and rewrite a constant minus an infimum
-- as the corresponding supremum.
/-- The distance-based potential agrees with the supremum of the affine functions
`x ↦ inner ℝ y x - ‖y‖² / 2` indexed by `y ∈ C`. -/
theorem euclidean_distance_potential_eq_sSup_affine (C : Set E) (hC : C.Nonempty) (x : E) :
    euclidean_distance_potential C x =
      sSup ((fun y : E ↦ inner ℝ y x - (‖y‖ ^ 2) / 2) '' C) := sorry

-- Proof sketch: if `C = ∅`, then `Metric.infDist x C = 0`, so the function is `x ↦ ‖x‖² / 2`,
-- which is convex. Otherwise rewrite with `euclidean_distance_potential_eq_sSup_affine`; each term
-- `x ↦ inner ℝ y x - ‖y‖² / 2` is affine, hence convex, and a pointwise supremum of such affine
-- functions is convex.
/-- Example 2.5: for a subset `C` of a real inner product space, the function
`x ↦ (‖x‖² - d_C(x)²) / 2` is convex. -/
theorem euclidean_distance_potential_convex (C : Set E) :
    ConvexOn ℝ univ (euclidean_distance_potential C) := sorry

end
