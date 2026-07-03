import Mathlib
import SmoothManifoldsLee.Chap03.Sec03_20.Problem_3_5

-- Declarations for this item will be appended below by the statement pipeline.

open Manifold
open scoped ContDiff Manifold

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

-- `lean_leansearch` was unavailable in this environment, so this item follows the local immersed
-- curve API pattern already used in `Problem_5_10` and `Problem_5_11`.

/-- Problem 5-9: the boundary of the square of side length `2` centered at the origin in `ℝ²`
does not admit any topology and smooth structure for which the inclusion into `ℝ²` is a smooth
immersion. -/
theorem squareBoundary_not_admits_immersed_curve_structure :
    ¬ ∃ t : TopologicalSpace squareBoundary,
        let _ : TopologicalSpace squareBoundary := t
        ∃ _ : ChartedSpace ℝ squareBoundary,
          ∃ _ : IsManifold 𝓘(ℝ) ∞ squareBoundary,
            IsImmersion 𝓘(ℝ) 𝓘(ℝ, Plane) ∞
              (Subtype.val : squareBoundary → Plane) := sorry
