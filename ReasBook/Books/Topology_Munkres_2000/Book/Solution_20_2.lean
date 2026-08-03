module

import Mathlib.Topology.MetricSpace.Pseudo.Pi

/- Solution 20.2: the square metric on `Fin n → ℝ` satisfies the triangle inequality. -/
#check fun {n : ℕ} (x y z : Fin n → ℝ) ↦
  (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

/- The canonical finite Pi-space distance is the supremum of the coordinate distances,
which is the textbook maximum for a nonempty finite coordinate type. -/
#check fun {n : ℕ} (x y : Fin n → ℝ) ↦ dist_pi_def x y
