module

import Mathlib.Analysis.InnerProductSpace.PiL2

variable {n : ℕ} (x y z : EuclideanSpace ℝ (Fin n))

/- Exercise 20.9 (a): the Euclidean dot product is the real inner product, whose
coordinate formula and additivity are already provided by the inner-product API. -/
#check PiLp.inner_apply
#check Real.inner_apply
#check (inner_add_right x y z : inner ℝ x (y + z) = inner ℝ x y + inner ℝ x z)

/- Exercise 20.9 (b): the Cauchy–Schwarz inequality. -/
#check (abs_real_inner_le_norm x y : |inner ℝ x y| ≤ ‖x‖ * ‖y‖)

/- Exercise 20.9 (c): the triangle inequality for the Euclidean norm. -/
#check (norm_add_le x y : ‖x + y‖ ≤ ‖x‖ + ‖y‖)

/- Exercise 20.9 (d): the Euclidean distance formula is carried by the canonical
metric-space instance on `EuclideanSpace ℝ (Fin n)`. -/
#check (inferInstance : MetricSpace (EuclideanSpace ℝ (Fin n)))
#check (EuclideanSpace.dist_eq x y :
  dist x y = Real.sqrt (∑ i, dist (x i) (y i) ^ 2))
