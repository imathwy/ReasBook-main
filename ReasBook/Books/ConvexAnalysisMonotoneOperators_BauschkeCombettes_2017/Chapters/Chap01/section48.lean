import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_1_48 (from Chap01) -/
universe u

/-- Example 1.48: the textbook estimate (1.67) is the pointwise form of the canonical
`1`-Lipschitz estimate for `x ↦ Metric.infDist x C`; the book's nonemptiness hypothesis is
unnecessary for this inequality. -/
theorem abs_infDist_sub_infDist_le_dist {α : Type u} [PseudoMetricSpace α] {C : Set α} (x y : α) :
    |Metric.infDist x C - Metric.infDist y C| ≤ dist x y := by
  simpa [Real.dist_eq, one_mul] using (Metric.lipschitz_infDist_pt C).dist_le_mul x y
