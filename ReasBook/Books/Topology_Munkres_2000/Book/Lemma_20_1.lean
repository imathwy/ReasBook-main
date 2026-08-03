module

public import Topology_Munkres_2000.Book.Definition_20_1

public section

/- Lemma 20.1 (1): If `ε > 0`, then the center `x` belongs to
`Metric.ball x ε`. -/
#check Metric.mem_ball_self

namespace Metric

/-- Lemma 20.1 (2): If `y ∈ Metric.ball x ε`, then the explicit radius
`ε - dist x y` is positive and its ball about `y` is contained in `Metric.ball x ε`. -/
theorem ball_sub_dist_subset {α : Type u} [PseudoMetricSpace α] {x y : α} {ε : ℝ}
    (hy : y ∈ ball x ε) :
    0 < ε - dist x y ∧ ball y (ε - dist x y) ⊆ ball x ε :=
  ⟨sub_pos.2 (by simpa [dist_comm] using hy),
    ball_subset <| by rw [dist_comm, sub_sub_self]⟩

end Metric
