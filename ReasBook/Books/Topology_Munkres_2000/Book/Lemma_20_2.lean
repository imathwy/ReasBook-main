module

public import Topology_Munkres_2000.Book.Definition_20_1
import Mathlib.Topology.Order

public section

universe u

namespace PseudoMetricSpace

/-- The open ball determined by a specified pseudometric structure. -/
@[expose]
def ball {X : Type u} (m : PseudoMetricSpace X) (x : X) (ε : ℝ) : Set X :=
  {y | m.toDist.dist y x < ε}

@[simp]
theorem ball_eq {X : Type u} [m : PseudoMetricSpace X] (x : X) (ε : ℝ) :
    m.ball x ε = Metric.ball x ε := rfl

end PseudoMetricSpace

/-- Lemma 20.2: For two pseudometrics `m` and `m'` on `X`, the topology induced by
`m'` is finer than that induced by `m` if and only if every positive-radius `m`-ball
contains a positive-radius `m'`-ball with the same center. -/
theorem pseudoMetricTopology_le_iff_ball_subset {X : Type u}
    (m m' : PseudoMetricSpace X) :
    m'.toUniformSpace.toTopologicalSpace ≤ m.toUniformSpace.toTopologicalSpace ↔
      ∀ x ε, 0 < ε →
        ∃ δ, 0 < δ ∧ m'.ball x δ ⊆ m.ball x ε := by
  rw [le_iff_nhds]
  exact forall_congr' fun x ↦
    (@Metric.nhds_basis_ball X m' x).le_basis_iff (@Metric.nhds_basis_ball X m x)
