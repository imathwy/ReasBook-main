module

public import Topology_Munkres_2000.Book.Notation_43_3.CauchySequences
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

public section

universe u

open scoped Topology

namespace CauchySequences

variable {X : Type u} [PseudoMetricSpace X]

/-- Two Cauchy sequences are equivalent when their pointwise distances tend to zero. -/
def Equivalent (x y : X̃) : Prop :=
  Filter.Tendsto (fun n : ℕ ↦ dist (x.val n) (y.val n)) Filter.atTop (𝓝 0)

/-- Equivalence of Cauchy sequences. -/
scoped[CauchySequences] infix:50 " ∼ " => Equivalent

open scoped CauchySequences

/-- Equivalence is convergence of pointwise distances to zero. -/
theorem equivalent_tendsto {x y : X̃} (h : x ∼ y) :
    Filter.Tendsto (fun n : ℕ ↦ dist (x.val n) (y.val n)) Filter.atTop (𝓝 0) := h

/-- The ε–N characterization of equivalence of Cauchy sequences. -/
theorem equivalent_iff (x y : X̃) :
    x ∼ y ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (x.val n) (y.val n) < ε := by
  rw [Equivalent, Metric.tendsto_atTop]
  simp only [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg]

end CauchySequences

end
