module

public import Topology_Munkres_2000.Book.Theorem_20_5.WeightedMetric
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.Pi

public section

open Set

universe u

/- Exercise 45.1 (1). The countable product carries the compatible weighted
supremum metric with distance `Pi.weightedSupDist`. -/
#check Pi.weightedSupMetricSpace
#check Pi.weightedSupMetricSpace_dist
#check Pi.weightedSupMetricSpace_topology

namespace Pi

/-- Exercise 45.1 (2). A countable product of totally bounded metric spaces is
totally bounded for the weighted supremum metric `Pi.weightedSupMetricSpace`. -/
theorem totallyBounded_univ_countableProduct
    {X : ℕ → Type u} [∀ n, MetricSpace (X n)]
    (h_totallyBounded : ∀ n, TotallyBounded (univ : Set (X n))) :
    let _ : MetricSpace (∀ n, X n) := weightedSupMetricSpace
    TotallyBounded (univ : Set (∀ n, X n)) := by
  -- The statement's total-boundedness proposition uses the existing product uniformity.
  dsimp only
  -- An ultrafilter on the product is Cauchy once each coordinate projection is Cauchy.
  rw [totallyBounded_iff_ultrafilter]
  intro f hf
  rw [cauchy_pi_iff']
  intro n
  -- Coordinate total boundedness makes the projected ultrafilter Cauchy.
  rw [← Ultrafilter.coe_map]
  refine totallyBounded_iff_ultrafilter.mp (h_totallyBounded n) _ ?_
  simp

/- Exercise 45.1 (3). The compactness conclusion for a countable product is
the canonical product `CompactSpace` instance. Metrizability is needed only for
the exercise's requested proof via the weighted supremum metric. -/
#check Pi.compactSpace

end Pi

end
