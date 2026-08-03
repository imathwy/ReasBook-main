module

public import Topology_Munkres_2000.Book.Exercise_45_8.Graph
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

public section

/- Exercise 45.8 requires an authoritative correction before its clauses can be formalized:
with the stated metrics and codomain, its graph assignment is not always well-defined. In
particular, the source must assume a nonempty bounded domain and restrict to maps with bounded
range before the graph map, its image subtype, and its inverse can be defined. -/

/-- Exercise 45.8: The continuous constant-zero map on `ℝ` has an unbounded graph, so the
graph assignment in the printed exercise does not always take values in nonempty closed bounded
subsets. -/
theorem continuousMapGraph_not_always_bounded :
    ¬ Bornology.IsBounded (Function.graph (ContinuousMap.const ℝ (0 : ℝ))) := by
  intro hgraph
  -- Boundedness of the graph would force its entire real domain to be bounded.
  have huniv : Bornology.IsBounded (Set.univ : Set ℝ) :=
    (Function.graph_isBounded_iff _).mp hgraph |>.1
  -- Two sufficiently separated real points contradict any proposed metric bound.
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp huniv
  have hdist : dist (0 : ℝ) (|C| + 1) ≤ C :=
    hC (Set.mem_univ 0) (Set.mem_univ (|C| + 1))
  have hnonpos : (0 : ℝ) - (|C| + 1) ≤ 0 := by
    linarith [abs_nonneg C]
  rw [Real.dist_eq, abs_of_nonpos hnonpos] at hdist
  linarith [le_abs_self C]
