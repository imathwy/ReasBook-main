module

public import Topology_Munkres_2000.Book.Exercise_36_1.Separation
public import Topology_Munkres_2000.Book.Exercise_36_1.Metrizable
public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

universe u

/-- Exercise 36.1: Every Hausdorff second-countable Euclidean-charted space is regular
and metrizable. The Hausdorff hypothesis is used to obtain regularity. -/
theorem manifold_regular_and_metrizable (m : ℕ) {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) X] [T2Space X]
    [SecondCountableTopology X] :
    T3Space X ∧ TopologicalSpace.MetrizableSpace X := by
  -- Hausdorffness combines with local Euclidean compactness to give regularity;
  -- second countability then supplies the metrization theorem.
  exact ⟨ChartedSpace.t3Space (EuclideanSpace ℝ (Fin m)),
    ChartedSpace.metrizableSpace (EuclideanSpace ℝ (Fin m))⟩
