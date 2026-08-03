module

public import Topology_Munkres_2000.Book.Exercise_45_7.HausdorffMetric

public section

open Set

universe u

/-- Exercise 45.7 check-only aggregate: the Hausdorff distance gives a metric on nonempty
closed bounded subsets and preserves completeness, total boundedness, and compactness. -/
theorem «Exercise 45.7 check-only aggregate» :
    (∀ (X : Type u) [MetricSpace X],
      Nonempty (MetricSpace (TopologicalSpace.NonemptyClosedBounded X)) ∧
        ∀ A B : TopologicalSpace.NonemptyClosedBounded X,
          dist A B =
            sInf {ε : ℝ |
              (A : Set X) ⊆ Metric.thickening ε (B : Set X) ∧
                (B : Set X) ⊆ Metric.thickening ε (A : Set X)}) ∧
    (∀ (X : Type u) [MetricSpace X] [CompleteSpace X],
      Nonempty (CompleteSpace (TopologicalSpace.NonemptyClosedBounded X))) ∧
    (∀ (X : Type u) [MetricSpace X],
      TotallyBounded (Set.univ : Set X) →
        TotallyBounded
          (Set.univ : Set (TopologicalSpace.NonemptyClosedBounded X))) ∧
    ∀ (X : Type u) [MetricSpace X] [CompactSpace X],
      Nonempty (CompactSpace (TopologicalSpace.NonemptyClosedBounded X)) := by
  -- Package the established Hausdorff metric and its distance characterization.
  constructor
  · intro X _
    constructor
    · exact ⟨inferInstance⟩
    · exact Metric.NonemptyClosedBounded.dist_eq_sInf
  constructor
  · intro X _ _
    exact ⟨inferInstance⟩
  constructor
  · intro X _ hX
    exact TopologicalSpace.NonemptyClosedBounded.totallyBounded_univ hX
  · intro X _ _
    exact ⟨inferInstance⟩

/- Exercise 45.7. The Hausdorff hyperspace consists of the nonempty closed bounded
subsets of a metric space. -/
#check TopologicalSpace.NonemptyClosedBounded

/- Exercise 45.7 (a). The Hausdorff distance is the infimum of radii of mutual metric
neighborhoods. -/
#check Metric.NonemptyClosedBounded.dist_eq_sInf

/- Exercise 45.7 (a). The Hausdorff distance defines a metric on the hyperspace. -/
#check TopologicalSpace.NonemptyClosedBounded.instMetricSpace

/- Exercise 45.7 (b). Completeness of the ambient metric space passes to the Hausdorff
hyperspace of nonempty closed bounded subsets. -/
#check TopologicalSpace.NonemptyClosedBounded.instCompleteSpace

/- Exercise 45.7 (c). Total boundedness of the ambient metric space passes to the
Hausdorff hyperspace of nonempty closed bounded subsets. -/
#check TopologicalSpace.NonemptyClosedBounded.totallyBounded_univ

/- Exercise 45.7 (d). Compactness of the ambient metric space passes to the Hausdorff
hyperspace of nonempty closed bounded subsets. -/
#check TopologicalSpace.NonemptyClosedBounded.instCompactSpace
