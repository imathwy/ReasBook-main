module

public import Topology_Munkres_2000.Book.Exercise_43_6.Subspace
public import Topology_Munkres_2000.Book.Theorem_48_1

public section

universe u

/- Exercise 48.5 (1). A `Gδ` subset of a compact Hausdorff space is a Baire
space in the subspace topology. -/
#check fun {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    {Y : Set X} (hY : IsGδ Y) ↦
  (hY.baireSpace_of_t2Space_locallyCompactSpace : BaireSpace Y)

/-- Exercise 48.5 (2). A `Gδ` subset of a complete metric space is a Baire
space in the subspace topology. -/
theorem IsGδ.baireSpace_of_completeSpace {X : Type u} [MetricSpace X]
    [CompleteSpace X] {Y : Set X} (hY : IsGδ Y) : BaireSpace Y := by
  let _ := hY.isCompletelyMetrizableSpace
  infer_instance
