module

import Topology_Munkres_2000.Book.Exercise_43_6.Instances
public import Mathlib.Topology.Baire.CompleteMetrizable

public section

universe u

/-- A closed subspace of a completely metrizable space is a Baire space. -/
theorem IsClosed.baireSpace {X : Type u} [TopologicalSpace X]
    [TopologicalSpace.IsCompletelyMetrizableSpace X] {s : Set X} (hs : IsClosed s) :
    BaireSpace s := by
  -- Local instance justification (proof-local temporary data): the complete
  -- metrizability instance on `s` depends on the explicit hypothesis `hs`.
  let _ := hs.isCompletelyMetrizableSpace
  infer_instance

/- Example 48.3 (1): Every closed subspace of `ℝ` is a Baire space. -/
#check fun (s : Set ℝ) (hs : IsClosed s) ↦ hs.baireSpace

/- Example 48.3 (2): The subtype of irrational real numbers is a Baire space. -/
#check (inferInstance : BaireSpace {x : ℝ // Irrational x})
