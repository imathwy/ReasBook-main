module

public import Topology_Munkres_2000.Book.Definition_28_1.LimitPointCompact
import Topology_Munkres_2000.Book.Example_28_1.IndiscretePair
public import Mathlib.Topology.Category.TopCat.Basic

public section

universe u

/- Theorem 28.1 (1). Compactness implies limit point compactness. -/
#check fun (X : Type u) [TopologicalSpace X] [CompactSpace X] ↦
  (inferInstance : LimitPointCompactSpace X)

/-- Theorem 28.1 (2). Limit point compactness does not imply compactness. -/
theorem existsLimitPointCompactSpaceNotCompactSpace :
    ∃ X : TopCat.{0}, LimitPointCompactSpace X ∧ ¬ CompactSpace X := by
  exact ⟨TopCat.of PNatIndiscretePair, inferInstance, not_compactSpace_iff.mpr inferInstance⟩
