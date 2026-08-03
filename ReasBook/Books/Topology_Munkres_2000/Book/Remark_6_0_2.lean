module

import Topology_Munkres_2000.Book.Exercise_4_99_2
public import Mathlib.Topology.GDelta.MetrizableSpace

public section

universe u

/- Remark 6.0.2 (1): Regularity is necessary for metrizability; the search
described in the remark is therefore for a weaker replacement of the countable
basis condition, not of regularity. -/
#check fun (X : Type u) [TopologicalSpace X]
    [TopologicalSpace.MetrizableSpace X] ↦
  (inferInstance : T3Space X)

/-- Remark 6.0.2 (2): A countable basis is not necessary for metrizability,
which motivates seeking a weaker condition that is still sufficient for
metrizability and is satisfied by every metrizable space. -/
theorem not_every_metrizableSpace_secondCountable :
    ¬ ∀ (X : Type u) [TopologicalSpace X]
      [TopologicalSpace.MetrizableSpace X], SecondCountableTopology X := by
  intro h
  exact not_every_metricSpace_secondCountable fun X ↦ h X
