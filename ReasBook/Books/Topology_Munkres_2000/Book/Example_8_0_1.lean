module

import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.LocallyCompactRegular

universe u

/- Example 8.0.1 (1): A compact Hausdorff space is a Baire space. -/
#check fun (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] ↦
  (BaireSpace.of_t2Space_locallyCompactSpace : BaireSpace X)

/- Example 8.0.1 (2): A locally compact Hausdorff space is a Baire space. -/
#check fun (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] ↦
  (BaireSpace.of_t2Space_locallyCompactSpace : BaireSpace X)

/- Example 8.0.1 (3): A metrizable space whose topology is induced by a complete
metric is a Baire space. -/
#check fun (X : Type u) [TopologicalSpace X]
    [TopologicalSpace.IsCompletelyMetrizableSpace X] ↦
  (BaireSpace.of_completelyPseudoMetrizable : BaireSpace X)
