module

import Mathlib.Topology.Baire.CompleteMetrizable

universe u

/- Remark 8.0.1 (1): A metrizable space `X` is topologically complete when its
topology is induced by a metric with respect to which `X` is complete. -/
#check TopologicalSpace.IsCompletelyMetrizableSpace

/- Remark 8.0.1 (2): A topologically complete metrizable space `X` is a Baire
space. -/
#check fun (X : Type u) [TopologicalSpace X]
    [TopologicalSpace.IsCompletelyMetrizableSpace X] ↦
  (BaireSpace.of_completelyPseudoMetrizable : BaireSpace X)
