module

public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Baire.LocallyCompactRegular

public section

universe u

/- Theorem 48.1 (1): A compact Hausdorff space is a Baire space. -/
#check fun (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] ↦
  (BaireSpace.of_t2Space_locallyCompactSpace : BaireSpace X)

/- Theorem 48.1 (2): A complete metric space is a Baire space. -/
#check fun (X : Type u) [MetricSpace X] [CompleteSpace X] ↦
  (BaireSpace.of_completelyPseudoMetrizable : BaireSpace X)
