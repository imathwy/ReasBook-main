module

import Mathlib.Topology.Baire.LocallyCompactRegular

universe u

/- Exercise 48.3. Every locally compact Hausdorff space is a Baire space. -/
#check fun (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] ↦
  (BaireSpace.of_t2Space_locallyCompactSpace : BaireSpace X)
