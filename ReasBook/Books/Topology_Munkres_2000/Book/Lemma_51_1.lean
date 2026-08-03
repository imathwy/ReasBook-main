module

import Mathlib.Topology.Homotopy.Path

/- Lemma 51.1 (1): Homotopy of continuous maps is an equivalence relation. -/
#check ContinuousMap.Homotopic.equivalence

/- Lemma 51.1 (2): Path homotopy between paths with fixed endpoints is an equivalence relation. -/
#check Path.Homotopic.equivalence
