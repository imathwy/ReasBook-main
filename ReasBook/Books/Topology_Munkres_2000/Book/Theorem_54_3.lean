module

import Mathlib.Topology.Homotopy.Lifting

public section

/- Theorem 54.3. For a covering map, canonical lifts beginning at the same point of paths
that are homotopic relative to `{0, 1}` end at the same point and are themselves homotopic
relative to `{0, 1}`. -/
#check IsCoveringMap.homotopicRel_liftPath
#check IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel
