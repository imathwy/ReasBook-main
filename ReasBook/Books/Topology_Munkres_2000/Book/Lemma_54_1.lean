module

public import Mathlib.Topology.Homotopy.Lifting

public section

/- Lemma 54.1: A path through a covering map has a canonical lift once its
initial value is prescribed. -/
#check IsCoveringMap.liftPath

/- The canonical path lift projects to the original path. -/
#check IsCoveringMap.liftPath_lifts

/- The canonical path lift has the prescribed initial value. -/
#check IsCoveringMap.liftPath_zero

/- A path with the prescribed projection and initial value is the canonical lift. -/
#check IsCoveringMap.eq_liftPath_iff'
