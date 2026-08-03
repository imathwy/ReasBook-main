module

public import Mathlib.Topology.Compactness.CountablyCompact

public section

universe u

/-- Definition 28.1. A topological space `X` is limit point compact if every infinite
subset `s : Set X` has some `x : X` with `AccPt x (Filter.principal s)`. -/
class LimitPointCompactSpace (X : Type u) [TopologicalSpace X] : Prop where
  /-- Every infinite subset has an accumulation point. -/
  exists_accPt (s : Set X) (hs : s.Infinite) : ∃ x, AccPt x (Filter.principal s)
