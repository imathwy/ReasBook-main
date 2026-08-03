module

public import Mathlib.Topology.CompactOpen

public section

universe u v w

/-- Exercise 46.7: If `Y` is locally compact Hausdorff, composition
`C(X, Y) × C(Y, Z) → C(X, Z)` is continuous for the compact-open topologies.

Mathlib's `ContinuousMap.continuous_comp'` gives the slightly sharper result without the
Hausdorff assumption. -/
theorem continuous_compactOpen_comp {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [LocallyCompactSpace Y] [T2Space Y] :
    Continuous (fun p : C(X, Y) × C(Y, Z) ↦ p.2.comp p.1) :=
  ContinuousMap.continuous_comp'
