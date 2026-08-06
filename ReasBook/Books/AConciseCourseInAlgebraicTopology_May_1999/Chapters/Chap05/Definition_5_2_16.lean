module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.CompactOpen

public section

universe u v

open Set

/-- Definition 5.2.16: the compact-open topology on `C(X, Y)` has a topological basis consisting
of finite intersections of sets `{f | MapsTo f K U}`, where `K` is compact in `X` and `U`
is open in `Y`. -/
theorem continuousMap_compactOpen_isTopologicalBasis
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] :
    TopologicalSpace.IsTopologicalBasis
      ((fun 𝒮 : Set (Set C(X, Y)) ↦ ⋂₀ 𝒮) ''
        {𝒮 : Set (Set C(X, Y)) |
          𝒮.Finite ∧
            𝒮 ⊆ image2
              (fun K U : Set _ ↦ {f : C(X, Y) | MapsTo f K U})
              {K : Set X | IsCompact K}
              {U : Set Y | IsOpen U}}) := by
  simpa [ContinuousMap.compactOpen_eq] using
    TopologicalSpace.isTopologicalBasis_of_subbasis ContinuousMap.compactOpen_eq
