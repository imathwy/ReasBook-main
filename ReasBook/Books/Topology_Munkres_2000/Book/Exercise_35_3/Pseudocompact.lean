module

public import Mathlib.Topology.MetricSpace.Bounded

public section

universe u

/-- A topological space is pseudocompact if every continuous real-valued function on it has
bounded range. -/
class PseudocompactSpace (X : Type u) [TopologicalSpace X] : Prop where
  /-- Every continuous real-valued function has bounded range. -/
  isBounded_range (f : C(X, ℝ)) : Bornology.IsBounded (Set.range f)

/-- Every compact space is pseudocompact. -/
instance CompactSpace.toPseudocompactSpace (X : Type u) [TopologicalSpace X] [CompactSpace X] :
    PseudocompactSpace X where
  isBounded_range f := (isCompact_range f.continuous).isBounded

/-- The defining characterization of a pseudocompact space. -/
theorem pseudocompactSpace_iff (X : Type u) [TopologicalSpace X] :
    PseudocompactSpace X ↔
      ∀ f : X → ℝ, Continuous f → Bornology.IsBounded (Set.range f) := by
  constructor
  · intro hpseudo f hf
    -- Bundle the function so that the defining pseudocompactness field applies.
    exact hpseudo.isBounded_range ⟨f, hf⟩
  · intro h
    constructor
    -- Forgetting the continuous-map bundle recovers the stated range.
    intro f
    exact h f f.continuous

end
