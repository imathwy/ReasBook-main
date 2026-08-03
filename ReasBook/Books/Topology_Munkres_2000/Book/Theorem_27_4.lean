module

public import Mathlib.Topology.Order.Compact

public section

universe u v

open Set

/-- Theorem 27.4 (Extreme value theorem). A continuous map from a nonempty compact
space into a linearly ordered space with its order topology attains a global minimum
and a global maximum. -/
theorem extremeValueTheorem {X : Type u} {Y : Type v} [TopologicalSpace X]
    [CompactSpace X] [Nonempty X] [LinearOrder Y] [TopologicalSpace Y] [OrderTopology Y]
    (f : X → Y) (hf : Continuous f) :
    ∃ c d : X, ∀ x : X, f c ≤ f x ∧ f x ≤ f d := by
  obtain ⟨c, -, hc⟩ := isCompact_univ.exists_isMinOn univ_nonempty hf.continuousOn
  obtain ⟨d, -, hd⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hf.continuousOn
  exact ⟨c, d, fun x ↦ ⟨hc (mem_univ x), hd (mem_univ x)⟩⟩

end
