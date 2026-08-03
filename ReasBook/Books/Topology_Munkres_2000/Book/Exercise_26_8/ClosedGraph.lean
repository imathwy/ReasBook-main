module

public import Mathlib.Data.Rel
public import Mathlib.Topology.Maps.Proper.Basic

public section

universe u v

namespace Continuous

/-- A continuous map into a Hausdorff space has a closed graph. -/
theorem isClosed_graph {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] {f : X → Y} (hf : Continuous f) :
    IsClosed (Function.graph f) := by
  -- Express the graph as the equalizer of the two coordinate maps.
  simpa only [Function.graph, Function.comp_apply] using
    isClosed_eq (hf.comp continuous_fst) continuous_snd

end Continuous

/-- A map into a compact Hausdorff space is continuous if its graph is closed. -/
theorem continuous_of_isClosed_graph {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] {f : X → Y}
    (hf : IsClosed (Function.graph f)) : Continuous f := by
  -- It suffices to show that the preimage of every closed set is closed.
  rw [continuous_iff_isClosed]
  intro s hs
  -- Intersect the graph with the closed product slice `X × s`.
  have hSlice : IsClosed (Function.graph f ∩ (Set.univ ×ˢ s)) :=
    hf.inter (isClosed_univ.prod hs)
  -- The first projection of the graph slice is exactly the desired preimage.
  have hProjection :
      Prod.fst '' (Function.graph f ∩ (Set.univ ×ˢ s)) = f ⁻¹' s := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      rcases hp with ⟨hpGraph, hpProduct⟩
      rcases hpProduct with ⟨-, hpSecond⟩
      have hValue : f p.1 = p.2 := Function.mem_graph.mp hpGraph
      rw [Set.mem_preimage, hValue]
      exact hpSecond
    · intro hx
      use (x, f x)
      constructor
      · constructor
        · exact rfl
        · constructor
          · exact Set.mem_univ x
          · exact hx
      · exact rfl
  -- Compactness of `Y` makes the projection closed; transport along the set identity.
  rw [← hProjection]
  exact isClosedMap_fst_of_compactSpace _ hSlice

/-- A map into a compact Hausdorff space is continuous exactly when its graph is closed. -/
theorem continuous_iff_isClosed_graph {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] (f : X → Y) :
    Continuous f ↔ IsClosed (Function.graph f) := by
  -- Assemble the equalizer and closed-projection implications.
  constructor
  · exact Continuous.isClosed_graph
  · exact continuous_of_isClosed_graph
