module

public import Mathlib.Data.Rel
public import Mathlib.Topology.Maps.Proper.Basic

public section

universe u v

/-- Exercise 26.8: A map into a compact Hausdorff space is continuous exactly when
its graph is closed in the product. -/
theorem continuous_iff_isClosed_graph {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] (f : X → Y) :
    Continuous f ↔ IsClosed (Function.graph f) := by
  constructor
  · intro hf
    -- The graph is the equalizer of the two coordinate maps.
    simpa only [Function.graph, Function.comp_apply] using
      isClosed_eq (hf.comp continuous_fst) continuous_snd
  · intro hf
    -- By the closed-set criterion, project closed graph slices onto `X`.
    rw [continuous_iff_isClosed]
    intro s hs
    have hSlice : IsClosed (Function.graph f ∩ (Set.univ ×ˢ s)) :=
      hf.inter (isClosed_univ.prod hs)
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
        refine ⟨(x, f x), ?_, rfl⟩
        constructor
        · exact rfl
        · exact ⟨Set.mem_univ x, hx⟩
    rw [← hProjection]
    exact isClosedMap_fst_of_compactSpace _ hSlice
