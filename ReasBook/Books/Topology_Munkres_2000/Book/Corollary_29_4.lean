module

import Topology_Munkres_2000.Book.Corollary_29_3
public import Topology_Munkres_2000.Book.Theorem_29_1

public section

universe u

/-- Corollary 29.4. A space is homeomorphic to an open subspace of a compact Hausdorff space if
and only if it is weakly locally compact and Hausdorff. -/
theorem exists_isOpenEmbedding_compHaus_iff {X : Type u} [TopologicalSpace X] :
    (∃ (Y : CompHaus.{u}) (f : X → Y), Topology.IsOpenEmbedding f) ↔
      (WeaklyLocallyCompactSpace X ∧ T2Space X) := by
  constructor
  · rintro ⟨Y, f, hf⟩
    -- Pull local compactness and Hausdorffness back along the open embedding.
    letI : LocallyCompactSpace X := hf.locallyCompactSpace
    exact ⟨inferInstance, hf.isEmbedding.t2Space⟩
  · intro hX
    -- The one-point compactification realizes `X` as a singleton complement.
    rcases OnePoint.existsCompactification_iff.mp hX with ⟨Y, f, y, hf, hRange⟩
    have hOpenRange : IsOpen (Set.range f) := by
      rw [hRange]
      exact isOpen_compl_singleton
    -- Bundle the embedding with the openness of its range.
    have hOpenEmbedding : Topology.IsOpenEmbedding f := ⟨hf, hOpenRange⟩
    exact ⟨Y, f, hOpenEmbedding⟩

end
