module

public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Metrizable.Basic
import Topology_Munkres_2000.Book.Lemma_39_2
import Topology_Munkres_2000.Book.Lemma_41_3

public section

universe u

namespace TopologicalSpace

/-- Theorem 41.4. Every metrizable topological space is paracompact. -/
instance MetrizableSpace.paracompactSpace
    {X : Type u} [TopologicalSpace X] [MetrizableSpace X] : ParacompactSpace X := by
  -- Lemma 39.2 supplies the countably locally finite open refinement condition.
  have h_countablyLocallyFinite :
      ∀ 𝒦 : Set (Set X),
        (∀ U ∈ 𝒦, IsOpen U) → ⋃₀ 𝒦 = Set.univ →
          ∃ ℰ : Set (Set X),
            IsOpenRefinement ℰ 𝒦 ∧ ⋃₀ ℰ = Set.univ ∧ ℰ.CountablyLocallyFinite := by
    intro 𝒦 h_open h_cover
    exact MetrizableSpace.exists_countablyLocallyFinite_openRefinement 𝒦 h_open h_cover
  -- Lemma 41.3 converts that refinement condition into paracompactness.
  exact ((_root_.openCoverRefinement_tfae X).out 0 3).mp h_countablyLocallyFinite

end TopologicalSpace

/- Theorem 41.4. Every metrizable space is paracompact. -/
#check TopologicalSpace.MetrizableSpace.paracompactSpace
