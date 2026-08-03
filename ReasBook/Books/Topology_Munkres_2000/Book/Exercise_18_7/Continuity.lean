module

public import Topology_Munkres_2000.Book.Definition_13_3.SorgenfreyLine

public section

open scoped Topology

namespace SorgenfreyLine

/-- Helper for Exercise 18.7: the Sorgenfrey neighborhood filter transports along `toReal`
to the usual right-neighborhood filter. -/
lemma nhds_eq_comap_nhdsWithin_Ici (a : SorgenfreyLine) :
    (𝓝 a : Filter SorgenfreyLine) =
      Filter.comap toReal (𝓝[Set.Ici (toReal a)] (toReal a)) := by
  -- Both filters have the corresponding basis of half-open intervals `[a, b)`.
  apply isTopologicalBasis_lowerLimitBasis.nhds_hasBasis.ext
    ((nhdsGE_basis_Ico (toReal a)).comap toReal)
  · rintro _ ⟨⟨c, d, _, rfl⟩, hac, had⟩
    exact ⟨d, had, Set.preimage_mono (Set.Ico_subset_Ico_left hac)⟩
  · intro d had
    exact ⟨Set.Ico (toReal a) d, ⟨⟨toReal a, d, had, rfl⟩,
      Set.left_mem_Ico.2 had⟩, Set.Subset.rfl⟩

/-- A map from the Sorgenfrey line is continuous exactly when its underlying real function is
continuous from the right at every point. -/
theorem continuous_comp_toReal_iff {Y : Type*} [TopologicalSpace Y] (f : ℝ → Y) :
    Continuous (f ∘ toReal) ↔ ∀ a : ℝ, ContinuousWithinAt f (Set.Ici a) a := by
  rw [continuous_iff_continuousAt]
  constructor
  · intro h a
    have h_at := h (toReal.symm a)
    rw [ContinuousAt, nhds_eq_comap_nhdsWithin_Ici] at h_at
    have h_range : Set.range toReal ∈ 𝓝[Set.Ici a] a := by
      simpa only [toReal.surjective.range_eq] using Filter.univ_mem
    exact (Filter.tendsto_comap'_iff h_range).1 (by simpa using h_at)
  · intro h a
    rw [ContinuousAt, nhds_eq_comap_nhdsWithin_Ici]
    have h_range : Set.range toReal ∈ 𝓝[Set.Ici (toReal a)] (toReal a) := by
      simpa only [toReal.surjective.range_eq] using Filter.univ_mem
    have h_right := h (toReal a)
    rw [ContinuousWithinAt] at h_right
    exact (Filter.tendsto_comap'_iff h_range).2 (by simpa using h_right)

end SorgenfreyLine
