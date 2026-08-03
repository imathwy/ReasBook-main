module

public import Topology_Munkres_2000.Book.Exercise_29_1

public section

open Set
open scoped Topology

universe u v

/-- Exercise 29.3 (1): The identity from discrete `ℚ` to usual `ℚ` is a continuous
map from a weakly locally compact space whose range is not weakly locally compact. -/
theorem continuousImage_not_weaklyLocallyCompact :
    WeaklyLocallyCompactSpace (WithDiscreteTopology ℚ) ∧
      Continuous (fun x : WithDiscreteTopology ℚ ↦ x.ofTopology) ∧
        ¬ WeaklyLocallyCompactSpace
          (range fun x : WithDiscreteTopology ℚ ↦ x.ofTopology) := by
  let f : WithDiscreteTopology ℚ → ℚ := fun x ↦ x.ofTopology
  have hf_surjective : Function.Surjective f := fun x ↦
    ⟨WithTopology.toTopology ⊥ x, rfl⟩
  have hf_range : range f = univ := range_eq_univ.mpr hf_surjective
  refine ⟨⟨fun x ↦ ⟨{x}, isCompact_singleton,
    discreteTopology_iff_singleton_mem_nhds.mp inferInstance x⟩⟩,
    continuous_of_discreteTopology, ?_⟩
  intro h_range
  have hf_open_range : IsOpen (range f) := hf_range ▸ isOpen_univ
  have hq : IsOpenQuotientMap (Subtype.val : range f → ℚ) :=
    ⟨fun x ↦ ⟨⟨x, hf_range.symm ▸ mem_univ x⟩, rfl⟩, continuous_subtype_val,
      hf_open_range.isOpenMap_subtype_val⟩
  apply Rat.notWeaklyLocallyCompact
  refine ⟨hq.surjective.forall.2 fun x ↦ ?_⟩
  rcases h_range.exists_compact_mem_nhds x with ⟨K, hK_compact, hK_mem⟩
  exact ⟨Subtype.val '' K, hK_compact.image hq.continuous,
    hq.isOpenMap.image_mem_nhds hK_mem⟩

/-- Exercise 29.3 (2): The range of a continuous open map from a locally compact
space is locally compact with its subspace topology, in the compact-neighborhood sense. -/
theorem weaklyLocallyCompact_range_of_continuous_isOpenMap
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [WeaklyLocallyCompactSpace X] {f : X → Y} (hf : Continuous f) (hf_open : IsOpenMap f) :
    WeaklyLocallyCompactSpace (range f) := by
  have hf_range : IsOpenQuotientMap (rangeFactorization f) :=
    ⟨rangeFactorization_surjective, hf.rangeFactorization,
      hf_open.subtype_mk fun x ↦ mem_range_self x⟩
  exact hf_range.weaklyLocallyCompactSpace
