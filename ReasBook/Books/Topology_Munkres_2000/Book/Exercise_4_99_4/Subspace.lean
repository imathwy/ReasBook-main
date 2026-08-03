module

public import Topology_Munkres_2000.Book.Definition_28_1.LimitPointCompact
public import Topology_Munkres_2000.Book.Exercise_4_99_2.LocallyMetrizable

public section

universe u

/-- A closed subspace of a limit point compact space is limit point compact. -/
theorem IsClosed.limitPointCompactSpace {X : Type u} [TopologicalSpace X]
    [LimitPointCompactSpace X] {s : Set X} (hs : IsClosed s) :
    LimitPointCompactSpace s := by
  refine ⟨fun t ht ↦ ?_⟩
  have htImage : (Subtype.val '' t : Set X).Infinite :=
    ht.image Subtype.val_injective.injOn
  obtain ⟨x, hx⟩ := LimitPointCompactSpace.exists_accPt (Subtype.val '' t) htImage
  have hxMem : x ∈ s := by
    apply isClosed_iff_accPt.mp hs x
    exact hx.mono (Filter.principal_mono.mpr (Set.image_subset_iff.mpr fun y _ ↦ y.property))
  refine ⟨⟨x, hxMem⟩, accPt_iff_nhds.mpr ?_⟩
  intro v hv
  obtain ⟨w, hw, hwv⟩ := (mem_nhds_subtype s ⟨x, hxMem⟩ v).mp hv
  obtain ⟨y, hy, hyx⟩ := accPt_iff_nhds.mp hx w hw
  obtain ⟨z, hzt, rfl⟩ := hy.2
  refine ⟨z, ⟨hwv hy.1, hzt⟩, ?_⟩
  intro hzx
  exact hyx (congrArg Subtype.val hzx)

/-- Every subspace of a locally metrizable space is locally metrizable. -/
instance Subtype.locallyMetrizableSpace {X : Type u} [TopologicalSpace X]
    [LocallyMetrizableSpace X] (s : Set X) : LocallyMetrizableSpace s := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨t, ht, htMetrizable⟩ := LocallyMetrizableSpace.exists_metrizable_nhds (x : X)
  let f : {y : s | (y : X) ∈ t} → t := fun y ↦ ⟨y, y.property⟩
  have hf : Topology.IsEmbedding f := by
    apply (Topology.IsEmbedding.of_comp_iff
      (Topology.IsEmbedding.subtypeVal :
        Topology.IsEmbedding (Subtype.val : t → X))).mp
    convert Topology.IsEmbedding.subtypeVal.comp
      (Topology.IsEmbedding.subtypeVal :
        Topology.IsEmbedding (Subtype.val : {y : s | (y : X) ∈ t} → s)) using 1
    funext y
    rfl
  refine ⟨Subtype.val ⁻¹' t, continuous_subtype_val.continuousAt ht, ?_⟩
  exact hf.metrizableSpace
