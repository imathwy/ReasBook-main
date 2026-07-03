import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Maps.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Topology

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/-- Definition 4.24-extra-2: A topological immersion is a continuous map such that every point of
the source has a neighborhood on which the restricted map is a topological embedding. The
continuity clause is redundant, since it is forced by the local embedding condition. -/
@[mk_iff]
structure IsTopologicalImmersion (f : X → Y) : Prop where
  /-- Every point admits a neighborhood on which the map is a topological embedding. -/
  local_embedding (x : X) : ∃ s : Set X, s ∈ 𝓝 x ∧ IsEmbedding (s.restrict f)

namespace IsTopologicalImmersion

/-- A topological immersion is continuous. -/
theorem continuous (hf : IsTopologicalImmersion f) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨s, hs, hs_emb⟩ := hf.local_embedding x
  have hcontOn : ContinuousOn f s := by
    rw [continuousOn_iff_continuous_restrict]
    simpa using hs_emb.continuous
  exact hcontOn.continuousAt hs

/-- A topological immersion is continuous. -/
instance (hf : IsTopologicalImmersion f) : Continuous f := hf.continuous

end IsTopologicalImmersion

namespace IsEmbedding

/-- Any topological embedding is, in particular, a topological immersion. -/
-- Proof sketch: For each point, take the neighborhood `univ`; the restriction of the map to `univ`
-- is canonically the original embedding.
theorem isTopologicalImmersion (hf : IsEmbedding f) : IsTopologicalImmersion f := by
  refine ⟨fun _ ↦ ?_⟩
  refine ⟨Set.univ, Filter.univ_mem, ?_⟩
  simpa [Set.restrict_eq] using hf.comp IsEmbedding.subtypeVal

end IsEmbedding

end Topology
