module

public import Mathlib.Topology.Metrizable.Basic

public section

universe u

open scoped Topology

/-- A topological space is locally metrizable if every point has a metrizable neighborhood. -/
class LocallyMetrizableSpace (X : Type u) [TopologicalSpace X] : Prop where
  /-- Every point belongs to a neighborhood that is metrizable in its subspace topology. -/
  exists_metrizable_nhds (x : X) :
    ∃ s : Set X, s ∈ 𝓝 x ∧ TopologicalSpace.MetrizableSpace s

/-- The defining characterization of a locally metrizable space. -/
theorem locallyMetrizableSpace_iff (X : Type u) [TopologicalSpace X] :
    LocallyMetrizableSpace X ↔
      ∀ x, ∃ s : Set X, s ∈ 𝓝 x ∧ TopologicalSpace.MetrizableSpace s := by
  -- Unpack or build the class using its sole defining field.
  constructor
  · intro h
    exact h.exists_metrizable_nhds
  · intro h
    exact ⟨h⟩

/-- Every metrizable topological space is locally metrizable. -/
instance TopologicalSpace.MetrizableSpace.toLocallyMetrizableSpace
    (X : Type u) [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] :
    LocallyMetrizableSpace X := by
  -- The whole space is a metrizable neighborhood of each point.
  constructor
  intro x
  refine ⟨Set.univ, Filter.univ_mem, ?_⟩
  infer_instance
