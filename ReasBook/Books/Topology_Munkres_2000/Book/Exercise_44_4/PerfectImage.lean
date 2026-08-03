module

public import Topology_Munkres_2000.Book.Definition_26_7.PerfectMap
public import Topology_Munkres_2000.Book.Definition_44_1.PeanoSpace
public import Topology_Munkres_2000.Book.Exercise_25_6.WeaklyLocallyConnected
public import Topology_Munkres_2000.Book.Exercise_25_8
public import Topology_Munkres_2000.Book.Exercise_31_7
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Topology.UnitInterval

public section

open Set TopologicalSpace Topology

universe u

/-- Helper for Exercise 44.4: a surjective continuous map from the closed unit interval
to a Hausdorff space is a perfect map. -/
theorem isPerfectMap_unitInterval_of_surjective
    {X : Type u} [TopologicalSpace X] [T2Space X] (f : C(unitInterval, X))
    (hf : Function.Surjective f) : IsPerfectMap f := by
  -- Compactness of the interval makes every closed source set and every fiber compact.
  rw [isPerfectMap_iff]
  exact ⟨f.continuous, f.continuous.isClosedMap, hf,
    fun y ↦ (isClosed_singleton.preimage f.continuous).isCompact⟩

/-- Helper for Exercise 44.4: every locally connected space is weakly locally connected. -/
theorem LocallyConnectedSpace.weaklyLocallyConnectedSpace
    (X : Type u) [TopologicalSpace X] [LocallyConnectedSpace X] :
    WeaklyLocallyConnectedSpace X := by
  refine ⟨fun x ↦ (weaklyLocallyConnectedAt_iff x).mpr ?_⟩
  intro U hU
  obtain ⟨C, hC, hCpreconnected, hCU⟩ :=
    locallyConnectedSpace_iff_connected_subsets.mp inferInstance x U hU
  exact ⟨C, hC, ⟨⟨x, mem_of_mem_nhds hC⟩, hCpreconnected⟩, hCU⟩

namespace PeanoSpace

/-- Helper for Exercise 44.4: a Peano space witness supplies compactness without requiring
it to be installed as the ambient `PeanoSpace` instance. -/
theorem compactSpace {X : Type u} [TopologicalSpace X] (h : PeanoSpace X) :
    CompactSpace X := by
  obtain ⟨f, hf⟩ := h.exists_surjective
  exact Function.Surjective.compactSpace f.continuous hf

/-- Helper for Exercise 44.4: every Peano space is compact. -/
instance instCompactSpace (X : Type u) [TopologicalSpace X] [h : PeanoSpace X] :
    CompactSpace X := h.compactSpace

/-- Helper for Exercise 44.4: a Peano space witness supplies connectedness without requiring
it to be installed as the ambient `PeanoSpace` instance. -/
theorem connectedSpace {X : Type u} [TopologicalSpace X] (h : PeanoSpace X) :
    ConnectedSpace X := by
  obtain ⟨f, hf⟩ := h.exists_surjective
  exact hf.connectedSpace f.continuous

/-- Helper for Exercise 44.4: every Peano space is connected. -/
instance instConnectedSpace (X : Type u) [TopologicalSpace X] [h : PeanoSpace X] :
    ConnectedSpace X := h.connectedSpace

/-- Helper for Exercise 44.4: a Peano space witness supplies weak local connectedness without
requiring it to be installed as the ambient `PeanoSpace` instance. -/
theorem weaklyLocallyConnectedSpace {X : Type u} [TopologicalSpace X]
    (h : PeanoSpace X) : WeaklyLocallyConnectedSpace X := by
  obtain ⟨f, hf⟩ := h.exists_surjective
  -- The perfect interval map is quotient, so local connectedness descends to its target.
  letI : LocallyPathConnectedSpace unitInterval :=
    (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  letI : LocallyConnectedSpace X :=
    (isPerfectMap_unitInterval_of_surjective f hf).isQuotientMap.locallyConnectedSpace
  exact LocallyConnectedSpace.weaklyLocallyConnectedSpace X

/-- Helper for Exercise 44.4: every Peano space is weakly locally connected. -/
instance instWeaklyLocallyConnectedSpace
    (X : Type u) [TopologicalSpace X] [h : PeanoSpace X] : WeaklyLocallyConnectedSpace X :=
  h.weaklyLocallyConnectedSpace

/-- Helper for Exercise 44.4: a Peano space witness supplies metrizability without requiring
it to be installed as the ambient `PeanoSpace` instance. -/
theorem metrizableSpace {X : Type u} [TopologicalSpace X] (h : PeanoSpace X) :
    MetrizableSpace X := by
  obtain ⟨f, hf⟩ := h.exists_surjective
  have hperfect : IsPerfectMap f := isPerfectMap_unitInterval_of_surjective f hf
  -- Perfect images inherit the two hypotheses of Urysohn's metrization theorem.
  letI : T3Space X := hperfect.t3Space
  letI : SecondCountableTopology X := hperfect.secondCountableTopology
  infer_instance

/-- Helper for Exercise 44.4: every Peano space is metrizable. -/
instance instMetrizableSpace (X : Type u) [TopologicalSpace X] [h : PeanoSpace X] :
    MetrizableSpace X := h.metrizableSpace

end PeanoSpace
