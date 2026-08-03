module

public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Analysis.Real.Cardinality

public section

/-- The real-indexed product of closed unit intervals. -/
abbrev RealIndexedUnitCube := ℝ → Set.Icc (0 : ℝ) 1

#synth T2Space RealIndexedUnitCube
#synth LocallyCompactSpace RealIndexedUnitCube
#synth ParacompactSpace RealIndexedUnitCube

namespace RealIndexedUnitCube

/-- The real-indexed unit cube is connected. -/
instance connectedSpace : ConnectedSpace RealIndexedUnitCube := by
  -- Each factor is connected, so the product inherits connectedness.
  letI : ConnectedSpace (Set.Icc (0 : ℝ) 1) :=
    Subtype.connectedSpace (isConnected_Icc (by norm_num))
  infer_instance

/-- Helper for Exercise 41.10: the point supported at one real coordinate with value one. -/
noncomputable def coordinateSpike (i : ℝ) : RealIndexedUnitCube :=
  Function.update 0 i 1

/-- Helper for Exercise 41.10: evaluation of a coordinate spike. -/
lemma coordinateSpike_apply (i j : ℝ) :
    coordinateSpike i j = if j = i then 1 else 0 := by
  -- Unfold the update once to expose its two coordinate cases.
  rw [coordinateSpike, Function.update_apply]
  simp only [Pi.zero_apply]

/-- Helper for Exercise 41.10: distinct coordinates determine distinct spikes. -/
lemma coordinateSpike_injective : Function.Injective coordinateSpike := by
  -- Evaluate an alleged equality at the first coordinate.
  intro i j hij
  by_contra hne
  have heval := congrFun hij i
  have heval' : (1 : Set.Icc (0 : ℝ) 1) = 0 := by
    rw [coordinateSpike_apply, coordinateSpike_apply] at heval
    rw [if_pos rfl, if_neg hne] at heval
    exact heval
  have hval := congrArg Subtype.val heval'
  norm_num at hval

/-- Helper for Exercise 41.10: the coordinate spikes form a discrete subspace. -/
lemma coordinateSpikeRange_discreteTopology :
    DiscreteTopology (Set.range coordinateSpike) := by
  -- The coordinate condition `1 / 2 < f i` isolates the spike at `i`.
  rw [discreteTopology_subtype_iff']
  intro y hy
  obtain ⟨i, rfl⟩ := hy
  refine ⟨{f | (1 / 2 : ℝ) < f i}, ?_, ?_⟩
  · exact isOpen_lt continuous_const (continuous_subtype_val.comp (continuous_apply i))
  · ext f
    constructor
    · intro hf
      rcases hf.2 with ⟨j, rfl⟩
      have hij : i = j := by
        by_contra hne
        have hzero : ((coordinateSpike j i : Set.Icc (0 : ℝ) 1) : ℝ) = 0 := by
          simp [coordinateSpike_apply, hne]
        have hlt : (1 / 2 : ℝ) < coordinateSpike j i := hf.1
        rw [hzero] at hlt
        norm_num at hlt
      subst j
      exact Set.mem_singleton _
    · intro hf
      have hfi : f = coordinateSpike i := Set.mem_singleton_iff.mp hf
      subst f
      constructor
      · simp [coordinateSpike_apply]
        norm_num
      · exact ⟨i, rfl⟩

/-- Helper for Exercise 41.10: the real-indexed unit cube is not second countable. -/
lemma not_secondCountableTopology : ¬ SecondCountableTopology RealIndexedUnitCube := by
  -- Second countability would make the discrete spike range countable.
  intro hsecond
  letI : SecondCountableTopology RealIndexedUnitCube := hsecond
  letI : DiscreteTopology (Set.range coordinateSpike) :=
    coordinateSpikeRange_discreteTopology
  letI : Countable (Set.range coordinateSpike) :=
    TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  let spikeToRange : ℝ → Set.range coordinateSpike :=
    fun i ↦ ⟨coordinateSpike i, ⟨i, rfl⟩⟩
  have hinjective : Function.Injective spikeToRange := by
    intro i j hij
    exact coordinateSpike_injective (congrArg Subtype.val hij)
  have hreal : Countable ℝ := hinjective.countable
  exact Cardinal.not_countable_real Set.countable_univ

/-- Exercise 41.10. The printed theorem is false: the Hausdorff, locally compact,
paracompact space `RealIndexedUnitCube` is connected, but its connected component is
not second countable. -/
theorem not_secondCountableTopology_connectedComponent (x : RealIndexedUnitCube) :
    ¬ SecondCountableTopology (connectedComponent x) := by
  -- Connectedness identifies the component with the whole cube; transport the topology.
  intro hsecond
  letI : SecondCountableTopology (connectedComponent x) := hsecond
  let componentHomeomorph : connectedComponent x ≃ₜ RealIndexedUnitCube :=
    (Homeomorph.setCongr (PreconnectedSpace.connectedComponent_eq_univ x)).trans
      (Homeomorph.Set.univ RealIndexedUnitCube)
  letI : SecondCountableTopology RealIndexedUnitCube :=
    componentHomeomorph.symm.isEmbedding.secondCountableTopology
  exact not_secondCountableTopology inferInstance

end RealIndexedUnitCube
