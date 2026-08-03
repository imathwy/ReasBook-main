module

import Topology_Munkres_2000.Book.Corollary_27_8
public import Topology_Munkres_2000.Book.Exercise_20_4.RealSequences
import Topology_Munkres_2000.Book.Proposition_21_3.UniformConvergence
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import Mathlib.Topology.UnitInterval

public section

open Set

/-- The closed unit interval is uncountable. -/
instance unitInterval.instUncountable : Uncountable unitInterval :=
  (uncountable_iff_not_countable unitInterval).mpr
    (Cardinal.Real.Icc_not_countable zero_lt_one)

/-- Real sequence space with the uniform topology is topologically complete. -/
instance uniformRealSequencesCompletelyMetrizable :
    TopologicalSpace.IsCompletelyMetrizableSpace UniformRealSequence := by
  -- The uniformity on the uniform-function model has a countable basis.
  obtain ⟨V, hV⟩ := Filter.exists_antitone_basis (uniformity ℝ)
  letI : Filter.IsCountablyGenerated (uniformity (UniformFun ℕ ℝ)) :=
    (UniformFun.hasBasis_uniformity_of_basis ℕ ℝ hV.1).isCountablyGenerated
  -- Transfer complete metrizability across the canonical homeomorphism.
  exact (UniformMetric.functionSpaceHomeomorph ℕ).isClosedEmbedding
    |>.IsCompletelyMetrizableSpace

end
