module

public import Topology_Munkres_2000.Book.Exercise_43_8.UniformTopology
public import Mathlib.Topology.Baire.CompleteMetrizable

public section

open UniformConvergence

universe u v

namespace UniformTopologyContinuousMap

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [UniformSpace Y]

/-- Helper for Corollary 8.0.1: the canonical inclusion of uniformly topologized
continuous maps into all uniform functions is a uniform embedding. -/
theorem isUniformEmbedding_toUniformFun :
    IsUniformEmbedding (toUniformFun : UniformTopologyContinuousMap X Y → UniformFun X Y) := by
  -- The uniformity is defined by this comap, so only injectivity remains.
  apply isUniformEmbedding_comap
  intro f g h
  have h' : UniformFun.ofFun (equivContinuousMap f) =
      UniformFun.ofFun (equivContinuousMap g) := by
    rw [← toUniformFun_eq f, ← toUniformFun_eq g]
    exact h
  apply equivContinuousMap.injective
  ext x
  exact congrFun (UniformFun.ofFun.injective h') x

/-- Helper for Corollary 8.0.1: the range of the canonical inclusion consists exactly
of the continuous uniform functions. -/
theorem range_toUniformFun :
    Set.range (toUniformFun : UniformTopologyContinuousMap X Y → UniformFun X Y) =
      {f | Continuous (UniformFun.toFun f)} := by
  -- Identify membership in the range with continuity of the underlying function.
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    rw [toUniformFun_eq]
    simpa only [Set.mem_setOf_eq, UniformFun.toFun_ofFun] using
      (equivContinuousMap g).continuous
  · intro hf
    let g : C(X, Y) := ⟨UniformFun.toFun f, hf⟩
    refine ⟨equivContinuousMap.symm g, ?_⟩
    rw [toUniformFun_eq, Equiv.apply_symm_apply]
    exact UniformFun.ofFun_toFun f

/-- If the codomain is complete, continuous maps into it are complete in the uniform topology. -/
instance instCompleteSpace [CompleteSpace Y] :
    CompleteSpace (UniformTopologyContinuousMap X Y) := by
  -- Transfer completeness to the closed range of the canonical inclusion.
  rw [completeSpace_iff_isComplete_range isUniformEmbedding_toUniformFun.isUniformInducing,
    range_toUniformFun]
  exact (UniformFun.isClosed_setOf_continuous X).isComplete

end UniformTopologyContinuousMap

namespace UniformTopologyContinuousMap

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [PseudoMetricSpace Y]

/-- Helper for Corollary 8.0.1: a pseudometric codomain makes the uniformity on
uniformly topologized continuous maps countably generated. -/
instance instIsCountablyGeneratedUniformity :
    Filter.IsCountablyGenerated (uniformity (UniformTopologyContinuousMap X Y)) := by
  -- First transport a countable basis from the codomain to all uniform functions.
  obtain ⟨V, hV⟩ := Filter.exists_antitone_basis (uniformity Y)
  letI : Filter.IsCountablyGenerated (uniformity (UniformFun X Y)) :=
    (UniformFun.hasBasis_uniformity_of_basis X Y hV.1).isCountablyGenerated
  -- The target uniformity is the comap along the canonical inclusion.
  exact Filter.comap.isCountablyGenerated _ _

/-- Continuous maps into a complete pseudometric space form a Baire space in the uniform
topology. -/
instance instBaireSpace [CompleteSpace Y] :
    BaireSpace (UniformTopologyContinuousMap X Y) := by
  -- Completeness and countable generation give a compatible complete pseudometric.
  letI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace
      (UniformTopologyContinuousMap X Y) := inferInstance
  exact BaireSpace.of_completelyPseudoMetrizable

end UniformTopologyContinuousMap
