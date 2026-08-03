module

public import Topology_Munkres_2000.Book.Exercise_41_2
public import Topology_Munkres_2000.Book.Exercise_41_4.Instances
public section

universe u

/- Exercise 41.4 (1): A space with the discrete topology is paracompact. -/
#check fun {X : Type u} [TopologicalSpace X] [DiscreteTopology X] ↦
  (inferInstance : ParacompactSpace X)

namespace OpenOmegaOne

/-- Helper for Exercise 41.4: the identity map from discrete `OpenOmegaOne` to its usual
topology. -/
def fromDiscrete : C(WithDiscreteTopology OpenOmegaOne, OpenOmegaOne) :=
  -- The underlying identity is continuous because its source is discrete.
  ⟨WithTopology.ofTopology, continuous_of_discreteTopology⟩

/-- Helper for Exercise 41.4: the identity from discrete `OpenOmegaOne` has full range. -/
lemma range_fromDiscrete : Set.range fromDiscrete = Set.univ := by
  -- Every point has the same underlying point equipped with the discrete topology as a preimage.
  apply Set.range_eq_univ.mpr
  intro x
  exact ⟨WithTopology.toTopology ⊥ x, rfl⟩

/-- Helper for Exercise 41.4: the range of the identity from discrete `OpenOmegaOne` is
homeomorphic to `OpenOmegaOne`. -/
def rangeFromDiscreteHomeomorph : Set.range fromDiscrete ≃ₜ OpenOmegaOne :=
  -- Identify the range with the universal subspace, then forget that subspace wrapper.
  (Homeomorph.setCongr range_fromDiscrete).trans (Homeomorph.Set.univ OpenOmegaOne)

/-- Helper for Exercise 41.4: the identity from discrete `OpenOmegaOne` to its usual topology
has a non-paracompact range. -/
theorem discreteRange_notParacompact : ¬ ParacompactSpace (Set.range fromDiscrete) := by
  intro h
  -- Transporting the assumed property across the range homeomorphism contradicts the ordinal
  -- space's known failure of paracompactness.
  exact OpenOmegaOne.notParacompact
    (rangeFromDiscreteHomeomorph.paracompactSpace_iff.mp h)

end OpenOmegaOne

/-- Exercise 41.4 (2): Continuous images of paracompact spaces, with the
subspace topology on their ranges, need not be paracompact. -/
theorem continuousRange_not_always_paracompact :
    ∃ f : ContinuousMap.{1, 1} (WithDiscreteTopology OpenOmegaOne) OpenOmegaOne,
      ParacompactSpace (WithDiscreteTopology OpenOmegaOne) ∧
        ¬ ParacompactSpace (Set.range f) := by
  -- The discrete source is paracompact, while the preceding range computation supplies the
  -- required non-paracompact continuous image.
  exact ⟨OpenOmegaOne.fromDiscrete, inferInstance,
    OpenOmegaOne.discreteRange_notParacompact⟩
