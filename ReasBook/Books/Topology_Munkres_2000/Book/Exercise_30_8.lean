module

public import Topology_Munkres_2000.Book.Exercise_20_4.RealSequences
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Metrizable.Basic
import Topology_Munkres_2000.Book.Example_30_2

public section

namespace UniformRealSequence

/- Exercise 30.8 (1): The countable real power with the uniform topology satisfies
the first countability axiom, as established in Example 30.2. -/
#check UniformRealSequence.instFirstCountableTopology

/- Exercise 30.8 (2): The countable real power with the uniform topology does not
satisfy the second countability axiom, as established in Example 30.2. -/
#check UniformRealSequence.notSecondCountable

/-- Helper for Exercise 30.8: the uniform topology on real sequences is pseudometrizable. -/
private theorem uniformPseudoMetrizableSpace :
    TopologicalSpace.PseudoMetrizableSpace UniformRealSequence := by
  -- Equip the unwrapped sequence space with the metric that defines the uniform topology.
  letI : TopologicalSpace (ℕ → ℝ) := UniformMetric.topology ℕ
  letI : MetricSpace (ℕ → ℝ) := UniformMetric.metricSpace ℕ
  let unwrap : UniformRealSequence ≃ₜ (ℕ → ℝ) :=
    { WithTopology.equiv (ℕ → ℝ) (UniformMetric.topology ℕ) with
      continuous_toFun := WithTopology.continuous_ofTopology (UniformMetric.topology ℕ)
      continuous_invFun := WithTopology.continuous_toTopology (UniformMetric.topology ℕ) }
  -- Pull pseudometrizability back along the canonical unwrapping homeomorphism.
  exact unwrap.isInducing.pseudoMetrizableSpace

/-- Helper for Exercise 30.8: a separable pseudometrizable space is second-countable. -/
private theorem secondCountable_of_separable_pseudoMetrizable {X : Type*}
    [TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X]
    [TopologicalSpace.SeparableSpace X] : SecondCountableTopology X := by
  -- Choose the compatible countably generated uniformity supplied by pseudometrizability.
  letI : UniformSpace X := TopologicalSpace.pseudoMetrizableSpaceUniformity X
  have hUniformity : (uniformity X).IsCountablyGenerated :=
    TopologicalSpace.pseudoMetrizableSpaceUniformity_countably_generated X
  -- Apply the standard uniform-space implication from separability to second countability.
  exact @UniformSpace.secondCountable_of_separable X inferInstance hUniformity inferInstance

end UniformRealSequence

/-- Exercise 30.8 (3): The countable real power with the uniform topology does not
satisfy the separability axiom. -/
theorem UniformRealSequence.notSeparable :
    ¬ TopologicalSpace.SeparableSpace UniformRealSequence := by
  -- A separability instance would combine with pseudometrizability to give a countable basis.
  intro hSeparable
  letI : TopologicalSpace.SeparableSpace UniformRealSequence := hSeparable
  letI : TopologicalSpace.PseudoMetrizableSpace UniformRealSequence :=
    UniformRealSequence.uniformPseudoMetrizableSpace
  have hSecondCountable : SecondCountableTopology UniformRealSequence :=
    UniformRealSequence.secondCountable_of_separable_pseudoMetrizable
  -- This contradicts the non-second-countability established in Example 30.2.
  exact UniformRealSequence.notSecondCountable hSecondCountable

/-- The canonical non-Lindelöf companion instance for Exercise 30.8. -/
@[instance] theorem UniformRealSequence.instNonLindelofSpace :
    NonLindelofSpace UniformRealSequence := by
  -- Express the typeclass goal as the proposition that no Lindelöf instance exists.
  rw [← not_LindelofSpace_iff]
  intro hLindelof
  letI : LindelofSpace UniformRealSequence := hLindelof
  letI : TopologicalSpace.PseudoMetrizableSpace UniformRealSequence :=
    UniformRealSequence.uniformPseudoMetrizableSpace
  -- Lindelöf pseudometrizable spaces are second-countable, contradicting Example 30.2.
  exact UniformRealSequence.notSecondCountable inferInstance

/-- The countable real power with the uniform topology does not carry a
`LindelofSpace` instance. -/
theorem UniformRealSequence.notLindelof : ¬ LindelofSpace UniformRealSequence :=
  not_LindelofSpace_iff.mpr inferInstance
