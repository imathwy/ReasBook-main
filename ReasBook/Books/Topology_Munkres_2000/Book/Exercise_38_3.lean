module

public import Topology_Munkres_2000.Book.Lemma_38_1.InducedCompactification
public import Mathlib.Topology.MetricSpace.PiNat
public import Mathlib.Topology.Metrizable.Uniformity

public section

universe u

/-- Helper for Exercise 38.3: a separable metrizable space admits a same-universe metrizable
compactification. -/
lemma existsMetrizableCompactification_of_separableSpace
    (X : Type u) [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    [TopologicalSpace.SeparableSpace X] :
    ∃ C : Compactification.{u, u} X, TopologicalSpace.MetrizableSpace C := by
  -- Choose a compatible metric and embed the space into the Hilbert cube.
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  obtain ⟨f, hf⟩ := Metric.PiNatEmbed.exists_embedding_to_hilbert_cube (X := X)
  -- Lift the Hilbert cube so that the induced compactification remains in universe `u`.
  let fLift : X → ULift.{u} (ℕ → unitInterval) := ULift.up ∘ f
  have hfLift : Topology.IsEmbedding fLift :=
    Homeomorph.ulift.symm.isEmbedding.comp hf
  letI : TopologicalSpace.MetrizableSpace (ULift.{u} (ℕ → unitInterval)) :=
    Topology.IsEmbedding.uliftDown.metrizableSpace
  let C : Compactification.{u, u} X :=
    InducedCompactification.compactification fLift hfLift
  -- The closure of the lifted range inherits metrizability from the ambient cube.
  refine ⟨C, ?_⟩
  exact (InducedCompactification.isEmbedding_inclusion fLift).metrizableSpace

/-- Helper for Exercise 38.3: a metrizable compactification forces the original space to be
separable. -/
lemma separableSpace_of_metrizableCompactification
    (X : Type u) [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    (hC : ∃ C : Compactification.{u, u} X, TopologicalSpace.MetrizableSpace C) :
    TopologicalSpace.SeparableSpace X := by
  -- A compact metrizable target is second countable.
  obtain ⟨C, hCmetrizable⟩ := hC
  letI : TopologicalSpace.MetrizableSpace C := hCmetrizable
  letI : SecondCountableTopology C := inferInstance
  -- Pull separability back along the compactification embedding.
  exact C.isDenseEmbedding.isEmbedding.separableSpace

/-- Exercise 38.3: A metrizable space has a metrizable compactification if and only if it is
separable. -/
theorem metrizableCompactification_iff_separableSpace
    (X : Type u) [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] :
    (∃ C : Compactification.{u, u} X, TopologicalSpace.MetrizableSpace C) ↔
      TopologicalSpace.SeparableSpace X := by
  -- Apply the construction and obstruction lemmas in the two directions.
  constructor
  · exact separableSpace_of_metrizableCompactification X
  · intro hX
    letI : TopologicalSpace.SeparableSpace X := hX
    exact existsMetrizableCompactification_of_separableSpace X

/-- For a metrizable space, existence of a metrizable compactification is equivalent to second
countability. -/
theorem metrizableCompactification_iff_secondCountableTopology
    (X : Type u) [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] :
    (∃ C : Compactification.{u, u} X, TopologicalSpace.MetrizableSpace C) ↔
      SecondCountableTopology X := by
  -- Translate the compactification criterion through the metrizable equivalence of
  -- separability and second countability.
  rw [metrizableCompactification_iff_separableSpace]
  constructor
  · intro hX
    letI : TopologicalSpace.SeparableSpace X := hX
    letI : UniformSpace X := TopologicalSpace.pseudoMetrizableSpaceUniformity X
    letI : (uniformity X).IsCountablyGenerated :=
      TopologicalSpace.pseudoMetrizableSpaceUniformity_countably_generated X
    exact UniformSpace.secondCountable_of_separable X
  · intro hX
    letI : SecondCountableTopology X := hX
    exact inferInstance
