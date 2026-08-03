module

public import Mathlib.Topology.Metrizable.Basic

public section

universe u v

namespace TopologicalSpace.MetrizableSpace

/-- Theorem 21.2: A countable product of metrizable spaces is metrizable in the
product topology. -/
instance pi_countable {ι : Type u} [Countable ι] {X : ι → Type v}
    [∀ i, TopologicalSpace (X i)] [∀ i, MetrizableSpace (X i)] :
    MetrizableSpace (∀ i, X i) := by
  -- Equip every factor with its canonical compatible pseudometric uniformity.
  letI (i : ι) : UniformSpace (X i) := pseudoMetrizableSpaceUniformity (X i)
  -- These factor uniformities are countably generated, so the product uniformity is too.
  letI (i : ι) : (uniformity (X i)).IsCountablyGenerated :=
    pseudoMetrizableSpaceUniformity_countably_generated (X i)
  -- The product uniformity and the coordinatewise T₀ property yield metrizability.
  infer_instance

end TopologicalSpace.MetrizableSpace
