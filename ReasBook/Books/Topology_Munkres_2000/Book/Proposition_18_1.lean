module

public import Mathlib.Topology.Bases

public section

universe u v

/-- Proposition 18.1: If `ℬ` is a basis for the topology on `Y`, then a function
`f : X → Y` is continuous provided the preimage of every member of `ℬ` is open. -/
theorem continuous_of_isOpen_preimage_basis {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {ℬ : Set (Set Y)}
    (hℬ : TopologicalSpace.IsTopologicalBasis ℬ) (f : X → Y)
    (hf : ∀ U ∈ ℬ, IsOpen (f ⁻¹' U)) : Continuous f :=
  hℬ.continuous_iff.mpr hf
