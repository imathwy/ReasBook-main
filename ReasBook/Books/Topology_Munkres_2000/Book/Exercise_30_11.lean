module

public import Mathlib.Topology.Compactness.Lindelof

public section

open Set TopologicalSpace

universe u v

/- Exercise 30.11 (1): A continuous image of a Lindelöf space is Lindelöf. -/
#check isLindelof_range

/-- Exercise 30.11 (2): A continuous image of a space with a countable dense subset
has a countable dense subset in its subspace topology. -/
theorem Continuous.separableSpace_range {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [SeparableSpace X] {f : X → Y}
    (hf : Continuous f) : SeparableSpace (range f) :=
  rangeFactorization_surjective.denseRange.separableSpace
    (hf.subtype_mk fun x ↦ mem_range_self x)
