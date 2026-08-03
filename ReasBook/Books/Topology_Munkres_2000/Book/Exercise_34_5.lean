module

import Topology_Munkres_2000.Book.Exercise_34_3
public import Topology_Munkres_2000.Book.Exercise_34_5.Instances
public import Mathlib.Topology.Metrizable.Basic

public section

open OnePoint TopologicalSpace

universe u

/-- Exercise 34.5 (1). If a locally compact Hausdorff space has a countable basis,
then its one-point compactification is metrizable. -/
theorem onePoint_metrizableSpace_of_secondCountableTopology
    {X : Type u} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [SecondCountableTopology X] : MetrizableSpace (OnePoint X) := by
  exact metrizableSpace_iff_secondCountableTopology_of_compact.mpr inferInstance

/-- Exercise 34.5 (2). If the one-point compactification of a space is metrizable,
then the original space has a countable basis. -/
theorem secondCountableTopology_of_onePoint_metrizableSpace
    {X : Type u} [TopologicalSpace X] [MetrizableSpace (OnePoint X)] :
    SecondCountableTopology X := by
  exact isOpenEmbedding_coe.isEmbedding.secondCountableTopology

/-- Exercise 34.5. For a locally compact Hausdorff space, the one-point compactification
is metrizable if and only if the original space has a countable basis. -/
theorem onePoint_metrizableSpace_iff_secondCountableTopology
    {X : Type u} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X] :
    MetrizableSpace (OnePoint X) ↔ SecondCountableTopology X := by
  constructor
  · intro h
    -- Local instance justification (proof-local temporary data): installs the assumed class.
    letI : MetrizableSpace (OnePoint X) := h
    exact secondCountableTopology_of_onePoint_metrizableSpace
  · intro h
    -- Local instance justification (proof-local temporary data): installs the assumed class.
    letI : SecondCountableTopology X := h
    exact onePoint_metrizableSpace_of_secondCountableTopology

end
