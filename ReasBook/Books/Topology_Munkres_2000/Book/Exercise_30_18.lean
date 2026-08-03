module

public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.UniformSpace.Cauchy

universe u

public section

namespace IsTopologicalGroup

/-- Helper for Exercise 30.18: the canonical right uniformity of a first-countable
topological group is countably generated. -/
lemma rightUniformity_isCountablyGenerated (G : Type u) [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] [FirstCountableTopology G] :
    (@uniformity G (IsTopologicalGroup.rightUniformSpace G)).IsCountablyGenerated := by
  -- Express the right uniformity through the neighborhood filter at the identity.
  rw [uniformity_eq_comap_nhds_one']
  exact Filter.comap.isCountablyGenerated _ _

end IsTopologicalGroup

/-- The separable case of Exercise 30.18: a first-countable topological group with a
countable dense subset has a countable basis. -/
instance IsTopologicalGroup.secondCountableTopologyOfSeparable
    (G : Type u) [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] [FirstCountableTopology G]
    [TopologicalSpace.SeparableSpace G] : SecondCountableTopology G := by
  -- Use the canonical right uniformity, whose topology is the original group topology.
  letI : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  letI : (uniformity G).IsCountablyGenerated :=
    IsTopologicalGroup.rightUniformity_isCountablyGenerated G
  exact UniformSpace.secondCountable_of_separable G

/-- The Lindelöf case of Exercise 30.18: a first-countable Lindelöf topological group
has a countable basis. -/
instance IsTopologicalGroup.secondCountableTopologyOfLindelof
    (G : Type u) [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] [FirstCountableTopology G] [LindelofSpace G] :
    SecondCountableTopology G := by
  -- For each entourage, Lindelöfness supplies countably many uniform balls covering the group.
  letI : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  letI : (uniformity G).IsCountablyGenerated :=
    IsTopologicalGroup.rightUniformity_isCountablyGenerated G
  apply UniformSpace.secondCountable_of_almost_dense_set
  intro U hU
  exact countable_cover_nhds fun x ↦ UniformSpace.ball_mem_nhds x hU

/-- Exercise 30.18: A first-countable topological group that is separable or Lindelöf
has a countable basis. -/
theorem IsTopologicalGroup.secondCountableTopologyOfSeparableOrLindelof
    (G : Type u) [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] [FirstCountableTopology G]
    (hG : TopologicalSpace.SeparableSpace G ∨ LindelofSpace G) :
    SecondCountableTopology G := by
  -- Apply the corresponding companion instance in each of the two cases.
  rcases hG with hG | hG
  · letI : TopologicalSpace.SeparableSpace G := hG
    exact inferInstance
  · letI : LindelofSpace G := hG
    exact inferInstance
