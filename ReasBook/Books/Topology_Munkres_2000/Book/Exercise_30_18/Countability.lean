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
  -- Rewrite the right uniformity as the pullback of the neighborhood filter at the identity.
  rw [uniformity_eq_comap_nhds_one']
  -- First countability at the identity is preserved by this pullback.
  exact Filter.comap.isCountablyGenerated _ _

/-- A separable first-countable topological group has a countable topological basis. -/
instance secondCountableTopologyOfSeparable (G : Type u) [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] [FirstCountableTopology G]
    [TopologicalSpace.SeparableSpace G] : SecondCountableTopology G := by
  -- Equip the group with its canonical right uniformity, which induces the given topology.
  letI : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  -- Supply the countable uniformity basis obtained from first countability at the identity.
  letI : (uniformity G).IsCountablyGenerated := rightUniformity_isCountablyGenerated G
  -- Uniform balls centered at a countable dense set form a countable topological basis.
  exact UniformSpace.secondCountable_of_separable G

/-- A Lindelöf first-countable topological group has a countable topological basis. -/
instance secondCountableTopologyOfLindelof (G : Type u) [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] [FirstCountableTopology G] [LindelofSpace G] :
    SecondCountableTopology G := by
  -- Equip the group with the canonical right uniformity and its countable entourage basis.
  letI : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  letI : (uniformity G).IsCountablyGenerated := rightUniformity_isCountablyGenerated G
  -- Lindelöfness selects countably many uniform balls covering the group for each entourage.
  apply UniformSpace.secondCountable_of_almost_dense_set
  intro U hU
  exact countable_cover_nhds fun x => UniformSpace.ball_mem_nhds x hU

end IsTopologicalGroup
