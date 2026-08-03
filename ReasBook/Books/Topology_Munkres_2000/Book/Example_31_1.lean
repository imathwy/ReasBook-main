module

public import Topology_Munkres_2000.Book.Example_31_1.Separation

public section

namespace RealTopology

/- Example 31.1 (1): The real line with the `K`-topology is Hausdorff. -/
#check kT2Space

/-- Example 31.1 (2): The `K`-topology fails the point-versus-closed-set
regularity property. -/
theorem kNotRegularSpace :
    ¬ @RegularSpace ℝ k := by
  -- Regularity would provide disjoint neighborhoods of the closed set and zero.
  intro hRegular
  letI : TopologicalSpace ℝ := k
  letI : RegularSpace ℝ := hRegular
  have hDisjoint : Disjoint (nhdsSet positiveReciprocals) (nhds 0) :=
    RegularSpace.regular positiveReciprocalsClosed zeroNotMemPositiveReciprocals
  obtain ⟨v, ⟨hv, hKv⟩, u, ⟨h0u, hu⟩, hvu⟩ :=
    ((hasBasis_nhdsSet positiveReciprocals).disjoint_iff
      (nhds_basis_opens (0 : ℝ))).mp hDisjoint
  -- The interval obstruction rules out precisely these open representatives.
  exact zeroAndPositiveReciprocalsNotSeparated
    ⟨u, v, hu, hv, h0u, hKv, hvu.symm⟩

/-- Consequence of Example 31.1: the real line with the `K`-topology is not a
`T₃` space. -/
theorem kNotT3Space :
    ¬ @T3Space ℝ k := by
  intro h
  exact kNotRegularSpace h.toRegularSpace

end RealTopology
