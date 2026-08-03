module

public import Topology_Munkres_2000.Book.Exercise_2_99_4

public section

namespace Subgroup

/-- Helper for Exercise 25.9: conjugation preserves the connected component of the identity. -/
lemma connectedComponentOfOne_conj_mem (G : Type u) [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] (n : G) (hn : n ∈ connectedComponentOfOne G) (g : G) :
    g * n * g⁻¹ ∈ connectedComponentOfOne G := by
  -- Regard the subgroup membership as membership in the connected component of `1`.
  have hn' : n ∈ connectedComponent (1 : G) := by
    exact hn
  -- Continuous conjugation maps that component into the component of the conjugated base point.
  have hconj : g * n * g⁻¹ ∈ connectedComponent (g * 1 * g⁻¹) :=
    (IsTopologicalGroup.continuous_conj g).mapsTo_connectedComponent 1 hn'
  -- Conjugation fixes the identity, so the target component is again the component of `1`.
  have hcomponent : g * n * g⁻¹ ∈ connectedComponent (1 : G) := by
    simpa only [mul_one, mul_inv_cancel] using hconj
  exact hcomponent

/-- Exercise 25.9: In a topological group, the connected component containing the
identity element is a normal subgroup. -/
instance connectedComponentOfOne_normal (G : Type u) [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] : (connectedComponentOfOne G).Normal :=
  -- The companion lemma is precisely the conjugation-closure field of normality.
  ⟨connectedComponentOfOne_conj_mem G⟩

end Subgroup
