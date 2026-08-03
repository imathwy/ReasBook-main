module

public import Topology_Munkres_2000.Book.Example_37_1.EllipticFamily

public section

open Set

namespace FixedFociEllipse

/-- Helper for Example 37.2: the second focus belongs to `region c` exactly when the
distance between the two foci is at most `c`. -/
lemma q_mem_region_iff (c : ℝ) : q ∈ region c ↔ dist p q ≤ c := by
  -- Normalize the focal-distance sum at the focus `q`.
  rw [mem_region, dist_self, add_zero, dist_comm q p]

/-- Example 37.2. The successful coordinate choice `(1 / 2, 2 / 3)`, represented by
`q`, belongs to every fixed-foci elliptical region. -/
theorem q_mem_iInter_family : q ∈ ⋂ D ∈ family, D := by
  -- Reduce intersection membership to an arbitrary member of the ellipse family.
  rw [mem_iInter₂]
  intro D hD
  -- Expose its focal-distance bound and replace the member by its defining region.
  rw [mem_family] at hD
  obtain ⟨c, hc, _, rfl⟩ := hD
  -- Membership of the focus follows from the weak form of the strict bound.
  rw [q_mem_region_iff]
  exact hc.le

/-- The second focus belongs to each fixed-foci elliptical region in the family. -/
theorem q_mem_of_mem_family {D : Set Plane} (hD : D ∈ family) : q ∈ D :=
  mem_iInter₂.mp q_mem_iInter_family D hD

end FixedFociEllipse
