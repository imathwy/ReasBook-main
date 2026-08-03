module

public import Topology_Munkres_2000.Book.Example_71_1.Geometry

public section

namespace InfiniteEarring

/-- The planar carrier of the infinite earring. -/
def carrier : Set Plane :=
  ⋃ n : ℕ+, circle n

/-- The infinite earring with its subspace topology from the Euclidean plane. -/
abbrev Space := carrier

/-- The origin belongs to the planar carrier of the infinite earring. -/
theorem zero_mem_carrier : (0 : Plane) ∈ carrier := by
  -- Every component circle passes through the origin; use the first one.
  rw [carrier, Set.mem_iUnion]
  refine ⟨1, ?_⟩
  rw [mem_circle_iff, EuclideanSpace.dist_eq]
  simp [center_apply, Fin.sum_univ_two]

/-- The common base point of the component circles of the infinite earring. -/
def origin : Space := ⟨0, zero_mem_carrier⟩

/-- The `n`th component circle, regarded as a subset of the infinite earring. -/
def component (n : ℕ+) : Set Space :=
  Subtype.val ⁻¹' circle n

/-- A point lies in the carrier exactly when it lies on one of the component circles. -/
theorem mem_carrier_iff (x : Plane) :
    x ∈ carrier ↔ ∃ n : ℕ+, x ∈ circle n := by
  -- Membership in the indexed union is exactly existential membership.
  simp only [carrier, Set.mem_iUnion]

/-- The ambient point underlying the base point is the origin of the plane. -/
theorem origin_coe : (origin : Plane) = 0 := by
  -- Coercing the subtype point forgets only its carrier proof.
  rfl

/-- Membership in a component is membership in its ambient planar circle. -/
theorem mem_component_iff (x : Space) (n : ℕ+) :
    x ∈ component n ↔ (x : Plane) ∈ circle n := by
  -- Membership in the preimage unfolds to ambient circle membership.
  rfl

end InfiniteEarring
