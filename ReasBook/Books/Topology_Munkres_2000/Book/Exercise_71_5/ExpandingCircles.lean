module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.PNat.Basic

public section

namespace ExpandingCircles

/-- The Euclidean plane containing the expanding circles. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The center `(n, 0)` of the circle of radius `n`. -/
noncomputable def center (n : ℕ+) : Plane :=
  WithLp.toLp 2 ![(n : ℝ), 0]

/-- Helper for Exercise 71.5: the coordinates of an expanding circle's center. -/
lemma center_apply (n : ℕ+) (i : Fin 2) :
    center n i = ![(n : ℝ), 0] i := by
  -- The `WithLp` wrapper changes the norm but preserves every coordinate.
  rfl

/-- The circle of radius `n` centered at `(n, 0)`. -/
def circle (n : ℕ+) : Set Plane :=
  Metric.sphere (center n) (n : ℝ)

/-- Helper for Exercise 71.5: membership in an expanding circle is its sphere equation. -/
lemma mem_circle_iff (x : Plane) (n : ℕ+) :
    x ∈ circle n ↔ dist x (center n) = (n : ℝ) := by
  -- Unfold the geometric object once and expose the standard metric API.
  rw [circle, Metric.mem_sphere]

/-- The planar union of all circles of positive integral radius. -/
def carrier : Set Plane :=
  ⋃ n : ℕ+, circle n

/-- The union of the expanding circles with its subspace topology. -/
abbrev Space := carrier

/-- The origin belongs to every expanding circle. -/
theorem zero_mem_circle (n : ℕ+) : (0 : Plane) ∈ circle n := by
  -- The distance from `(0, 0)` to `(n, 0)` is the positive radius `n`.
  rw [mem_circle_iff, EuclideanSpace.dist_eq]
  have hnnonneg : 0 ≤ (n : ℝ) := by
    exact_mod_cast n.property.le
  simp [center_apply, Fin.sum_univ_two, hnnonneg]

/-- The origin belongs to the carrier of the expanding circles. -/
theorem zero_mem_carrier : (0 : Plane) ∈ carrier := by
  -- Membership in any one component, here the first, gives union membership.
  rw [carrier, Set.mem_iUnion]
  exact ⟨1, zero_mem_circle 1⟩

/-- The common basepoint of the expanding circles. -/
def origin : Space := ⟨0, zero_mem_carrier⟩

/-- The `n`th circle, regarded as a subspace of the union. -/
def component (n : ℕ+) : Set Space :=
  Subtype.val ⁻¹' circle n

/-- The common basepoint belongs to every component circle. -/
theorem origin_mem_component (n : ℕ+) : origin ∈ component n := by
  -- Forgetting the carrier proof exposes the planar origin on the `n`th circle.
  exact zero_mem_circle n

/-- The common basepoint regarded as a point of the `n`th component circle. -/
abbrev componentOrigin (n : ℕ+) : component n := ⟨origin, origin_mem_component n⟩

/-- A point lies in the carrier exactly when it lies on one expanding circle. -/
theorem mem_carrier_iff (x : Plane) :
    x ∈ carrier ↔ ∃ n : ℕ+, x ∈ circle n := by
  -- Membership in an indexed union is existential membership.
  simp only [carrier, Set.mem_iUnion]

/-- The ambient coordinate of the common basepoint is the planar origin. -/
theorem origin_coe : (origin : Plane) = 0 := by
  -- Coercing the subtype point forgets only its carrier proof.
  rfl

/-- Membership in a component is membership in its ambient planar circle. -/
theorem mem_component_iff (x : Space) (n : ℕ+) :
    x ∈ component n ↔ (x : Plane) ∈ circle n := by
  -- Membership in the preimage is definitionally ambient circle membership.
  rfl

end ExpandingCircles
