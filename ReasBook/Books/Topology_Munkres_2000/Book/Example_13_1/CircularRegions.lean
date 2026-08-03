module

public import Topology_Munkres_2000.Book.Example_11_1.CircularRegion
public import Mathlib.Topology.Bases

public section

namespace EuclideanPlane

/-- The point sets of circular regions in the Euclidean plane. -/
def circularRegions : Set (Set (EuclideanSpace ℝ (Fin 2))) :=
  Set.range CircularRegion.set

/-- A set belongs to `circularRegions` exactly when it is the point set of a circular region. -/
theorem mem_circularRegions (U : Set (EuclideanSpace ℝ (Fin 2))) :
    U ∈ circularRegions ↔ ∃ V : CircularRegion, V.set = U := by
  rfl

/-- A set belongs to `circularRegions` exactly when it is a positive-radius open metric ball. -/
theorem mem_circularRegions_iff_ball (U : Set (EuclideanSpace ℝ (Fin 2))) :
    U ∈ circularRegions ↔ ∃ x r, 0 < r ∧ U = Metric.ball x r := by
  constructor
  · rintro ⟨V, rfl⟩
    exact ⟨V.center, V.radius, V.radius_pos, V.set_eq_ball⟩
  · rintro ⟨x, r, hr, rfl⟩
    exact ⟨⟨x, r, hr⟩, CircularRegion.set_eq_ball _⟩

/-- The circular regions form a basis for the Euclidean topology on the plane. -/
theorem isTopologicalBasis_circularRegions :
    TopologicalSpace.IsTopologicalBasis circularRegions := by
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro U ⟨V, rfl⟩
    rw [V.set_eq_ball]
    exact Metric.isOpen_ball
  · intro x U hx hU
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hx
    refine ⟨Metric.ball x r, ⟨⟨x, r, hr⟩, ?_⟩, Metric.mem_ball_self hr, hball⟩
    exact CircularRegion.set_eq_ball _

/-- A plane subset is open exactly when every point has a contained circular region. -/
theorem isOpen_iff_circularRegion_subset (U : Set (EuclideanSpace ℝ (Fin 2))) :
    IsOpen U ↔ ∀ x ∈ U, ∃ V ∈ circularRegions, x ∈ V ∧ V ⊆ U :=
  isTopologicalBasis_circularRegions.isOpen_iff

end EuclideanPlane
