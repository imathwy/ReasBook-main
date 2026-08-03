module

public import Topology_Munkres_2000.Book.Exercise_59_1.PointedWedge
public import Topology_Munkres_2000.Book.Definition_71_4.WedgeOfCircles

public section

universe u

namespace Topology.CircleWedge

/-- The distinguished point `1 ∈ Circle`. -/
def basepoint : Circle :=
  ⟨1, by simp⟩

/-- The quotient model of the wedge of circles indexed by `J`. -/
abbrev Space (J : Type u) :=
  IndexedPointedWedge.Space (fun _ : J ↦ Circle) (fun _ ↦ basepoint)

/-- The canonical inclusion of one circle into the indexed circle wedge. -/
def inclusion {J : Type u} (j : J) : Circle → Space J :=
  IndexedPointedWedge.inclusion (fun _ : J ↦ Circle) (fun _ ↦ basepoint) j

/-- The image of one circle in the indexed circle wedge. -/
def circle {J : Type u} (j : J) : Set (Space J) :=
  Set.range (inclusion j)

/-- The common point of the indexed circle wedge, represented in one factor. -/
def point {J : Type u} (j : J) : Space J :=
  IndexedPointedWedge.point (fun _ : J ↦ Circle) (fun _ ↦ basepoint) j

/-- The common point is independent of the circle used to represent it. -/
theorem point_eq {J : Type u} (i j : J) : point i = point j :=
  IndexedPointedWedge.point_eq (fun _ : J ↦ Circle) (fun _ ↦ basepoint) i j

end Topology.CircleWedge
