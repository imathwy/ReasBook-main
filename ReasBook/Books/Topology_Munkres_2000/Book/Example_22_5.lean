module

public import Topology_Munkres_2000.Book.Example_22_5.Torus
public import Topology_Munkres_2000.Book.Proposition_22_1

public section

/- Example 22.5: The partition of the unit square obtained by identifying each pair of
opposite edges. -/
#check TorusSquare.identified

/- The partition blocks are determined coordinatewise by endpoint
identification. -/
#check TorusSquare.identified_iff

/- Pasting each pair of opposite edges gives a quotient map onto the torus. -/
#check TorusSquare.toTorus_isQuotientMap

/- The quotient map realizes the pasted square as the torus. -/
#check TorusSquare.toTorus

/-- The image of an open saturated subset of the unit square
is open in the torus. -/
theorem TorusSquare.isOpen_image_toTorus (U : Set (unitInterval × unitInterval))
    (hU : IsOpen U) (h_saturated : Set.IsSaturated toTorus U) :
    IsOpen (toTorus '' U) :=
  toTorus_isQuotientMap.isOpen_image_of_isSaturated h_saturated hU

end
