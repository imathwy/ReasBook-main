module

public import Topology_Munkres_2000.Book.Exercise_35_4.RadialRetraction
public import Topology_Munkres_2000.Book.Exercise_58_9.Degree

noncomputable section

public section

namespace PuncturedPlaneMap

/-- The winding number of a continuous map from the circle to the punctured plane, relative to
chosen integer coordinates on the source and target fundamental groups. -/
def windingNumber
    (sourceCoordinates : Circle.FundamentalOrientation)
    (h : C(Circle, EuclideanPlane.punctured))
    (targetCoordinates : FundamentalGroup EuclideanPlane.punctured (h 1) ≃* Multiplicative ℤ) : ℤ :=
  Multiplicative.toAdd
    (targetCoordinates
      (FundamentalGroup.map h 1
        (sourceCoordinates.symm (Multiplicative.ofAdd 1))))

/-- The induced fundamental-group map sends the chosen source generator to the power indexed by
`windingNumber` of the chosen target generator. -/
theorem windingNumber_spec
    (sourceCoordinates : Circle.FundamentalOrientation)
    (h : C(Circle, EuclideanPlane.punctured))
    (targetCoordinates : FundamentalGroup EuclideanPlane.punctured (h 1) ≃* Multiplicative ℤ) :
    FundamentalGroup.map h 1 (sourceCoordinates.symm (Multiplicative.ofAdd 1)) =
      targetCoordinates.symm
        (Multiplicative.ofAdd (windingNumber sourceCoordinates h targetCoordinates)) := by
  simp [windingNumber]


end PuncturedPlaneMap
