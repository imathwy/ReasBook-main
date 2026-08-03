module

public import Topology_Munkres_2000.Book.Definition_21_3.ClosedUnitDisk
public import Topology_Munkres_2000.Book.Definition_55_2.Nonvanishing

public section

/-- The Euclidean plane used for vector fields on the closed unit disk. -/
abbrev EuclideanPlane := EuclideanSpace ℝ (Fin 2)

/-- A vector field on the closed unit disk is a continuous plane-valued map. -/
abbrev DiskVectorField := C(B², EuclideanPlane)

namespace DiskVectorField

/-- A nonvanishing disk vector field as a continuous map into the punctured plane. -/
abbrev toPuncturedPlane (v : DiskVectorField) (hv : v.IsNonvanishing) :
    C(B², {y : EuclideanPlane // y ≠ 0}) :=
  v.toNonzero hv

/-- The punctured-plane form of a nonvanishing vector field has the original value. -/
theorem toPuncturedPlane_apply (v : DiskVectorField) (hv : v.IsNonvanishing)
    (x : B²) : (v.toPuncturedPlane hv x : EuclideanPlane) = v x :=
  rfl

end DiskVectorField
