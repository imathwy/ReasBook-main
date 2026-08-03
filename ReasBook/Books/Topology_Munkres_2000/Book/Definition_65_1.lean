module

public import Topology_Munkres_2000.Book.Definition_65_1.WindingNumber

public section

/- Definition 65.1: The winding number of a continuous map `h : C(Circle,
EuclideanPlane.punctured)` is the integral exponent obtained from the induced fundamental-group
homomorphism after choosing generators of the source and target fundamental groups. -/
#check PuncturedPlaneMap.windingNumber
#check PuncturedPlaneMap.windingNumber_spec
