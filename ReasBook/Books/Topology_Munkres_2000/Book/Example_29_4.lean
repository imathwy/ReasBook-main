module

public import Topology_Munkres_2000.Book.Example_29_4.Sphere

public section

/- Example 29.4 (1): The one-point compactification of `ℝ` is homeomorphic to
the circle `S¹`, modeled as the unit sphere in `EuclideanSpace ℝ (Fin 2)`. -/
#check OnePoint.realHomeomorphSphere

/- Example 29.4 (2): The one-point compactification of `ℝ²`, modeled as
`EuclideanSpace ℝ (Fin 2)`, is homeomorphic to the sphere `S²`. -/
#check OnePoint.planeHomeomorphSphere

/- Example 29.4 (3): Regarding `ℝ²` as `ℂ`, its one-point compactification
`OnePoint ℂ` is homeomorphic to `S²` and is called the Riemann sphere or the
extended complex plane. -/
#check OnePoint.complexHomeomorphSphere
