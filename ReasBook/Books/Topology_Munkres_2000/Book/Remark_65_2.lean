module

public import Topology_Munkres_2000.Book.Example_29_4.Sphere

public section

open Metric Module

/- Remark 65.2: Identify the one-point compactification of `ℝ²` with `S²`;
for a chosen homeomorphism `e`, the corresponding points are `e 0` and
`e OnePoint.infty`. -/
#check OnePoint.planeHomeomorphSphere
#check fun
  (e : OnePoint (EuclideanSpace ℝ (Fin 2)) ≃ₜ
    sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ↦
  (e (OnePoint.some 0), e OnePoint.infty)
