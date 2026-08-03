module

public import Topology_Munkres_2000.Book.Definition_55_2.Sphere

public section

/-- A vector field on the standard closed ball is a continuous ambient vector-valued map. -/
abbrev BallVectorField (n : ℕ) :=
  C(ClosedUnitBall n, EuclideanSpace ℝ (Fin (n + 1)))
