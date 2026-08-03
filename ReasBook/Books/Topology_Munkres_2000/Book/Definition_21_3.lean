module

public import Topology_Munkres_2000.Book.Definition_21_3.ClosedUnitDisk

/- Definition 21.3. The set `B²` is the closed unit ball in `ℝ²`. -/
#check (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)

#check B²
