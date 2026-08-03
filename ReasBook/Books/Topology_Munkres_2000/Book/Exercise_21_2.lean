module

import Mathlib.Topology.MetricSpace.Isometry

/- Exercise 21.2: A map between metric spaces preserving every distance is an
isometric embedding, hence a topological embedding. -/
#check Isometry.isEmbedding
#check isometry_iff_dist_eq
