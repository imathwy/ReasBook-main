module

public import Topology_Munkres_2000.Book.Exercise_8_99_3.Instances
public import Mathlib.Topology.Algebra.Ring.Real

public section

/- Exercise 8.99.3 (1). The real line is locally 1-euclidean. -/
#check (inferInstance : ChartedSpace (EuclideanSpace ℝ (Fin 1)) ℝ)

/- Exercise 8.99.3 (2). The real line is a 1-manifold: it is Hausdorff and has a
countable basis. -/
#check (inferInstance : T2Space ℝ)
#check (inferInstance : SecondCountableTopology ℝ)

/- Exercise 8.99.3 (3). The real line does not satisfy condition (i), since it is
not compact. -/
#check (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace ℝ) : ¬ CompactSpace ℝ)
