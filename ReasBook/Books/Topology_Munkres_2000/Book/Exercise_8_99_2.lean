module

public import Topology_Munkres_2000.Book.Definition_36_1.TopologicalManifold
public import Topology_Munkres_2000.Book.Exercise_36_1.Metrizable
public import Topology_Munkres_2000.Book.Exercise_8_99_2.Separation
public import Mathlib.Topology.GDelta.MetrizableSpace

public section

universe u

/- Exercise 8.99.2 (1). A compact Hausdorff locally `m`-Euclidean space is an `m`-manifold. -/
#check fun (m : ℕ) {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) X] [CompactSpace X] [T2Space X] ↦
  TopologicalManifold.of m inferInstance
    (ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin m)) X)

/- Exercise 8.99.2 (2). An `m`-manifold is metrizable. -/
#check fun (m : ℕ) {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) X] [TopologicalManifold m X] ↦
  (ChartedSpace.metrizableSpace (EuclideanSpace ℝ (Fin m)) :
    TopologicalSpace.MetrizableSpace X)

/- Exercise 8.99.2 (3). A metrizable space is normal. -/
#check fun (X : Type u) [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] ↦
  (inferInstance : NormalSpace X)

/- Exercise 8.99.2 (4). A normal locally `m`-Euclidean space is Hausdorff. -/
#check fun (m : ℕ) {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) X] [NormalSpace X] ↦
  (ChartedSpace.t2SpaceOfNormal (EuclideanSpace ℝ (Fin m)) : T2Space X)
