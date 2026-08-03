module

public import Topology_Munkres_2000.Book.Exercise_36_5.Charts
public import Topology_Munkres_2000.Book.Exercise_36_5.Separation

public section

universe u

/- Remark 8.99.1 (1). A locally `m`-Euclidean space satisfies the `T₁` axiom. -/
#check fun (m : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) X] ↦
  (ChartedSpace.t1Space (EuclideanSpace ℝ (Fin m)) X : T1Space X)

/- Remark 8.99.1 (2). The line with two origins is locally one-Euclidean but not Hausdorff. -/
#check LineWithTwoOrigins.instChartedSpace
#check LineWithTwoOrigins.notHausdorff
