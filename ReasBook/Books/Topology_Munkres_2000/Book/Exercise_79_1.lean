module

public import Topology_Munkres_2000.Book.Theorem_59_3
public import Topology_Munkres_2000.Book.Theorem_53_1.CircleMap
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Topology.Homotopy.Lifting

public section

/-- Exercise 79.1. If `n > 1`, every continuous map from the standard
`n`-sphere to the circle is nullhomotopic. -/
theorem standardSphereToCircle_nullhomotopic (n : ℕ) (hn : 1 < n)
    (f : C(StandardSphere n, Circle)) :
    f.Nullhomotopic := by
  -- Simple connectedness supplies a basepoint and permits lifting through the universal cover.
  letI : SimplyConnectedSpace (StandardSphere n) :=
    simplyConnectedSpace_standardSphere n hn
  letI : LocallyPathConnectedSpace (StandardSphere n) :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin n))
      (StandardSphere n)
  obtain ⟨x₀⟩ := (inferInstance : Nonempty (StandardSphere n))
  obtain ⟨e₀, he₀⟩ := Circle.turnExp_surjective (f x₀)
  obtain ⟨F, hF, -⟩ :=
    Circle.isCoveringMap_turnExp.existsUnique_continuousMap_lifts f x₀ e₀ he₀
  let turnExpMap : C(ℝ, Circle) :=
    ⟨Circle.turnExp, Circle.isCoveringMap_turnExp.continuous⟩
  -- Convert the lift specification to equality of bundled continuous maps.
  have liftEquation : turnExpMap.comp F = f := by
    apply ContinuousMap.ext
    intro x
    change Circle.turnExp (F x) = f x
    exact congrFun hF.2 x
  -- Contract the real-valued lift, then project that contraction to the circle.
  have liftNullhomotopic : F.Nullhomotopic := by
    simpa only [ContinuousMap.id_comp] using
      (id_nullhomotopic ℝ).comp_left F
  rw [← liftEquation]
  exact liftNullhomotopic.comp_right turnExpMap
