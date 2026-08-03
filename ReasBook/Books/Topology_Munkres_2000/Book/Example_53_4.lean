module

public import Topology_Munkres_2000.Book.Example_53_4.Covering
public import Topology_Munkres_2000.Book.Example_53_4.Doughnut

public section

/- Example 53.4 (1). The coordinatewise circle exponential covers the torus by the plane. -/
#check Torus.cover_isCoveringMap

/- Example 53.4 (2). Every integer unit square maps onto the whole torus. -/
#check Torus.unitSquare_surjOn

/- Example 53.4 (3). The product torus is homeomorphic to the familiar doughnut surface. -/
#check Torus.doughnutHomeomorph

/-- Example 53.4: The coordinatewise circle exponential covers the torus, maps every
integer unit square onto it, and the product torus is homeomorphic to the doughnut surface. -/
theorem Torus.cover_unitSquare_doughnutModel :
    (IsCoveringMap Torus.cover ∧ Function.Surjective Torus.cover) ∧
      (∀ n m : ℤ,
        Set.SurjOn Torus.cover
          (Set.Icc (n : ℝ) ((n : ℝ) + 1) ×ˢ Set.Icc (m : ℝ) ((m : ℝ) + 1)) Set.univ) ∧
      Nonempty (Torus ≃ₜ Torus.doughnutSurface) := by
  -- Combine the covering, square-surjectivity, and geometric-model results.
  constructor
  · exact Torus.cover_isCoveringMap
  · constructor
    · intro n m
      exact Torus.unitSquare_surjOn n m
    · exact ⟨Torus.doughnutHomeomorph⟩
