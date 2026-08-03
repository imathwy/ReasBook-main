module

public import Topology_Munkres_2000.Book.Definition_53_4.Torus
public import Topology_Munkres_2000.Book.Theorem_53_1.CircleMap
public import Topology_Munkres_2000.Book.Theorem_53_3.Product

public section

open Function Set

namespace Torus

/-- The coordinatewise one-turn exponential from the plane to the product torus. -/
noncomputable def cover : ℝ × ℝ → Torus :=
  Prod.map Circle.turnExp Circle.turnExp

/-- The coordinatewise circle exponential is a covering map of the torus by the plane. -/
theorem isCoveringMap_cover : IsCoveringMap cover :=
  Circle.isCoveringMap_turnExp.prodMap Circle.isCoveringMap_turnExp

/-- The coordinatewise circle exponential is surjective. -/
theorem cover_surjective : Surjective cover :=
  Circle.turnExp_surjective.prodMap Circle.turnExp_surjective

/-- The coordinatewise circle exponential is a covering map in Munkres' surjective sense. -/
theorem cover_isCoveringMap : IsCoveringMap cover ∧ Surjective cover :=
  ⟨isCoveringMap_cover, cover_surjective⟩

/-- Every integer unit square maps onto the whole torus. -/
theorem unitSquare_surjOn (n m : ℤ) :
    SurjOn cover (Icc (n : ℝ) ((n : ℝ) + 1) ×ˢ Icc (m : ℝ) ((m : ℝ) + 1)) univ := by
  -- Take the product of the two one-period interval surjections.
  simpa only [cover, SurjOn, Prod.map_apply', univ_prod_univ] using
    (Circle.surjOn_Icc_int_turnExp n).prodMap (Circle.surjOn_Icc_int_turnExp m)

end Torus
