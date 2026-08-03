module

public import Topology_Munkres_2000.Book.Exercise_54_7.Product
public import Topology_Munkres_2000.Book.Theorem_54_5.FundamentalGroup

public section

/-- Exercise 54.7: The fundamental group of the torus `Circle × Circle` at the
standard basepoint `(1, 1)` is isomorphic to
`Multiplicative ℤ × Multiplicative ℤ`. -/
noncomputable def fundamentalGroup_circle_prod_circle :
    FundamentalGroup (Circle × Circle) (1, 1) ≃* Multiplicative ℤ × Multiplicative ℤ :=
  (FundamentalGroup.prodMulEquiv 1 1).trans
    (Circle.fundamentalGroupEquivInt.prodCongr Circle.fundamentalGroupEquivInt)

/-- The torus isomorphism records the integer classes of the two projected loops. -/
@[simp]
theorem fundamentalGroup_circle_prod_circle_apply
    (p : FundamentalGroup (Circle × Circle) (1, 1)) :
    fundamentalGroup_circle_prod_circle p =
      (Circle.fundamentalGroupEquivInt (Path.Homotopic.projLeft p),
        Circle.fundamentalGroupEquivInt (Path.Homotopic.projRight p)) := by
  rfl
