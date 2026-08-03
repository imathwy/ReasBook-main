module

public import Topology_Munkres_2000.Book.Example_52_1
public import Topology_Munkres_2000.Book.Exercise_54_7.Product
public import Topology_Munkres_2000.Book.Theorem_54_5.FundamentalGroup
public import Topology_Munkres_2000.Book.Theorem_59_3.Sphere

noncomputable section

public section

/-- Exercise 60.1 (1): The fundamental group of the solid torus `S¹ × B²` is infinite
cyclic. -/
def fundamentalGroup_circle_prod_closedBall
    (p : Circle × ClosedUnitBall 1) :
    FundamentalGroup (Circle × ClosedUnitBall 1) p ≃* Multiplicative ℤ :=
  (FundamentalGroup.prodMulEquivLeftOfSubsingleton p.1 p.2
      (Convex.subsingleton_fundamentalGroup (convex_closedBall 0 1) p.2)).trans
    ((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected p.1 1).trans
      Circle.fundamentalGroupEquivInt)

/-- Exercise 60.1 (2): The fundamental group of `S¹ × S²` is infinite cyclic. -/
def fundamentalGroup_circle_prod_twoSphere
    (p : Circle × StandardSphere 2) :
    FundamentalGroup (Circle × StandardSphere 2) p ≃* Multiplicative ℤ :=
  (FundamentalGroup.prodMulEquivLeftOfSubsingleton p.1 p.2 inferInstance).trans
    ((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected p.1 1).trans
      Circle.fundamentalGroupEquivInt)
