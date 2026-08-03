module

public import Topology_Munkres_2000.Book.Exercise_52_7.LoopGroup

public section

/- Exercise 52.7 (a). Pointwise multiplication defines a group structure on loops
based at the identity of a topological group. -/
#check Path.pointwiseMul_apply
#check Path.instGroupIdentityLoop

/- Exercise 52.7 (b). Pointwise multiplication descends to a group operation on
`π₁(G, 1)`. -/
#check FundamentalGroup.pointwiseMul_mk
#check FundamentalGroup.pointwiseGroup

/- Exercise 52.7 (c). The descended pointwise operation agrees with the usual
concatenation product on `π₁(G, 1)`. -/
#check FundamentalGroup.pointwiseMul_eq_mul

/- Exercise 52.7 (d). The fundamental group of a topological group is abelian. -/
open scoped LoopPointwise

universe u

namespace FundamentalGroup

variable {G : Type u} [TopologicalSpace G] [Group G]

/-- Exercise 52.7 (d). The fundamental group of a topological group at its identity is abelian. -/
noncomputable instance instIsMulCommutativeTopologicalGroup [IsTopologicalGroup G] :
    IsMulCommutative (FundamentalGroup G 1) := by
  -- Eckmann–Hilton interchange reverses the factors after inserting ordinary units.
  refine IsMulCommutative.of_comm ?_
  intro a b
  have pointwiseOne_eq_one : pointwiseOne = (1 : FundamentalGroup G 1) := by
    calc
      pointwiseOne = pointwiseOne * 1 := (mul_one pointwiseOne).symm
      _ = pointwiseOne ⊗ 1 := (pointwiseMul_eq_mul pointwiseOne 1).symm
      _ = 1 := pointwiseOne_mul 1
  calc
    a * b = a ⊗ b := (pointwiseMul_eq_mul a b).symm
    _ = ((1 : FundamentalGroup G 1) * a) ⊗ (b * (1 : FundamentalGroup G 1)) := by
      rw [one_mul, mul_one]
    _ = ((1 : FundamentalGroup G 1) ⊗ b) * (a ⊗ (1 : FundamentalGroup G 1)) :=
      pointwiseMul_interchange 1 a b 1
    _ = b * a := by
      rw [← pointwiseOne_eq_one, pointwiseOne_mul, pointwiseMul_one]

end FundamentalGroup
