module

public import Topology_Munkres_2000.Book.Definition_2_99_2.HomeomorphAction
public import Mathlib.Topology.Algebra.Group.Basic

public section

universe u

variable {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
variable (α : G)

/- Exercise 2.99.4 (1): Left multiplication by `α` is the self-homeomorphism
`Homeomorph.mulLeft α`, whose underlying function is `fun x ↦ α * x`. -/
#check Homeomorph.mulLeft α
#check Homeomorph.coe_mulLeft α

/- Exercise 2.99.4 (2): Right multiplication by `α` is the self-homeomorphism
`Homeomorph.mulRight α`, whose underlying function is `fun x ↦ x * α`. -/
#check Homeomorph.mulRight α
#check Homeomorph.coe_mulRight α

/-- Exercise 2.99.4 (3): Every topological group is homogeneous. -/
instance IsTopologicalGroup.instIsPretransitive :
    MulAction.IsPretransitive (G ≃ₜ G) G where
  exists_smul_eq x y := ⟨Homeomorph.mulLeft (y * x⁻¹), by simp⟩
