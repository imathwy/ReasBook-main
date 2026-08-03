module

public import Topology_Munkres_2000.Book.Definition_69_7.Presentation
public import Topology_Munkres_2000.Book.Exercise_54_7

public section

namespace TorusFundamentalGroup

/-- The standard loop class in the first circle factor of the torus. -/
noncomputable def alpha : FundamentalGroup (Circle × Circle) (1, 1) :=
  fundamentalGroup_circle_prod_circle.symm (Multiplicative.ofAdd 1, 1)

/-- The standard loop class in the second circle factor of the torus. -/
noncomputable def beta : FundamentalGroup (Circle × Circle) (1, 1) :=
  fundamentalGroup_circle_prod_circle.symm (1, Multiplicative.ofAdd 1)

/-- The standard pair of generators `α`, `β` for the fundamental group of the torus. -/
noncomputable def generator : Fin 2 → FundamentalGroup (Circle × Circle) (1, 1)
  | 0 => alpha
  | 1 => beta

/-- The commutator word `α * β * α⁻¹ * β⁻¹` defining the standard torus presentation. -/
def relator : FreeGroup (Fin 2) :=
  FreeGroup.of 0 * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹

/-- The presentation `⟨α, β | α * β * α⁻¹ * β⁻¹ = 1⟩` of the fundamental group
of the torus. -/
noncomputable def presentation :
    Group.Presentation (FundamentalGroup (Circle × Circle) (1, 1)) (Fin 2) Unit where
  generators := generator
  relators := fun _ ↦ relator
  generates := by sorry
  complete := by sorry

/-- The standard torus generators satisfy their defining commutator relation. -/
theorem relation : alpha * beta * alpha⁻¹ * beta⁻¹ = 1 := sorry

/-- The torus fundamental group is canonically equivalent to the group specified by its
standard presentation. -/
noncomputable def mulEquivPresentedGroup :
    FundamentalGroup (Circle × Circle) (1, 1) ≃*
      PresentedGroup (Set.range presentation.relators) :=
  presentation.mulEquivPresentedGroup

end TorusFundamentalGroup
