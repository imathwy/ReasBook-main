module

public import ComputationalMethodsInverseProblems_Vogel_2002.Book.Ch9.Definition_9_3.LICQ

public section

/-
Definition 9.3. For a feasible point `f` of `(9.9)`, the linear independence
constraint qualification at the source-facing textbook layer is formalized by
`ConstraintQualification.IsRegularPoint c f`, which expands to
`ConstraintQualification.SatisfiesLICQ c (ActiveSet.active c) f`. The core owner
`ConstraintQualification.SatisfiesLICQ c active f` remains available for a
general active-index selector `active`.
-/
#check ConstraintQualification.IsRegularPoint

/-
Companion checks for the generalized LICQ owner and the source-facing bridge to
the active-set formulation.
-/
#check ConstraintQualification.SatisfiesLICQ
#check ConstraintQualification.isRegularPoint_iff_satisfiesLICQ
