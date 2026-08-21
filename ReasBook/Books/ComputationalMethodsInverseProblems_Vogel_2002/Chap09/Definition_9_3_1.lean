module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Definition_9_3_1.BindingSet

public section

/-
Definition 9.3.4-extra-1. The binding set is formalized by
`NonnegativeOrthant.bindingSet J f`, the coordinate set
`{i | f i = 0 ∧ 0 < gradient J f i}`.
-/
#check NonnegativeOrthant.bindingSet
