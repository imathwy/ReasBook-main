module

public import ComputationalMethodsInverseProblems_Vogel_2002.Book.Ch1.Exercise_1_11.Operator
public import ComputationalMethodsInverseProblems_Vogel_2002.Book.Ch1.Exercise_1_11.Regularity

public section

/-
The current source item is blocked in this repository snapshot.

`Book/Ch1/Remark_1_1.lean` identifies source equation `(1.1)` with
`Fredholm1D.operator_apply`, while `Book/Ch1/Exercise_1_11/Operator.lean`
currently provides only the Gaussian specialization
`Fredholm1D.gaussianBlurL2_realizesOperator` together with the bundled adjoint
fact `Fredholm1D.gaussianBlurL2_adjoint_eq`.

A source-faithful statement here requires either a bundled `L²(0, 1)` owner
with adjoint API for the general operator `Fredholm1D.operator`, or a verified
local theorem identifying the exercise's `(1.1)` itself with
`Fredholm1D.gaussianBlurL2`.
-/
