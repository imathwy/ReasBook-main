module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Notation_2_extra_2

public section

/- Exercise 2.6. Use Theorem 2.6 to derive the representation `(2.13)`-(2.15) for the best
approximation.

This exercise is realized by direct reuse of the existing Chapter 2 source-facing bridge theorems
for the coordinate/Gram-matrix representation and the orthonormal-basis representation.
-/
#check Submodule.bestApproximation_repr_solve_gram
#check Submodule.bestApproximation_eq_sum_inner_orthonormalBasis
