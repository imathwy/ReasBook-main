module

public import Book.Ch4.Exercise_4_7.Factorization

public section

/- Exercise 4.7. Equation `(4.11)` is the pointwise factorization of the joint
probability mass function for independent, jointly distributed, discrete random
variables:
`joint (x, y) = fstMarginal joint x * sndMarginal joint y`.

In the current repo, that statement is formalized exactly by
`ProbabilityTheory.JointPmf.apply_eq_mul_marginals_of_indepFun`.
-/
#check ProbabilityTheory.JointPmf.apply_eq_mul_marginals_of_indepFun
