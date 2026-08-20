module

public import ComputationalMethodsInverseProblems_Vogel_2002.Book.Ch1.Remark_1_2_1

public section

/- Exercise 1.9 (1).

The right-hand side of `(1.27)` is minimized by the a priori choice `(1.28)`.
This exercise clause is already formalized by the imported Chapter 1 theorem
below, so the source-facing entry is direct canonical reuse.
-/

#check tsvdSourceCondition_aPrioriAlpha

/- Exercise 1.9 (2).

Substituting the a priori choice `(1.28)` into `(1.27)` yields the estimate
`(1.29)`. This exercise clause is already formalized by the imported Chapter 1
theorem below, so the source-facing entry is direct canonical reuse.
-/

#check tsvdSourceCondition_error_le_of_aPrioriAlpha
