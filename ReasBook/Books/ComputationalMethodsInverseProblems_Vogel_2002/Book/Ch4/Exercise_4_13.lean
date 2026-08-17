module

public import Book.Ch4.Prop_4_30

public section

/- Exercise 4.13.

This exercise is direct canonical reuse of the existing real-symmetric
trace-eigenvalue identity. The orthogonal eigendecomposition mentioned in the
text is a proof route, not part of the public statement surface for this item.
-/
#check Matrix.IsSymm.trace_eq_sum_eigenvalues
