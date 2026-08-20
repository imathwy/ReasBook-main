module

public import ComputationalMethodsInverseProblems_Vogel_2002.Book.Ch5.Notation_5_2_2

public section

/- Exercise 5.10. Verify the equalities in `(5.40)`.

This exercise is a check-only reuse surface: the two source-facing inverse
2D scaled DFT equalities from `(5.40)` are already formalized in
`Book.Ch5.Notation_5_2_2` as `Matrix.ifft2_def` and `Matrix.ifft2_apply`.
-/

#check Matrix.ifft2_def
#check Matrix.ifft2_apply

end
