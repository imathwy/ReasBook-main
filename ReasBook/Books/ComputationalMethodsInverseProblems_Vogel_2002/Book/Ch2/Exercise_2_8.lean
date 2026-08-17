module

public import Book.Ch2.Example_2_12

public section

/- Exercise 2.8. The source asks to show that the diagonal operator `D` from
Example 2.8 is a compact operator on `ℓ²(ℝ)`.

This is already formalized in Chapter 2 by the existing theorem
`RealL2.harmonicDiagonal_isCompactOperator`, whose operator is exactly the
diagonal operator from Example 2.8. -/

#check RealL2.harmonicDiagonal_isCompactOperator
