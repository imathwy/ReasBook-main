module

public import Book.Ch5.Exercise_5_15
public import Book.Ch5.Lemma_5_21
public import Book.Ch5.Remark_5_17

public section

/- Exercise 5.16. Prove Lemma 5.21.

This exercise is a check-only reuse surface: Lemma 5.21 is already formalized
in `Book.Ch5.Lemma_5_21` as
`Matrix.bestCirculantApproximation_eq_fourierDiagonalProjection`.

The textbook hint is also already exposed by the source-facing results
`Matrix.circulant_eq_fourierDiagonal_fft` and
`Matrix.frobenius_norm_mul_eq_of_mem_unitary`.
-/
#check Matrix.bestCirculantApproximation_eq_fourierDiagonalProjection

#check Matrix.circulant_eq_fourierDiagonal_fft

#check Matrix.frobenius_norm_mul_eq_of_mem_unitary
