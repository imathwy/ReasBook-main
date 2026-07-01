import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Exercise 12 (1): The complex cosine function is analytic on the whole complex plane. -/
recall Complex.analyticOnNhd_cos

/- Exercise 12 (2): On the real axis, the complex cosine restricts to the real cosine, so it is
the analytic extension of `Real.cos`. -/
recall Complex.ofReal_cos

/- Exercise 12 (3): The complex sine function is analytic on the whole complex plane. -/
recall Complex.analyticOnNhd_sin

/- Exercise 12 (4): On the real axis, the complex sine restricts to the real sine, so it is the
analytic extension of `Real.sin`. -/
recall Complex.ofReal_sin

/- Exercise 12 (5): The complex cosine satisfies the addition formula
`cos (z + z') = cos z * cos z' - sin z * sin z'`. -/
recall Complex.cos_add

/- Exercise 12 (6): The complex sine satisfies the addition formula
`sin (z + z') = sin z * cos z' + cos z * sin z'`. -/
recall Complex.sin_add

/- Exercise 12 (7): The complex trigonometric functions satisfy `cos z ^ 2 + sin z ^ 2 = 1`. -/
recall Complex.cos_sq_add_sin_sq
