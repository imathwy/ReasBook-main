import Mathlib

/- Remark I.1-extra-5: multiplying a monomial from the first formal power series by a monomial
from the second gives the corresponding monomial in the product. This is the canonical theorem
`PowerSeries.monomial_mul_monomial`. -/
recall PowerSeries.monomial_mul_monomial

/- Remark I.1-extra-5: the product of two formal power series is given coefficientwise by the
Cauchy product, so it is obtained by summing all pairwise products of a monomial from the first
series with a monomial from the second. -/
recall PowerSeries.coeff_mul
