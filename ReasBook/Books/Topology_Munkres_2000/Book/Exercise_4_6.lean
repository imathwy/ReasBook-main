module

public import Topology_Munkres_2000.Book.Exercise_4_6.PositivePowers

public section

open scoped Real

/-- Exercise 4.6 (1): Positive powers with the same base multiply by adding
their exponents. -/
theorem realPowAddPositive (a : ℝ) (n m : ℕ+) :
    a ^ n * a ^ m = a ^ (n + m) := by
  simp only [Real.positivePow_eq_pow, PNat.add_coe, pow_add]

/-- Exercise 4.6 (2): Iterating positive powers multiplies their exponents. -/
theorem realPowMulPositive (a : ℝ) (n m : ℕ+) :
    (a ^ n) ^ m = a ^ (n * m) := by
  simp only [Real.positivePow_eq_pow, PNat.mul_coe, pow_mul]

/-- Exercise 4.6 (3): A positive power of a product is the product of the
positive powers. -/
theorem realMulPowPositive (a b : ℝ) (m : ℕ+) :
    a ^ m * b ^ m = (a * b) ^ m := by
  simp only [Real.positivePow_eq_pow]
  exact (mul_pow a b m).symm
