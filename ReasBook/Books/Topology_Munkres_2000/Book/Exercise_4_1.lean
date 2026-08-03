module

public import Topology_Munkres_2000.Book.Remark_1_7

public section

/- Exercise 4.1 (a): If `x + y = x` for real numbers, then `y = 0`. -/
#check (add_eq_left.mp : ∀ {x y : ℝ}, x + y = x → y = 0)

/- Exercise 4.1 (b): Zero multiplied by a real number is zero. -/
#check (zero_mul : ∀ x : ℝ, 0 * x = 0)

/- Exercise 4.1 (c): The additive inverse of zero is zero. -/
#check (neg_zero : -(0 : ℝ) = 0)

/- Exercise 4.1 (d): Taking the additive inverse twice returns the original real number. -/
#check (neg_neg : ∀ x : ℝ, -(-x) = x)

/- Exercise 4.1 (e): Negating either factor negates a real product. -/
#check (mul_neg : ∀ x y : ℝ, x * (-y) = -(x * y))
#check (fun x y : ℝ ↦ (neg_mul x y).symm)

/- Exercise 4.1 (f): Multiplication by `-1` gives the additive inverse. -/
#check (neg_one_mul : ∀ x : ℝ, (-1) * x = -x)

/- Exercise 4.1 (g): Multiplication distributes over subtraction for real numbers. -/
#check (mul_sub : ∀ x y z : ℝ, x * (y - z) = x * y - x * z)

/- Exercise 4.1 (h), first identity: The negative of a sum is the sum of the negatives. -/
#check (neg_add : ∀ x y : ℝ, -(x + y) = -x - y)

/-- Exercise 4.1 (h), second identity: The negative of a difference reverses its terms. -/
theorem neg_sub_real (x y : ℝ) : -(x - y) = -x + y := by
  rw [neg_sub, sub_eq_add_neg, add_comm]

/- Exercise 4.1 (i): A nonzero real factor may be cancelled from `x * y = x`. -/
#check (fun {x y : ℝ} (hx : x ≠ 0) (hxy : x * y = x) ↦ (mul_eq_left₀ hx).mp hxy)

/- Exercise 4.1 (j): A nonzero real number divided by itself is one. -/
#check (div_self : ∀ {x : ℝ}, x ≠ 0 → x / x = 1)

/- Exercise 4.1 (k): Dividing a real number by one leaves it unchanged. -/
#check (div_one : ∀ x : ℝ, x / 1 = x)

/- Exercise 4.1 (l): The product of two nonzero real numbers is nonzero. -/
#check (mul_ne_zero : ∀ {x y : ℝ}, x ≠ 0 → y ≠ 0 → x * y ≠ 0)

/- Exercise 4.1 (m): The product of two reciprocals is the reciprocal of the product. -/
#check (one_div_mul_one_div : ∀ y z : ℝ, (1 / y) * (1 / z) = 1 / (y * z))

/- Exercise 4.1 (n): Multiplication of real fractions multiplies numerators and denominators. -/
#check (div_mul_div_comm : ∀ x y w z : ℝ, (x / y) * (w / z) = (x * w) / (y * z))

/-- Exercise 4.1 (o): Addition of real fractions uses the common denominator `y * z`. -/
theorem div_add_div_real (x y w z : ℝ) (hy : y ≠ 0) (hz : z ≠ 0) :
    x / y + w / z = (x * z + w * y) / (y * z) := by
  simpa [mul_comm] using div_add_div x w hy hz

/- Exercise 4.1 (p): The reciprocal of a nonzero real number is nonzero. -/
#check (one_div_ne_zero : ∀ {x : ℝ}, x ≠ 0 → 1 / x ≠ 0)

/- Exercise 4.1 (q): Taking the reciprocal of a real fraction reverses its terms. -/
#check (one_div_div : ∀ w z : ℝ, 1 / (w / z) = z / w)

/- Exercise 4.1 (r): Dividing by a real fraction multiplies by its reciprocal. -/
#check (div_div_div_eq : ∀ x y w z : ℝ, (x / y) / (w / z) = (x * z) / (y * w))

/- Exercise 4.1 (s): A scalar factor may be moved outside a real quotient. -/
#check (mul_div_assoc : ∀ a x y : ℝ, (a * x) / y = a * (x / y))

/- Exercise 4.1 (t): Negating either part of a real quotient negates the quotient. -/
#check (neg_div : ∀ y x : ℝ, (-x) / y = -(x / y))
#check (div_neg : ∀ {y : ℝ} (x : ℝ), x / (-y) = -(x / y))
