module

public import Topology_Munkres_2000.Book.Exercise_4_1

public section

/- Exercise 4.2 (a): Strict inequalities are preserved when adding corresponding real terms. -/
#check (add_lt_add : ∀ {x y w z : ℝ}, y < x → z < w → y + z < x + w)

/- Exercise 4.2 (b), first statement: The sum of two positive real numbers is positive. -/
#check (add_pos : ∀ {x y : ℝ}, 0 < x → 0 < y → 0 < x + y)

/- Exercise 4.2 (b), second statement: The product of two positive real numbers is positive. -/
#check (mul_pos : ∀ {x y : ℝ}, 0 < x → 0 < y → 0 < x * y)

/- Exercise 4.2 (c): A real number is positive exactly when its negative is negative. -/
#check (neg_lt_zero : ∀ {x : ℝ}, -x < 0 ↔ 0 < x)

/- Exercise 4.2 (d): Negation reverses a strict inequality between real numbers. -/
#check (neg_lt_neg_iff : ∀ {x y : ℝ}, -x < -y ↔ y < x)

/- Exercise 4.2 (e): Multiplication by a negative real number reverses strict inequality. -/
#check (mul_lt_mul_of_neg_right :
  ∀ {x y z : ℝ}, y < x → z < 0 → x * z < y * z)

/- Exercise 4.2 (f): The square of a nonzero real number is positive. -/
#check (sq_pos_of_ne_zero : ∀ {x : ℝ}, x ≠ 0 → 0 < x ^ 2)

/- Exercise 4.2 (g), first inequality: Negative one is less than zero in `ℝ`. -/
#check (neg_one_lt_zero : -(1 : ℝ) < 0)

/- Exercise 4.2 (g), second inequality: Zero is less than one in `ℝ`. -/
#check (zero_lt_one : (0 : ℝ) < 1)

/- Exercise 4.2 (h): A real product is positive exactly when its factors have the same sign. -/
#check (mul_pos_iff :
  ∀ {x y : ℝ}, 0 < x * y ↔ (0 < x ∧ 0 < y) ∨ (x < 0 ∧ y < 0))

/- Exercise 4.2 (i): The reciprocal of a positive real number is positive. -/
#check (fun {x : ℝ} (hx : 0 < x) ↦ one_div_pos.mpr hx)

/- Exercise 4.2 (j): Taking reciprocals reverses strict inequality between positive reals. -/
#check (one_div_lt_one_div_of_lt : ∀ {x y : ℝ}, 0 < y → y < x → 1 / x < 1 / y)

/- Exercise 4.2 (k), first inequality: The midpoint of ordered reals is greater than the first. -/
#check (fun {x y : ℝ} (hxy : x < y) ↦ left_lt_add_div_two.mpr hxy)

/- Exercise 4.2 (k), second inequality: The midpoint of ordered reals is less than the second. -/
#check (fun {x y : ℝ} (hxy : x < y) ↦ add_div_two_lt_right.mpr hxy)
