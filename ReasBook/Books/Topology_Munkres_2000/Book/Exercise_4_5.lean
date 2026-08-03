module

import Mathlib.Data.PNat.Basic

/- Exercise 4.5 (a): The sum of two positive integers is a positive integer. -/
#check fun (a b : ℕ+) ↦ a + b

/- Exercise 4.5 (b): The product of two positive integers is a positive integer. -/
#check fun (a b : ℕ+) ↦ a * b

/- Exercise 4.5 (c): Subtracting one from a positive integer gives a natural number;
here `ℕ` represents the positive integers together with zero. -/
#check fun (a : ℕ+) ↦ a.natPred

/- Exercise 4.5 (d), first statement: The sum of two integers is an integer. -/
#check fun (c d : ℤ) ↦ c + d

/- Exercise 4.5 (d), second statement: The difference of two integers is an integer. -/
#check fun (c d : ℤ) ↦ c - d

/- Exercise 4.5 (e): The product of two integers is an integer. -/
#check fun (c d : ℤ) ↦ c * d
