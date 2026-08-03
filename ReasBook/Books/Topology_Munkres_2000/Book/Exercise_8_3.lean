module

public import Topology_Munkres_2000.Book.Exercise_8_2
public import Mathlib.Data.Nat.Factorial.Basic

public section

/-- Exercise 8.3 (1): Natural powers are the positive partial products of a
constant real sequence. -/
theorem positivePartialProduct_const (a : ℝ) (n : ℕ+) :
    positivePartialProduct (fun _ ↦ a) n = a ^ (n : ℕ) := by
  induction n using PNat.recOn with
  | one => simp [positivePartialProduct_one]
  | succ n ih =>
      rw [positivePartialProduct_succ, ih]
      simp [pow_succ]

/-- Exercise 8.3 (2): The factorial of a positive natural number is the
positive partial product of the positive integers, viewed in `ℝ`. -/
theorem positivePartialProduct_natCast (n : ℕ+) :
    positivePartialProduct (fun k ↦ (k : ℝ)) n = ((n : ℕ).factorial : ℝ) := by
  induction n using PNat.recOn with
  | one => simp [positivePartialProduct_one]
  | succ n ih =>
      rw [positivePartialProduct_succ, ih]
      simp [PNat.add_one, Nat.succPNat_coe, Nat.factorial, mul_comm]
