module

public import Topology_Munkres_2000.Book.Definition_4_6
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

public section

namespace Real

/-- The positive power `aⁿ`, defined recursively for positive integers by
`a¹ = a` and `aⁿ⁺¹ = aⁿ * a`. -/
@[expose] def positivePow (a : ℝ) (n : ℕ+) : ℝ :=
  PNat.recOn n a (fun _ x ↦ x * a)

scoped instance instHPowPNat : HPow ℝ ℕ+ ℝ := ⟨positivePow⟩

@[simp]
theorem positivePow_one (a : ℝ) : a ^ (1 : ℕ+) = a :=
  rfl

@[simp]
theorem positivePow_succ (a : ℝ) (n : ℕ+) :
    a ^ (n + 1) = a ^ n * a := by
  exact PNat.recOn_succ n a (fun _ x ↦ x * a)

/-- Positive-integer exponentiation agrees with the canonical natural power. -/
theorem positivePow_eq_pow (a : ℝ) (n : ℕ+) :
    a ^ n = a ^ (n : ℕ) := by
  induction n using PNat.recOn with
  | one => simp
  | succ n ih => simp [ih, pow_succ]

/-- Real exponentiation at a positive integer agrees with positive-integer exponentiation. -/
@[simp]
theorem rpow_pnatCast (a : ℝ) (n : ℕ+) :
    a ^ ((n : ℕ) : ℝ) = a ^ n := by
  rw [rpow_natCast, positivePow_eq_pow]

end Real
