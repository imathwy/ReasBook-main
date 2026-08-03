module

public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.Prod.Lex

public section

/-- The lexicographically ordered set consisting of two copies of the positive integers. -/
abbrev TwoCopiesPNat := Fin 2 ×ₗ ℕ+

namespace TwoCopiesPNat

/-- The point `aₙ`, lying in the first copy of the positive integers. -/
def a (n : ℕ+) : TwoCopiesPNat :=
  toLex (0, n)

/-- The point `bₙ`, lying in the second copy of the positive integers. -/
def b (n : ℕ+) : TwoCopiesPNat :=
  toLex (1, n)

/-- The lexicographic coordinates of `a n`. -/
@[simp]
lemma a_apply (n : ℕ+) : ofLex (a n) = (0, n) := by
  apply ofLex_toLex

/-- The lexicographic coordinates of `b n`. -/
@[simp]
lemma b_apply (n : ℕ+) : ofLex (b n) = (1, n) := by
  apply ofLex_toLex

end TwoCopiesPNat
