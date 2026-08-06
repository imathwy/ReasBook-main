module

public import Mathlib.Data.List.Basic

public section

/-- A multiindex for an iterated Steenrod square operation. -/
abbrev SteenrodMultiIndex := List ℕ

namespace SteenrodMultiIndex

/-- An iterated Steenrod-square multiindex is admissible when each adjacent pair satisfies the
usual mod-`2` inequality `2 * i_{r+1} ≤ i_r`. -/
def Admissible : SteenrodMultiIndex → Prop
  | [] => True
  | [_] => True
  | i :: j :: I => 2 * j ≤ i ∧ Admissible (j :: I)

/-- The admissibility condition for a nontrivial multiindex is exactly the leading inequality
together with admissibility of the tail. -/
theorem admissible_cons_cons_iff (i j : ℕ) (I : SteenrodMultiIndex) :
    Admissible (i :: j :: I) ↔ 2 * j ≤ i ∧ Admissible (j :: I) :=
  Iff.rfl

/-- The excess of a Steenrod multiindex `I = (i₁, …, i_r)` is `i₁ - (i₂ + ··· + i_r)`. -/
def excess : SteenrodMultiIndex → ℕ
  | [] => 0
  | i :: I => i - I.sum

/-- The excess of a nonempty Steenrod multiindex is its leading term minus the sum of the tail. -/
theorem excess_cons (i : ℕ) (I : SteenrodMultiIndex) :
    excess (i :: I) = i - I.sum :=
  by simp [excess]

end SteenrodMultiIndex
