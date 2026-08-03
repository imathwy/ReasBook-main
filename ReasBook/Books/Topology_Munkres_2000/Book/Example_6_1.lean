module

public import Topology_Munkres_2000.Book.Notation_6_1
public import Mathlib.Data.PNat.Interval

public section

namespace PNat

/-- The positive-integer interval `{1,…,n}` has cardinality `n`. -/
theorem card_fintype_Iic (n : ℕ+) : Fintype.card {1,…,n} = n := by
  calc
    Fintype.card {1,…,n} = Fintype.card (Set.Icc (⊥ : ℕ+) n) :=
      Fintype.card_congr (Equiv.setCongr Set.Icc_bot.symm)
    _ = (n : ℕ) + 1 - ((⊥ : ℕ+) : ℕ) := card_fintype_Icc (⊥ : ℕ+) n
    _ = n := by
      change (n : ℕ) + 1 - 1 = n
      exact Nat.add_sub_cancel (n : ℕ) 1

end PNat

/- Example 6.1. The section `{1,…,n}` is in bijective correspondence with
itself under the identity equivalence and has cardinality `n`. -/
#check fun n : ℕ+ ↦ Equiv.refl {1,…,n}
#check PNat.card_fintype_Iic

end
