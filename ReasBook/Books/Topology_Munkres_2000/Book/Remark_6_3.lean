module

import Mathlib.SetTheory.Cardinal.Finite

universe u

/- Remark 6.3: The proposed alternative explanation is precisely that one set
admits bijections with two finite sections of different sizes. -/
#check fun A : Type u ↦
  ∃ n m : ℕ, n ≠ m ∧ Nonempty (A ≃ Fin n) ∧ Nonempty (A ≃ Fin m)

/- The canonical finite cardinality associated to either bijection rules out this alternative. -/
#check Nat.card_eq_of_equiv_fin
