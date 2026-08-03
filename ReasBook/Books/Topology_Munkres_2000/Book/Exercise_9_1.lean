module

public import Topology_Munkres_2000.Book.Notation_4_2

public section

/-- Exercise 9.1: The choice-free embedding of the positive integers into binary sequences
that sends `n` to the sequence supported at `n.natPred`. Here `Fin 2` represents the
two-element set `X = {0, 1}`. -/
def positiveOneHot : ℕ+ ↪ (ℕ → Fin 2) where
  toFun n := Pi.single n.natPred 1
  inj' := by
    intro m n h
    have hmn := congrFun h m.natPred
    change Pi.single m.natPred 1 m.natPred = Pi.single n.natPred 1 m.natPred at hmn
    rw [Pi.single_eq_same] at hmn
    by_contra hne
    have hpred : m.natPred ≠ n.natPred := fun hpred ↦
      hne (PNat.natPred_injective hpred)
    rw [Pi.single_eq_of_ne hpred] at hmn
    exact Nat.one_ne_zero (Fin.mk.inj hmn)

/-- The binary sequence `positiveOneHot n` is `1` at coordinate `n.natPred`. -/
@[simp]
theorem positiveOneHot_self (n : ℕ+) : positiveOneHot n n.natPred = 1 := by
  exact Pi.single_eq_same _ _

/-- The binary sequence `positiveOneHot n` is `0` away from coordinate `n.natPred`. -/
@[simp]
theorem positiveOneHot_of_ne {n : ℕ+} {k : ℕ} (h : k ≠ n.natPred) :
    positiveOneHot n k = 0 := by
  exact Pi.single_eq_of_ne h _
