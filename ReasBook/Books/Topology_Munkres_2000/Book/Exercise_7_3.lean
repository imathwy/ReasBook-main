module

public import Topology_Munkres_2000.Book.Theorem_7_1

public section

/-- Exercise 7.3: The power set of the positive integers is equivalent to the
binary sequences indexed by the positive integers. -/
noncomputable def positiveIntegerSetsEquivBinarySequences :
    Set ℕ+ ≃ (ℕ+ → Fin 2) :=
  (Equiv.refl ℕ+).arrowCongr (Equiv.propEquivBool.trans finTwoEquiv.symm)

/-- Under `positiveIntegerSetsEquivBinarySequences`, membership is encoded by `1`. -/
@[simp]
theorem positiveIntegerSetsEquivBinarySequences_apply_eq_one_iff
    (A : Set ℕ+) (n : ℕ+) : positiveIntegerSetsEquivBinarySequences A n = 1 ↔ n ∈ A := by
  classical
  rw [show positiveIntegerSetsEquivBinarySequences A n =
    (Equiv.propEquivBool.trans finTwoEquiv.symm) (n ∈ A) by rfl]
  by_cases h : n ∈ A <;> simp [Equiv.propEquivBool, finTwoEquiv, h]
