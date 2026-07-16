import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial

/-- Helper for Remark 1.3.37: membership in the explicit root set means being one of the three
even residue classes `0`, `2`, or `4` modulo `6`. -/
lemma mem_zero_two_four_iff (x : ZMod 6) :
    x ∈ ({0, 2, 4} : Finset (ZMod 6)) ↔ x = 0 ∨ x = 2 ∨ x = 4 := by
  -- Expand the explicit finset membership into the three concrete cases.
  simp only [Finset.mem_insert, Finset.mem_singleton]

/-- Helper for Remark 1.3.37: the coefficient `3` annihilates the three displayed roots in
`ZMod 6`. -/
lemma three_mul_eq_zero_of_mem_zero_two_four (x : ZMod 6)
    (hx : x ∈ ({0, 2, 4} : Finset (ZMod 6))) : (3 : ZMod 6) * x = 0 := by
  -- Reduce to the three explicit residues coming from the counterexample.
  rcases (mem_zero_two_four_iff x).mp hx with rfl | rfl | rfl
  all_goals native_decide

-- Proof sketch: evaluate `C 3 * X` at `0`, `2`, and `4` in `ZMod 6`, where each value is zero
-- because multiplication by `3` annihilates the even residue classes modulo `6`; then compute
-- that the finite set `{0, 2, 4}` has cardinality `3`.
/-- Remark 1.3.37: over the ring `ℤ/6ℤ`, the linear polynomial `3X` has the three roots `0`,
`2`, and `4`, so the field-case bound on the number of roots does not extend to arbitrary
coefficient rings. -/
theorem zmod6_linear_polynomial_has_three_specified_roots :
    ({0, 2, 4} : Finset (ZMod 6)).card = 3 ∧
      ∀ x ∈ ({0, 2, 4} : Finset (ZMod 6)), (C (3 : ZMod 6) * X).IsRoot x := by
  constructor
  -- Compute the size of the explicit three-element root set.
  · decide
  -- Rewrite `IsRoot` as a polynomial evaluation and invoke the annihilation helper.
  · intro x hx
    rw [Polynomial.IsRoot, eval_mul, eval_C, eval_X]
    exact three_mul_eq_zero_of_mem_zero_two_four x hx
