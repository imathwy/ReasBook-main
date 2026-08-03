import BauschkeLean.Chap20.Example_20_19
import BauschkeLean.Chap20.Example_20_34
import BauschkeLean.Chap22.Definition_22_13

-- Declarations for this item will be appended below by the statement pipeline.

open scoped EuclideanSpace InnerProductSpace

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

-- Semantic recall: local Chapter 20 precedent provides `quarterTurnOperator`,
-- `quarterTurnOperator_isMonotone`, and the canonical bridge
-- `ContinuousLinearMap.toSetValuedOperator_isMaximallyMonotone_of_isMonotone`.
-- `lean_leansearch` did not surface a reusable mathlib owner for cyclic monotonicity; Chapter 22
-- already owns the source-facing `n`-cyclic-monotonicity API as
-- `SetValuedOperator.IsNCyclicallyMonotone`.

/-- Example 22.15 (1): the quarter-turn operator on `ℝ²` induced by the matrix
`[[0, -1], [1, 0]]` is maximally monotone when viewed as its associated singleton-valued
set-valued operator. -/
theorem quarterTurnOperator_isMaximallyMonotone :
    Maximal SetValuedOperator.IsMonotone quarterTurnOperator.toSetValuedOperator :=
  ContinuousLinearMap.toSetValuedOperator_isMaximallyMonotone_of_isMonotone
    quarterTurnOperator
    quarterTurnOperator_isMonotone

/-- Example 22.15 (2): the quarter-turn operator on `ℝ²` induced by the matrix
`[[0, -1], [1, 0]]` is not `3`-cyclically monotone, i.e. it fails the `n = 3`
specialization of Definition 22.13. -/
theorem quarterTurnOperator_not_isThreeCyclicallyMonotone :
    ¬ SetValuedOperator.IsNCyclicallyMonotone quarterTurnOperator.toSetValuedOperator 3 := by
  intro hA
  let x : ℕ → ℝ² := fun i ↦
    match i with
    | 0 | 3 => !₂[(1 : ℝ), 0]
    | 1 => !₂[(0 : ℝ), 1]
    | _ => !₂[(0 : ℝ), 0]
  have hineq :=
    hA.ineq
      x
      (fun i ↦ quarterTurnOperator (x i))
      (by
        intro i hi
        simp [Function.toSetValuedOperator_apply])
      (by simp [x])
  let term : ℕ → ℝ := fun i ↦ ⟪x (i + 1) - x i, quarterTurnOperator (x i)⟫_ℝ
  have h0 : term 0 = 1 := by
    simp [term, x, quarterTurnOperator_apply, PiLp.inner_apply, Fin.sum_univ_two]
  have h1 : term 1 = 0 := by
    simp [term, x, quarterTurnOperator_apply, PiLp.inner_apply, Fin.sum_univ_two]
  have h2 : term 2 = 0 := by
    simp [term, x, quarterTurnOperator_apply, PiLp.inner_apply, Fin.sum_univ_two]
  have hsum : Finset.sum (Finset.range 3) term = 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    simp [h0, h1, h2, term]
  have hbad : (1 : ℝ) ≤ 0 := by
    simpa [term, hsum] using hineq
  norm_num at hbad
