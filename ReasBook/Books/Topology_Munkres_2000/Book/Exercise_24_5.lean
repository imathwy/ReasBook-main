module

public import Topology_Munkres_2000.Book.Example_24_2
public import Topology_Munkres_2000.Book.Example_3_12
public import Topology_Munkres_2000.Book.Exercise_3_15
public import Mathlib.Data.PNat.Basic

public section

open Prod.Lex

/- Exercise 24.5 (1): The dictionary-ordered product
`ℕ+ ×ₗ Set.Ico (0 : ℝ) 1` is a linear continuum by `instLinearContinuumLexIco`. -/
#check (inferInstance : LinearContinuum (ℕ+ ×ₗ Set.Ico (0 : ℝ) 1))

/-- Exercise 24.5 (2): The dictionary-ordered product
`Set.Ico (0 : ℝ) 1 ×ₗ ℕ+` is not a linear continuum. -/
theorem halfOpenPnatLex_not_linearContinuum :
    ¬ LinearContinuum (Set.Ico (0 : ℝ) 1 ×ₗ ℕ+) := by
  -- Use zero in the first coordinate to exhibit an adjacent pair in one fiber.
  have hzero : (0 : ℝ) ∈ Set.Ico 0 1 := by
    norm_num
  let t : Set.Ico (0 : ℝ) 1 := ⟨0, hzero⟩
  intro h
  -- Density forbids the cover supplied by incrementing the positive-natural coordinate.
  have hNoCovers : ∀ a b : Set.Ico (0 : ℝ) 1 ×ₗ ℕ+, ¬ a ⋖ b :=
    denselyOrdered_iff_forall_not_covBy.mp h.toDenselyOrdered
  exact hNoCovers (toLex (t, 1)) (toLex (t, 1 + 1))
    (unitPnatLex_covBy_addOne t 1)

/-- Exercise 24.5 (3): The dictionary-ordered product
`Set.Ico (0 : ℝ) 1 ×ₗ Set.Icc (0 : ℝ) 1` is a linear continuum. -/
instance instLinearContinuumHalfOpenClosedLex :
    LinearContinuum (Set.Ico (0 : ℝ) 1 ×ₗ Set.Icc (0 : ℝ) 1) := by
  -- Assemble the existing least-upper-bound theorem with the inferred density instance.
  apply (LinearContinuum.iff _).mpr
  constructor
  · exact lexHalfOpenClosed_leastUpperBoundProperty
  · infer_instance

/-- Exercise 24.5 (4): The dictionary-ordered product
`Set.Icc (0 : ℝ) 1 ×ₗ Set.Ico (0 : ℝ) 1` is not a linear continuum. -/
theorem closedHalfOpenLex_not_linearContinuum :
    ¬ LinearContinuum (Set.Icc (0 : ℝ) 1 ×ₗ Set.Ico (0 : ℝ) 1) := by
  -- A linear continuum would supply the LUB property already known to fail here.
  intro h
  exact lexClosedHalfOpen_not_leastUpperBoundProperty h.leastUpperBoundProperty
