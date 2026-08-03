module

public import Topology_Munkres_2000.Book.Example_2_2.RealFunctions

public section

/-- Example 2.2 (1). The composite `fiveMul ∘ shiftedQuadratic` is the function
`x ↦ 5 * (3 * x ^ 2 + 2)`. -/
theorem fiveMulCompQuadratic :
    fiveMul ∘ shiftedQuadratic = fun x ↦ 5 * (3 * x ^ 2 + 2) := by
  rfl

/-- Example 2.2 (2). The composite `shiftedQuadratic ∘ fiveMul` is the function
`x ↦ 3 * (5 * x) ^ 2 + 2`. -/
theorem quadraticCompFiveMul :
    shiftedQuadratic ∘ fiveMul = fun x ↦ 3 * (5 * x) ^ 2 + 2 := by
  rfl

/-- Example 2.2 (3). The composites of `shiftedQuadratic` and `fiveMul` in the
two possible orders are different functions. -/
theorem fiveMulQuadraticComp_ne :
    fiveMul ∘ shiftedQuadratic ≠ shiftedQuadratic ∘ fiveMul := by
  intro h
  have h_zero := congrFun h 0
  norm_num [fiveMul, shiftedQuadratic] at h_zero
