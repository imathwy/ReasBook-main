module

public import Topology_Munkres_2000.Book.Example_2_1

public section

namespace Real

/-- Part (1) of Exercise 4.10: If `0 ≤ h < 1`, then
`(x + h) ^ 2 ≤ x ^ 2 + h * (2 * x + 1)`, including the case `x > 0` in the
exercise. -/
theorem add_sq_le (x h : ℝ) (hh0 : 0 ≤ h) (hh1 : h < 1) :
    (x + h) ^ 2 ≤ x ^ 2 + h * (2 * x + 1) := by
  -- The bound `h < 1` controls the quadratic error term by the linear term.
  have hsq_le : h ^ 2 ≤ h := by
    nlinarith
  nlinarith

/-- Part (2) of Exercise 4.10: The estimate
`x ^ 2 - h * (2 * x) ≤ (x - h) ^ 2` holds for all real `x` and `h`, hence in
particular under the hypotheses in the exercise. -/
theorem sub_sq_ge (x h : ℝ) :
    x ^ 2 - h * (2 * x) ≤ (x - h) ^ 2 := by
  -- Expanding the square leaves the nonnegative remainder `h ^ 2`.
  nlinarith [sq_nonneg h]

/-- Part (3) of Exercise 4.10: If `x ^ 2 < a`, then some positive increment of `x` still
has square less than `a`, without needing the exercise's assumption `x > 0`. -/
theorem exists_pos_add_sq_lt {x a : ℝ} (hxa : x ^ 2 < a) :
    ∃ h : ℝ, 0 < h ∧ (x + h) ^ 2 < a := by
  -- First record positivity of the radicand, forced by the square inequality.
  have ha : 0 < a := by
    nlinarith [sq_nonneg x]
  by_cases hx : x < 0
  · -- Moving a negative `x` to zero gives an immediate positive increment.
    refine ⟨-x, ?_, ?_⟩
    · linarith
    · simpa using ha
  · -- For nonnegative `x`, move halfway toward the canonical square root.
    have hx0 : 0 ≤ x := le_of_not_gt hx
    have hx_sqrt : x < √a := Real.lt_sqrt_of_sq_lt hxa
    refine ⟨(√a - x) / 2, ?_, ?_⟩
    · linarith
    · have hmid0 : 0 ≤ x + (√a - x) / 2 := by
        nlinarith [Real.sqrt_nonneg a]
      have hmid_lt : x + (√a - x) / 2 < √a := by
        linarith
      exact (Real.lt_sqrt hmid0).1 hmid_lt

/-- Part (4) of Exercise 4.10: If `a < x ^ 2`, then some positive decrement of `x` still
has square greater than `a`, without needing the exercise's assumption `x > 0`. -/
theorem exists_pos_sub_sq_gt {x a : ℝ} (hax : a < x ^ 2) :
    ∃ h : ℝ, 0 < h ∧ a < (x - h) ^ 2 := by
  by_cases hx : x ≤ 0
  · -- Subtracting one from a nonpositive number strictly increases its square.
    have hone : (0 : ℝ) < 1 := by
      norm_num
    refine ⟨1, hone, ?_⟩
    nlinarith
  · -- For positive `x`, subtract a small fraction of the square excess.
    have hxpos : 0 < x := lt_of_not_ge hx
    have hxne : x ≠ 0 := ne_of_gt hxpos
    let h : ℝ := (x ^ 2 - a) / (4 * x)
    have hhpos : 0 < h := by
      dsimp [h]
      positivity
    have hnormalize : h * (2 * x) = (x ^ 2 - a) / 2 := by
      dsimp [h]
      field_simp [hxne]
      ring
    refine ⟨h, hhpos, ?_⟩
    have hlower := Real.sub_sq_ge x h
    nlinarith

/-- Part (5) of Exercise 4.10: The set of real numbers whose squares are less than `a` is
bounded above. -/
theorem bddAbove_sq_lt (a : ℝ) : BddAbove {x : ℝ | x ^ 2 < a} := by
  by_cases ha : a ≤ 0
  · -- If `a ≤ 0`, the strict square sublevel set is empty.
    refine ⟨0, ?_⟩
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    nlinarith [sq_nonneg x]
  · -- If `a > 0`, every member lies below `√a`.
    refine ⟨√a, ?_⟩
    intro x hx
    exact (Real.lt_sqrt_of_sq_lt hx).le

/-- Part (6) of Exercise 4.10: For `a > 0`, some positive real number has square less than
`a`. -/
theorem exists_pos_sq_lt {a : ℝ} (ha : 0 < a) :
    ∃ x : ℝ, 0 < x ∧ x ^ 2 < a := by
  -- Half of the positive square root is a positive strict sublevel point.
  have htwo : (0 : ℝ) < 2 := by
    norm_num
  refine ⟨√a / 2, ?_, ?_⟩
  · exact div_pos (Real.sqrt_pos.2 ha) htwo
  · nlinarith [Real.sq_sqrt ha.le]

/-- Part (7) of Exercise 4.10: For `a > 0`, the square of the supremum of the real numbers
whose squares are less than `a` is `a`. -/
theorem sq_sSup_sq_lt {a : ℝ} (ha : 0 < a) :
    (sSup {x : ℝ | x ^ 2 < a}) ^ 2 = a := by
  -- A positive member makes the supremum positive and supplies nonemptiness.
  obtain ⟨x, hxpos, hxmem⟩ := Real.exists_pos_sq_lt ha
  have hbdd : BddAbove {y : ℝ | y ^ 2 < a} := Real.bddAbove_sq_lt a
  have hxle : x ≤ sSup {y : ℝ | y ^ 2 < a} := le_csSup hbdd hxmem
  have hsup_pos : 0 < sSup {y : ℝ | y ^ 2 < a} := lt_of_lt_of_le hxpos hxle
  have hnonempty : ({y : ℝ | y ^ 2 < a} : Set ℝ).Nonempty := ⟨x, hxmem⟩
  -- The canonical square root is an upper bound, so the supremum's square is at most `a`.
  have hsup_le_sqrt : sSup {y : ℝ | y ^ 2 < a} ≤ √a := by
    refine csSup_le hnonempty ?_
    intro y hy
    exact (Real.lt_sqrt_of_sq_lt hy).le
  have hsq_le : (sSup {y : ℝ | y ^ 2 < a}) ^ 2 ≤ a :=
    (Real.le_sqrt hsup_pos.le ha.le).1 hsup_le_sqrt
  -- Strict inequality would permit a larger member, contradicting the supremum property.
  apply le_antisymm hsq_le
  by_contra hnot
  have hstrict : (sSup {y : ℝ | y ^ 2 < a}) ^ 2 < a := lt_of_not_ge hnot
  obtain ⟨h, hhpos, hhmem⟩ := Real.exists_pos_add_sq_lt hstrict
  have hadd_le : sSup {y : ℝ | y ^ 2 < a} + h ≤ sSup {y : ℝ | y ^ 2 < a} :=
    le_csSup hbdd hhmem
  linarith

/-- The supremum constructed in Exercise 4.10 is the canonical nonnegative square
root `√a`. -/
theorem sSup_sq_lt_eq_sqrt {a : ℝ} (ha : 0 < a) :
    sSup {x : ℝ | x ^ 2 < a} = √a := by
  -- Both quantities are nonnegative and have square `a`.
  obtain ⟨x, hxpos, hxmem⟩ := Real.exists_pos_sq_lt ha
  have hxle : x ≤ sSup {y : ℝ | y ^ 2 < a} :=
    le_csSup (Real.bddAbove_sq_lt a) hxmem
  have hsup0 : 0 ≤ sSup {y : ℝ | y ^ 2 < a} := by
    linarith
  nlinarith [Real.sq_sSup_sq_lt ha, Real.sq_sqrt ha.le, Real.sqrt_nonneg a]

/-- Part (8) of Exercise 4.10: Positive real numbers with equal squares are equal. -/
theorem eq_of_pos_of_sq_eq_sq {b c : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hsq : b ^ 2 = c ^ 2) : b = c := by
  -- The alternative factor `b + c` is positive, so equal squares force equality.
  nlinarith

/-- Exercise 4.10: Every positive real number has exactly one positive square
root. -/
theorem existsUnique_pos_sq_eq {a : ℝ} (ha : 0 < a) :
    ∃! b : ℝ, 0 < b ∧ b ^ 2 = a := by
  -- Use the canonical square root and the positive equal-squares criterion.
  refine ⟨√a, ?_, ?_⟩
  · exact ⟨Real.sqrt_pos.2 ha, Real.sq_sqrt ha.le⟩
  · intro y hy
    apply Real.eq_of_pos_of_sq_eq_sq hy.1 (Real.sqrt_pos.2 ha)
    rw [hy.2, Real.sq_sqrt ha.le]

end Real
