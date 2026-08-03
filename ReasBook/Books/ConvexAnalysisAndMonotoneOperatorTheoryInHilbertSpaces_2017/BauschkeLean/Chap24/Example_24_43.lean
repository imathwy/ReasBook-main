import BauschkeLean.Chap12.ProximityOperator

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

namespace ERealFunction

-- Semantic recall: `lean_leansearch` only returned unrelated complex-analytic "proximity"
-- lemmas, so the owner/API choice here is verified directly against
-- `Chap12/Definition_12_23.lean` and `Chap12/ProximityOperator.lean`.

/-- The `]-∞,+∞]`-valued function from equation `(24.80)`, equal to
`-sqrt (1 - ξ^2) - ξ^2 / 2` on `[-1,1]` and to `+∞` outside that interval. -/
def unitIntervalSqrtQuadratic : ℝ → Set.Ioi (⊥ : EReal) :=
  ι[Set.Icc (-1 : ℝ) 1] +
    (fun ξ : ℝ ↦ -(Real.sqrt (1 - ξ ^ 2)) - ξ ^ 2 / 2).toEReal

/-- On the source interval `[-1,1]`, `unitIntervalSqrtQuadratic` agrees with the real branch from
equation `(24.80)`. -/
@[simp] theorem unitIntervalSqrtQuadratic_apply_of_mem_Icc {ξ : ℝ}
    (hξ : ξ ∈ Set.Icc (-1 : ℝ) 1) :
    (unitIntervalSqrtQuadratic ξ : EReal) =
      (-(Real.sqrt (1 - ξ ^ 2)) - ξ ^ 2 / 2 : ℝ) := by
  simp [unitIntervalSqrtQuadratic, hξ]

/-- Outside `[-1,1]`, `unitIntervalSqrtQuadratic` takes the value `+∞`. -/
@[simp] theorem unitIntervalSqrtQuadratic_apply_of_not_mem_Icc {ξ : ℝ}
    (hξ : ξ ∉ Set.Icc (-1 : ℝ) 1) :
    (unitIntervalSqrtQuadratic ξ : EReal) = ⊤ := by
  rw [unitIntervalSqrtQuadratic]
  have hbranch_ne_bot :
      (-((Real.sqrt (1 - ξ ^ 2) : ℝ) : EReal) - ((ξ ^ 2 / 2 : ℝ) : EReal)) ≠ ⊥ := by
    simpa only [sub_eq_add_neg, EReal.coe_add, EReal.coe_neg] using
      (EReal.coe_ne_bot (-(Real.sqrt (1 - ξ ^ 2)) - ξ ^ 2 / 2 : ℝ))
  have hindicator :
      ((ι[Set.Icc (-1 : ℝ) 1] ξ : Set.Ioi (⊥ : EReal)) : EReal) = ⊤ := by
    simp [indicator_apply, hξ]
  rw [add_apply, hindicator, Function.toEReal_apply]
  exact EReal.top_add_of_ne_bot hbranch_ne_bot

/-- A companion statement for Example 24.43: the function in `(24.80)` belongs to `Γ₀(ℝ)`. -/
theorem unitIntervalSqrtQuadratic_mem_gammaZero :
    unitIntervalSqrtQuadratic ∈ Γ₀(ℝ) := sorry

/-- Example 24.43: for every real `ξ`, the proximity operator of the function in `(24.80)` is
`ξ / sqrt (1 + ξ^2)`. -/
theorem prox_unitIntervalSqrtQuadratic_eq (ξ : ℝ) :
    Prox[unitIntervalSqrtQuadratic, unitIntervalSqrtQuadratic_mem_gammaZero] ξ =
      ξ / Real.sqrt (1 + ξ ^ 2) := sorry

end ERealFunction
