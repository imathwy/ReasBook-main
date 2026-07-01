import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u

/-- The scalar `{0, 1}`-valued indicator of the nonzero locus, expressed via the canonical set
indicator. -/
noncomputable def l0Indicator (y : ℝ) : ℝ :=
  ({0} : Set ℝ)ᶜ.indicator (fun _ ↦ (1 : ℝ)) y

-- Proof sketch: unfold `l0Indicator`; since `0 ∉ ({0} : Set ℝ)ᶜ`, the indicator takes the value
-- `0` at the origin.
/-- The scalar `ℓ₀` indicator vanishes at the origin. -/
@[simp] theorem l0Indicator_zero :
    l0Indicator 0 = 0 := by
  simp [l0Indicator]

-- Proof sketch: unfold `l0Indicator`; when `y ≠ 0`, the point lies in `({0} : Set ℝ)ᶜ`, so the
-- indicator takes the constant branch value `1`.
/-- Away from the origin, the scalar `ℓ₀` indicator is `1`. -/
@[simp] theorem l0Indicator_of_ne_zero {y : ℝ} (hy : y ≠ 0) :
    l0Indicator y = 1 := by
  simp [l0Indicator, hy]

section

-- Proof sketch: unfold `l0Indicator`; if `a < 0`, neither branch can satisfy
-- `l0Indicator y ≤ a`, since both possible values `0` and `1` are nonnegative.
/-- The sublevel set of `l0Indicator` is empty below `0`. -/
theorem l0Indicator_sublevelSet_of_lt_zero {a : ℝ} (ha : a < 0) :
    l0Indicator ⁻¹' Set.Iic a = ∅ := sorry

-- Proof sketch: unfold `l0Indicator`; for `0 ≤ a < 1`, the inequality
-- `l0Indicator y ≤ a` holds exactly when the branch value is `0`, i.e. exactly when `y = 0`.
/-- Between `0` and `1`, the sublevel set of `l0Indicator` is the singleton `{0}`. -/
theorem l0Indicator_sublevelSet_of_nonneg_of_lt_one {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    l0Indicator ⁻¹' Set.Iic a = ({0} : Set ℝ) := sorry

-- Proof sketch: unfold `l0Indicator`; both possible values `0` and `1` are bounded above by any
-- `a ≥ 1`, so every real number lies in the sublevel set.
/-- Once the level is at least `1`, the sublevel set of `l0Indicator` is all of `ℝ`. -/
theorem l0Indicator_sublevelSet_of_one_le {a : ℝ} (ha : 1 ≤ a) :
    l0Indicator ⁻¹' Set.Iic a = Set.univ := sorry

-- Proof sketch: apply `lowerSemicontinuous_iff_isClosed_preimage`; the previous three lemmas give
-- an explicit description of every sublevel set, and each resulting set is closed in `ℝ`.
/-- The scalar indicator entering the `ℓ₀` example is closed, i.e. lower semicontinuous. -/
theorem l0Indicator_lowerSemicontinuous :
    LowerSemicontinuous l0Indicator := sorry

section

variable {ι : Type u} [Fintype ι]

-- Proof sketch: `hammingNorm x` is the canonical owner object for the number of nonzero
-- coordinates of `x`, while each term `l0Indicator (x i)` contributes `1` exactly when `x i ≠ 0`
-- and `0` otherwise; compare the resulting finite sum with `(hammingNorm x : ℝ)`.
/-- The `ℓ₀` count is the finite sum of the scalar nonzero indicators of the coordinates. -/
theorem hammingNorm_eq_sum_l0Indicator (x : ι → ℝ) :
    (hammingNorm x : ℝ) = ∑ i, l0Indicator (x i) := sorry

-- Proof sketch: rewrite the real-valued `ℓ₀` count using `hammingNorm_eq_sum_l0Indicator`; for
-- each coordinate `i`, the map `x ↦ l0Indicator (x i)` is lower semicontinuous by composing
-- `l0Indicator_lowerSemicontinuous` with the continuous evaluation map `x ↦ x i`, and then apply
-- `lowerSemicontinuous_sum`.
/-- Example 2.4: the `ℓ₀` function on a finite real coordinate space is closed, equivalently
lower semicontinuous, because it is the finite sum of the coordinatewise nonzero indicator. -/
theorem hammingNorm_lowerSemicontinuous :
    LowerSemicontinuous (fun x : ι → ℝ ↦ (hammingNorm x : ℝ)) := sorry

end

end
