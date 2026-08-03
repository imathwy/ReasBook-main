module

public import Mathlib.Data.Real.Basic

public section

/-- The vertical offset `y - x ^ 2` of a point from the standard parabola. -/
@[expose] def parabolaOffset (p : ℝ × ℝ) : ℝ :=
  p.2 - p.1 ^ 2

/-- The vertical offset evaluated at a point of the real plane. -/
@[simp]
theorem parabolaOffset_apply (p : ℝ × ℝ) :
    parabolaOffset p = p.2 - p.1 ^ 2 := rfl

/-- The vertical translate `y = x ^ 2 + c` of the standard parabola. -/
def parabolaTranslate (c : ℝ) : Set (ℝ × ℝ) :=
  parabolaOffset ⁻¹' {c}

/-- A point lies on the translate with offset `c` exactly when `y = x ^ 2 + c`. -/
@[simp]
theorem mem_parabolaTranslate (p : ℝ × ℝ) (c : ℝ) :
    p ∈ parabolaTranslate c ↔ p.2 = p.1 ^ 2 + c := by
  simp only [parabolaTranslate, Set.mem_preimage, Set.mem_singleton_iff, parabolaOffset_apply,
    sub_eq_iff_eq_add, add_comm]
