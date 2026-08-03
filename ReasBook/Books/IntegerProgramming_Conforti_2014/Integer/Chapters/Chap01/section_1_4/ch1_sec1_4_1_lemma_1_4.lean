import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool `lean_leansearch` was not available in this environment; this statement
-- uses Mathlib's `Int.fract β` for the fractional part `β - ⌊β⌋`.

/-- Lemma 1.4. For an integer `x` and a nonnegative real `y` satisfying `x - y ≤ β`, the mixed-
integer cut `x - y / (1 - Int.fract β) ≤ ⌊β⌋` is valid. -/
theorem mixed_integer_strip_cut_valid
    (β : ℝ) {x : ℤ} {y : ℝ}
    (hy : 0 ≤ y)
    (hxy : (x : ℝ) - y ≤ β) :
    (x : ℝ) - y / (1 - Int.fract β) ≤ (⌊β⌋ : ℝ) := sorry
