import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool `lean_leansearch` was not available in this environment; this statement
-- uses Mathlib's `convexHull ℝ` together with an explicit mixed-integer subset of `ℝ × ℝ`.

/-- Proposition 1.5. The convex hull of the mixed-integer set
`{(x, y) | x ∈ ℤ, y ≥ 0, x - y ≤ β}` is cut out by the original inequality, nonnegativity of
`y`, and the mixed-integer cut with `f = Int.fract β`. -/
theorem convexHull_mixed_integer_strip_eq
    (β : ℝ) :
    convexHull ℝ
        {p : ℝ × ℝ |
          p.1 ∈ Set.range (fun z : ℤ ↦ (z : ℝ)) ∧
            0 ≤ p.2 ∧
            p.1 - p.2 ≤ β} =
      {p : ℝ × ℝ |
        p.1 - p.2 ≤ β ∧
          p.1 - p.2 / (1 - Int.fract β) ≤ (⌊β⌋ : ℝ) ∧
          0 ≤ p.2} := sorry
