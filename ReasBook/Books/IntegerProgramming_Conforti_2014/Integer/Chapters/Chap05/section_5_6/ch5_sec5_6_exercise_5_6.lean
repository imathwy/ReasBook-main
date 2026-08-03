import Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_3
import Integer.Chapters.Chap05.section_5_1_5.ch5_sec5_1_5_definition_5_1_5_extra_1

open scoped IntegerVectorNotation Matrix

-- Semantic recall note: the mixed-space owner layer is already established in Chapter 4 via
-- `MixedRealPoint`, `mixed_integer_points`, and `mixed_linear_objective`, and the MIR owner is
-- already established in Chapter 5.1.5. This file therefore keeps only the source-facing
-- Exercise 5.6 set and reuses those canonical owners directly.

section Exercise56

variable {n p : ℕ}

/-- The mixed-integer set
`S = {(x, y) ∈ ℤ^n × ℝ^p | c x + g y ≤ b + α x_k, c x + g y ≤ b + β (1 - x_k)}`
from Exercise 5.6, embedded in `ℝ^n × ℝ^p`. -/
def exercise_5_6_set
    (c : Fin n → ℝ)
    (g : Fin p → ℝ)
    (b alpha beta : ℝ)
    (k : Fin n) : Set (MixedRealPoint n p) :=
  mixed_integer_points
    {xy | mixed_linear_objective c g xy ≤ b + alpha * xy.1 k ∧
      mixed_linear_objective c g xy ≤ b + beta * (1 - xy.1 k)}

/-- Membership in `exercise_5_6_set c g b alpha beta k` unfolds to integrality of the `x`
coordinates and the two defining linear inequalities. -/
theorem mem_exercise_5_6_set_iff
    (c : Fin n → ℝ)
    (g : Fin p → ℝ)
    (b alpha beta : ℝ)
    (k : Fin n)
    (xy : MixedRealPoint n p) :
    xy ∈ exercise_5_6_set c g b alpha beta k ↔
      xy.1 ∈ ℤ^n ∧
        mixed_linear_objective c g xy ≤ b + alpha * xy.1 k ∧
          mixed_linear_objective c g xy ≤ b + beta * (1 - xy.1 k) := by
  rw [exercise_5_6_set, mem_mixed_integer_points_iff, mem_mixed_integer_lattice_iff]
  simp [and_assoc, and_comm]

/-- The canonical flattened image of `exercise_5_6_set c g b alpha beta k` in `ℝ^(n + p)`,
used by the MIR owner `is_mixed_integer_rounding_inequality`. -/
def exercise_5_6_flat_set
    (c : Fin n → ℝ)
    (g : Fin p → ℝ)
    (b alpha beta : ℝ)
    (k : Fin n) : Set (Fin (n + p) → ℝ) :=
  (Fin.appendEquiv n p) '' exercise_5_6_set c g b alpha beta k

/-- Membership in `exercise_5_6_flat_set c g b alpha beta k` is equivalent to membership of the
unflattened point in the source-facing mixed-space set from Exercise 5.6. -/
theorem mem_exercise_5_6_flat_set_iff
    (c : Fin n → ℝ)
    (g : Fin p → ℝ)
    (b alpha beta : ℝ)
    (k : Fin n)
    (u : Fin (n + p) → ℝ) :
    u ∈ exercise_5_6_flat_set c g b alpha beta k ↔
      (Fin.appendEquiv n p).symm u ∈ exercise_5_6_set c g b alpha beta k := by
  constructor
  · rintro ⟨xy, hxy, rfl⟩
    simpa using hxy
  · intro hu
    refine ⟨(Fin.appendEquiv n p).symm u, hu, ?_⟩
    simpa using (Fin.appendEquiv n p).apply_symm_apply u

/-- Exercise 5.6. Let `c ∈ ℝ^n`, `g ∈ ℝ^p`, `b ∈ ℝ`, and
`S = {(x, y) ∈ ℤ^n × ℝ^p | c x + g y ≤ b + α x_k, c x + g y ≤ b + β (1 - x_k)}`
with `k : Fin n` encoding the source condition `1 ≤ k ≤ n` and `α, β > 0`. Then the inequality
`c x + g y ≤ b` is a mixed integer rounding inequality for `S`. -/
theorem exercise_5_6_cut_is_mixed_integer_rounding
    (c : Fin n → ℝ)
    (g : Fin p → ℝ)
    (b alpha beta : ℝ)
    (k : Fin n)
    (halpha : 0 < alpha)
    (hbeta : 0 < beta) :
    is_mixed_integer_rounding_inequality
      (Set.range (Fin.castAdd p))
      (exercise_5_6_flat_set c g b alpha beta k)
      (Fin.append c g)
      b := sorry

end Exercise56
