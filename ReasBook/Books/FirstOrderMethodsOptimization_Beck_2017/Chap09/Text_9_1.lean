import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Gradient

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Text 9.1 is `source-facing`, but its owner object is already the Chapter 9 declaration
`bregmanDistance` from Definition 9.2. This file is therefore a `bridge/view` specialization to
the textbook real-valued setting `ω : E → ℝ`, with primitive data only the function, the set, and
the strict-convexity/differentiability hypotheses. -/

/-- For a real-valued potential, the Chapter 9 Bregman distance specializes to the textbook
formula `ω(x) - ω(y) - ⟪∇ω(y), x - y⟫`. -/
@[simp] theorem bregmanDistance_apply_real (ω : E → ℝ) (x y : E) :
    B[ω] x y = ω x - ω y - inner ℝ (∇ ω y) (x - y) := by
  simp [bregmanDistance, Function.toEReal]

-- Proof sketch: apply the first-order lower support inequality for a differentiable convex
-- function at `y` to obtain `0 ≤ B[ω] x y`. If `x ≠ y`, strict convexity upgrades that support
-- inequality to a strict inequality, so `B[ω] x y > 0`. Combining this strict positivity with
-- the canonical diagonal identity `bregmanDistance_self_eq_zero` gives the equality
-- characterization. For this fixed pair `(x, y)`, only differentiability at the second argument
-- `y` is used.
/-- Text 9.1, specialized at a fixed pair `(x, y)`: if `ω` is strictly convex on `D` and
differentiable at `y ∈ D`, then the associated Bregman distance from `x` to `y` is nonnegative,
and it vanishes exactly on the diagonal. -/
theorem bregmanDistance_nonneg_and_eq_zero_iff
    (ω : E → ℝ) (D : Set E) (hω : StrictConvexOn ℝ D ω) {x y : E}
    (hx : x ∈ D) (hy : y ∈ D) (hy_diff : DifferentiableAt ℝ ω y) :
    0 ≤ B[ω] x y ∧ (B[ω] x y = 0 ↔ x = y) := sorry

end
