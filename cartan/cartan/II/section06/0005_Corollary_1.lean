import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- Corollary 1: every holomorphic function on an open set `D` admits, near each point of `D`, a
primitive on some ball contained in `D`. -/
-- Proof sketch: use openness to choose a small ball around `z` contained in `D`; the restriction
-- of `f` to that ball is holomorphic, hence conservative there by the canonical owner theorem
-- `DifferentiableOn.isConservativeOn`, and Morera's disk exactness theorem
-- `Complex.IsConservativeOn.isExactOn_ball` turns that conservative owner on the ball into a
-- primitive there.
theorem holomorphic_has_local_primitive
    {D : Set ℂ} {f : ℂ → ℂ} (hD : IsOpen D) (hf : DifferentiableOn ℂ f D) {z : ℂ}
    (hz : z ∈ D) :
    ∃ r > 0, Metric.ball z r ⊆ D ∧ Complex.IsExactOn f (Metric.ball z r) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hD z hz
  have hball_diff : DifferentiableOn ℂ f (Metric.ball z r) := hf.mono hball
  have hconservative : Complex.IsConservativeOn f (Metric.ball z r) :=
    hball_diff.isConservativeOn
  exact ⟨r, hr, hball, hconservative.isExactOn_ball hball_diff.continuousOn⟩
