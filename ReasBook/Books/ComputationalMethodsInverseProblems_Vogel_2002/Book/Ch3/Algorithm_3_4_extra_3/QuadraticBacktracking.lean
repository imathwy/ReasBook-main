module

public import Mathlib.Analysis.Calculus.Deriv.Basic

public section

noncomputable section

namespace LineSearch

/-- The quadratic backtracking candidate determined by the source formula `(3.30)`. -/
@[expose] def quadraticBacktrackingStep (φ : ℝ → ℝ) (τ₀ : ℝ) : ℝ :=
  -(deriv φ 0) * τ₀ ^ 2 / (2 * (φ τ₀ - φ 0 - deriv φ 0 * τ₀))

/-- Expands `quadraticBacktrackingStep` into its closed-form expression. -/
theorem quadraticBacktrackingStep_def (φ : ℝ → ℝ) (τ₀ : ℝ) :
    quadraticBacktrackingStep φ τ₀ =
      -(deriv φ 0) * τ₀ ^ 2 / (2 * (φ τ₀ - φ 0 - deriv φ 0 * τ₀)) := rfl

end LineSearch
