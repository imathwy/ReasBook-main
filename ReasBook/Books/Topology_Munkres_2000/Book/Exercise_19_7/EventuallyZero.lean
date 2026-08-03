module

public import Mathlib.Algebra.FiniteSupport.Defs
public import Mathlib.Data.Real.Basic

public section

/-- The set of real sequences whose nonzero support is finite. -/
def eventuallyZeroRealSequences : Set (ℕ → ℝ) :=
  {x | x.HasFiniteSupport}

/-- Membership in `eventuallyZeroRealSequences` is finite support. -/
theorem mem_eventuallyZeroRealSequences {x : ℕ → ℝ} :
    x ∈ eventuallyZeroRealSequences ↔ x.HasFiniteSupport := by
  rfl
