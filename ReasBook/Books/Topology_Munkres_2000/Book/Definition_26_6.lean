module

public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Monotone.Basic

public section

universe u

variable {X : Type u}

/- Definition 26.6: A sequence `f : ℕ → X → ℝ` is monotone increasing when
`f n x ≤ f (n + 1) x` for every `n` and `x`. -/
#check (Monotone : (ℕ → X → ℝ) → Prop)

/-- A sequence of real-valued functions is monotone exactly when each term is pointwise at most
the next term. -/
theorem monotone_iff_le_succ_apply (f : ℕ → X → ℝ) :
    Monotone f ↔ ∀ n x, f n x ≤ f (n + 1) x := by
  constructor
  · intro hf n x
    exact hf (Nat.le_succ n) x
  · intro hf
    exact monotone_nat_of_le_succ fun n x ↦ hf n x
