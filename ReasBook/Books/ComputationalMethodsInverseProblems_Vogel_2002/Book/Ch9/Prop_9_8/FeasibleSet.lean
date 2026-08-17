module

public import Mathlib.Analysis.Calculus.Gradient.Basic

public section

noncomputable section

namespace NonnegativeOrthant

variable {n : ℕ}

/-- The feasible set for problem `(9.16)` is the nonnegative orthant in
`EuclideanSpace ℝ (Fin n)`. -/
def feasibleSet (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  { f | ∀ i : Fin n, 0 ≤ f i }

@[simp] theorem mem_feasibleSet
    {f : EuclideanSpace ℝ (Fin n)} :
    f ∈ feasibleSet n ↔ ∀ i : Fin n, 0 ≤ f i :=
  Iff.rfl

end NonnegativeOrthant
