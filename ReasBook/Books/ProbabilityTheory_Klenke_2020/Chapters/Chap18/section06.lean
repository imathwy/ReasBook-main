import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_18_6 (from Items/Chap18) -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]

local instance : DecidableEq E := Classical.decEq E

/-- Example 18.6: the independent coalescent transition matrix on `E × E`; away from the diagonal
the two coordinates evolve independently with transition matrix `p`, and once the two coordinates
meet they move together along the diagonal. -/
def independentCoalescentMatrix (p : E → E → ℝ≥0∞) : (E × E) → (E × E) → ℝ≥0∞
  | (x₁, y₁), (x₂, y₂) =>
      if x₁ = y₁ then
        if x₂ = y₂ then p x₁ x₂ else 0
      else
        p x₁ x₂ * p y₁ y₂

-- Proof sketch: unfold `independentCoalescentMatrix`; when the starting coordinates are distinct,
-- the definition immediately reduces to the product of the two one-step transition probabilities.
/-- Off the diagonal, the independent coalescent uses the product transition law of two
independent copies of the chain with transition matrix `p`. -/
theorem independentCoalescentMatrix_apply_of_ne
    (p : E → E → ℝ≥0∞) {x₁ y₁ x₂ y₂ : E} (h : x₁ ≠ y₁) :
    independentCoalescentMatrix p (x₁, y₁) (x₂, y₂) = p x₁ x₂ * p y₁ y₂ := sorry

-- Proof sketch: unfold `independentCoalescentMatrix`; on the diagonal the outer `if` uses
-- `x = x`, and the inner `if` reduces the diagonal-to-diagonal transition to `p x z`.
/-- Once the two coordinates have coalesced at `x`, a diagonal transition to `(z, z)` has
probability `p x z`. -/
theorem independentCoalescentMatrix_apply_diag
    (p : E → E → ℝ≥0∞) (x z : E) :
    independentCoalescentMatrix p (x, x) (z, z) = p x z := sorry

-- Proof sketch: unfold `independentCoalescentMatrix`; on the diagonal the inner `if` forces every
-- transition to a non-diagonal state to have probability `0`.
/-- Once the two coordinates have coalesced, the independent coalescent cannot leave the diagonal.
-/
theorem independentCoalescentMatrix_apply_diag_of_ne
    (p : E → E → ℝ≥0∞) {x x₂ y₂ : E} (h : x₂ ≠ y₂) :
    independentCoalescentMatrix p (x, x) (x₂, y₂) = 0 := sorry

-- Proof sketch: split the row indexed by `(x, y)` into the off-diagonal case `x ≠ y`, where the
-- row sum factors as the product of two stochastic row sums, and the diagonal case `x = y`, where
-- only the diagonal states `(z, z)` contribute and the row sum is the single stochastic row sum
-- of `p`.
/-- The independent coalescent matrix is stochastic whenever `p` is stochastic. -/
theorem independentCoalescentMatrix_isStochasticMatrix
    (p : E → E → ℝ≥0∞) (hp : IsStochasticMatrix p) :
    IsStochasticMatrix (independentCoalescentMatrix p) := sorry

end ProbabilityTheory
