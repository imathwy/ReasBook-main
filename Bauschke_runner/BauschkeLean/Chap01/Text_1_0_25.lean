import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter

universe u v w

namespace Net

variable {X : Type u} {A : Type v} {B : Type w}

/-- Text 1.0.25: a net `y` is a subnet of a net `x` via `k` exactly when the textbook
reindexing-and-cofinality condition holds, equivalently when `y = x ∘ k` and `k` tends to
`atTop`. -/
theorem isSubnetOfVia_iff [Preorder A] [Preorder B] [IsDirectedOrder A] [IsDirectedOrder B]
    [Nonempty B] {x : A → X} {y : B → X} {k : B → A} :
    (y = x ∘ k ∧ ∀ a : A, ∃ d : B, ∀ b : B, d ≤ b → a ≤ k b) ↔
      y = x ∘ k ∧ Tendsto k atTop atTop := by
  rw [tendsto_atTop_atTop]

end Net
