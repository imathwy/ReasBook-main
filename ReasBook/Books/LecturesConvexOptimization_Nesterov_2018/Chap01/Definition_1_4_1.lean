import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 1.4.1 is a source-facing recall in the order-theoretic monotonicity domain.

Layer targeted by this refinement:
* source-facing recall of the core/canonical owner predicate `Antitone`

Sampled owner-style declarations:
* `Antitone`, the owner notion of a decreasing sequence on a preorder
* `antitone_nat_of_succ_le`, the canonical `ℕ` constructor from the one-step decrease condition

Primitive data:
* the antitonicity condition `Antitone a`

Derived API:
* the textbook successor-step criterion `∀ k, a (k + 1) ≤ a k`, obtained by evaluating
  `Antitone a` on `Nat.le_succ` and conversely rebuilding `Antitone a` with
  `antitone_nat_of_succ_le`

This file therefore introduces no parallel wrapper API for relaxation sequences.
-/

#check (Antitone : (ℕ → ℝ) → Prop)
#check antitone_nat_of_succ_le

/-- On `ℕ`, the owner predicate `Antitone` is equivalent to the textbook one-step decrease
criterion. -/
theorem antitone_nat_iff_succ_le {α : Type*} [Preorder α] {f : ℕ → α} :
    Antitone f ↔ ∀ n : ℕ, f (n + 1) ≤ f n := by
  exact ⟨fun hf n ↦ hf (Nat.le_succ n), antitone_nat_of_succ_le⟩
