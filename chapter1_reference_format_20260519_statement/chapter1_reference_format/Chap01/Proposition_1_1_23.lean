import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Proposition 1.1.23: the order relation `≤` on `ℤ` is a total order relation, i.e. the
chapter's canonical relation-level predicate `IsLinearOrder`. -/
#check (inferInstance : IsLinearOrder ℤ (· ≤ ·))

/- The standard embedding `ℕ ↪o ℤ` is the canonical order-theoretic extension of the
natural-number order to the integers. -/
#check (Nat.castOrderEmbedding : ℕ ↪o ℤ)

/- Companion pointwise formulation: the standard embedding preserves and reflects `≤`. -/
#check Int.ofNat_le
