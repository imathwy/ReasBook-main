import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 1.4.69: for every prime `p`, the `p`-adic complex field `ℂ_[p]` is algebraically
closed; this is the canonical mathlib instance `PadicComplex.isAlgClosed`. -/
recall PadicComplex.isAlgClosed (p : ℕ) [Fact (Nat.Prime p)] : IsAlgClosed ℂ_[p]
