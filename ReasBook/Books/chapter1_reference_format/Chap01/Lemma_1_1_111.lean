import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 1.1.111: the canonical order relation `≤` on `ℚ` is a total order relation. -/
#check (inferInstance : IsLinearOrder ℚ (· ≤ ·))

/- The standard embedding `ι_ℚ : ℤ → ℚ`, implemented by the integer cast, preserves and reflects
the order relation `≤`; in particular, the rational order extends the integer order. -/
#check (Int.cast_le : ∀ {m n : ℤ}, ((m : ℚ) ≤ (n : ℚ)) ↔ m ≤ n)
