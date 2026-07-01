import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- Proposition 1.1.115: the commutative ring `ZMod n` is a field exactly when `n` is prime. -/
-- Proof sketch: if `n` is prime, use the canonical field instance on `ZMod n` and transfer it to
-- `IsField`. Conversely, an `IsField` structure yields a `Field` structure on `ZMod n`, so the
-- finite unit group has cardinality `n - 1`; `Nat.prime_iff_card_units` then forces `n` to be
-- prime.
theorem zmod_isField_iff_prime (n : ℕ) :
    IsField (ZMod n) ↔ Nat.Prime n := by
  constructor
  · intro h
    by_cases hn : n = 0
    · subst hn
      exact False.elim <| Int.not_isField <| by simpa [ZMod] using h
    · letI : NeZero n := ⟨hn⟩
      letI : Field (ZMod n) := h.toField
      have hcard : Fintype.card (ZMod n)ˣ = n - 1 := by
        rw [Fintype.card_units, ZMod.card]
      exact (Nat.prime_iff_card_units n).2 hcard
  · intro hn
    letI : Fact n.Prime := ⟨hn⟩
    exact Field.toIsField (ZMod n)
