import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Proposition 1.1.71: there are infinitely many prime numbers; equivalently, the set of natural
numbers `p` such that `Nat.Prime p` is an infinite set. -/
recall Nat.infinite_setOf_prime : Set.Infinite {p : ℕ | Nat.Prime p}
