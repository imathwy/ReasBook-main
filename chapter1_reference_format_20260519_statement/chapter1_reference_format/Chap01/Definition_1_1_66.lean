import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 1.1.66: a natural number `p` is prime if it has no nontrivial divisors; in `ℕ`
this is the canonical predicate `Nat.Prime p`, equivalently `2 ≤ p` and every divisor of `p` is
either `1` or `p`. The informal `±1` and `±p` wording reduces to `1` and `p` for natural-number
divisors. -/
recall Nat.Prime (p : ℕ) : Prop
