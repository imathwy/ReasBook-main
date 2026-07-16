import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 1.1.67: every positive natural number admits a unique factorization into
prime powers, encoded by a finitely supported exponent function on the primes.
Mathlib's canonical owner for this source-facing statement is the equivalence
`Nat.factorizationEquiv`. -/
recall Nat.factorizationEquiv :
    ℕ+ ≃ { f : ℕ →₀ ℕ // ∀ p ∈ f.support, Nat.Prime p }
