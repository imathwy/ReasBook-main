import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

section PrimeModulusQuotientRing

variable (n : ℕ)

/- The quotient ring `ℤ/nℤ`, formalized as `ZMod n`, carries its canonical commutative ring
structure for every modulus `n`. -/
recall ZMod.commRing (n : ℕ) : CommRing (ZMod n)

variable [Fact (Nat.Prime n)]

/- Remark 1.1.83: if `n` is prime, then the quotient ring `ℤ/nℤ`, formalized as `ZMod n`, has its
canonical commutative ring structure and has no zero divisors; in Lean, the prime-modulus content
is the standard instance `ZMod.instIsDomain`. -/
recall ZMod.instIsDomain (n : ℕ) [Fact (Nat.Prime n)] : IsDomain (ZMod n)

end PrimeModulusQuotientRing
