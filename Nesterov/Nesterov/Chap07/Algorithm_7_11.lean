import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {α : Type u} [Monoid α]

/-- Algorithm 7.11: the repeated-squaring recursion attached to an input `A`, with
initial values `X₀ = A` and `Y₀ = 1` and updates
`X_{i+1} = X_i^2`, `Y_{i+1} = Y_i X_i`. -/
def repeatedSquaringOutputs (A : α) : ℕ → α × α
  | 0 => (A, 1)
  | k + 1 =>
      let outputs := repeatedSquaringOutputs A k
      (outputs.1 * outputs.1, outputs.2 * outputs.1)

/-- The first output `X_k` of the repeated-squaring recursion. -/
def repeatedSquaringX (A : α) (k : ℕ) : α :=
  (repeatedSquaringOutputs A k).1

/-- The second output `Y_k` of the repeated-squaring recursion. -/
def repeatedSquaringY (A : α) (k : ℕ) : α :=
  (repeatedSquaringOutputs A k).2

-- Proof sketch: prove by induction on `k`. The recursive step multiplies the previous first
-- component by itself and multiplies the previous second component by the previous first
-- component, so the exponents double and then add as in the textbook induction.
/-- The repeated-squaring recursion returns the pair
`(X_k, Y_k) = (A^(2^k), A^(2^k - 1))`; equivalently, for `p = 2^k` it outputs
`A^p` and `A^(p - 1)`. -/
theorem repeatedSquaringOutputs_eq_powers (A : α) (k : ℕ) :
    repeatedSquaringOutputs A k = (A ^ (2 ^ k), A ^ (2 ^ k - 1)) := sorry

-- Proof sketch: apply `Prod.fst` to `repeatedSquaringOutputs_eq_powers`.
/-- The first output of the repeated-squaring recursion is `A^(2^k)`. -/
theorem repeatedSquaringX_eq_pow (A : α) (k : ℕ) :
    repeatedSquaringX A k = A ^ (2 ^ k) := sorry

-- Proof sketch: apply `Prod.snd` to `repeatedSquaringOutputs_eq_powers`.
/-- The second output of the repeated-squaring recursion is `A^(2^k - 1)`. -/
theorem repeatedSquaringY_eq_pow_pred (A : α) (k : ℕ) :
    repeatedSquaringY A k = A ^ (2 ^ k - 1) := sorry

end
