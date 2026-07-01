import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

section EulerFermat

/- Corollary 1.1.88 (1): if `p` is prime, then every integer `a` satisfies
`a ^ p ≡ a [ZMOD p]`. -/
recall Int.ModEq.pow_prime_eq_self {p : ℕ} (hp : Nat.Prime p) (a : ℤ) :
  a ^ p ≡ a [ZMOD p]

/- Corollary 1.1.88 (2): if `p` is prime and `a` is coprime to `p`, then
`a ^ (p - 1) ≡ 1 [ZMOD p]`. -/
recall Int.ModEq.pow_card_sub_one_eq_one {p : ℕ} (hp : Nat.Prime p) {a : ℤ}
    (ha : IsCoprime a p) : a ^ (p - 1) ≡ 1 [ZMOD p]

namespace Int.ModEq

/-- Corollary 1.1.88: if `a : ℤ` is coprime to `n`, then `a ^ φ(n) ≡ 1 [ZMOD n]`. -/
-- Proof sketch: view `a` as the unit `ZMod.unitOfIsCoprime a ha` of `(ZMod n)ˣ`, apply the
-- canonical theorem `ZMod.pow_totient`, and translate the resulting equality in `ZMod n` back to
-- `Int.ModEq` via `ZMod.intCast_eq_intCast_iff`.
theorem pow_totient {n : ℕ} {a : ℤ} (ha : IsCoprime a n) : a ^ Nat.totient n ≡ 1 [ZMOD n] := by
  rw [← ZMod.intCast_eq_intCast_iff]
  have h' : ((a : ZMod n) ^ Nat.totient n) = 1 := by
    simpa only [ZMod.coe_unitOfIsCoprime, Units.val_pow_eq_pow_val] using
      congrArg (fun x : (ZMod n)ˣ ↦ (x : ZMod n)) (ZMod.pow_totient (ZMod.unitOfIsCoprime a ha))
  simpa using h'

end Int.ModEq

end EulerFermat
