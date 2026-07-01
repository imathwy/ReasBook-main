import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- Proposition 1.1.40: For any integer `a` and positive natural number `b`, there is a unique
pair `(q, r)` with `a = bq + r` and `0 ≤ r ≤ b - 1`; equivalently, the remainder satisfies
`r < b`. We package the bounded remainder canonically as an element of `Fin b`. -/
-- Proof sketch: use the canonical equivalence `Int.divModEquiv b : ℤ ≃ ℤ × Fin b`, whose inverse
-- sends `(q, r)` to `b * q + r`. Existence is `symm_apply_apply`, and uniqueness follows by
-- applying `Int.divModEquiv b` to any competing decomposition.
theorem existsUnique_int_quotient_remainder (a : ℤ) (b : ℕ) (hb : 0 < b) :
    ∃! qr : ℤ × Fin b, a = b * qr.1 + qr.2 := by
  letI : NeZero b := ⟨Nat.ne_of_gt hb⟩
  refine ⟨Int.divModEquiv b a, ?_, ?_⟩
  · simpa [Int.divModEquiv_symm_apply, mul_comm] using
      ((Int.divModEquiv b).left_inv a).symm
  · intro qr hqr
    refine (Int.divModEquiv b).symm.injective ?_
    calc
      (Int.divModEquiv b).symm qr = b * qr.1 + qr.2 := by
        simp [Int.divModEquiv_symm_apply, mul_comm]
      _ = a := hqr.symm
      _ = (Int.divModEquiv b).symm (Int.divModEquiv b a) := by
        simpa using ((Int.divModEquiv b).left_inv a).symm
