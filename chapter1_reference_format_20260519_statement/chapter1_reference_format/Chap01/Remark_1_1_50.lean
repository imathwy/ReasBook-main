import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Remark 1.1.50: since the ideal `0ℤ` is the zero ideal, the quotient `ℤ / 0ℤ` is canonically
identified with `ℤ`. -/
#check
  (((Ideal.quotEquivOfEq Ideal.span_singleton_zero).trans (RingEquiv.quotientBot ℤ)) :
    ℤ ⧸ Ideal.span ({(0 : ℤ)} : Set ℤ) ≃+* ℤ)

-- Proof sketch: rewrite the quotient by `Ideal.span {0}` as the quotient by `⊥`, then apply the
-- computation rule for `RingEquiv.quotientBot`.
/-- The canonical identification `ℤ / 0ℤ ≃+* ℤ` sends the class of `z` to `z`. -/
theorem int_quotient_zero_ideal_equiv_mk (z : ℤ) :
    ((Ideal.quotEquivOfEq Ideal.span_singleton_zero).trans (RingEquiv.quotientBot ℤ))
        (Ideal.Quotient.mk (Ideal.span ({(0 : ℤ)} : Set ℤ)) z) =
      z := by
  simp
