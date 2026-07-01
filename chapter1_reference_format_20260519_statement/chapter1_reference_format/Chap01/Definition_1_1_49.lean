import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 1.1.49: congruence modulo an integer is the standard relation `Int.ModEq`; for a
natural modulus `n`, the notation `x ≡ y [ZMOD n]` expresses that `x` and `y` are congruent
modulo `n`. -/
recall Int.ModEq (n a b : ℤ) : Prop

/-- Congruence modulo a natural number is equivalent to the canonical difference `y - x` lying in
the additive subgroup `nℤ`, represented in Lean by `AddSubgroup.zmultiples (n : ℤ)`. -/
-- Proof sketch: rewrite congruence by `Int.modEq_iff_dvd` and identify membership in
-- `AddSubgroup.zmultiples (n : ℤ)` with divisibility via `Int.mem_zmultiples_iff`.
theorem modEq_nat_iff_sub_mem_zmultiples {n : ℕ} {x y : ℤ} :
    x ≡ y [ZMOD n] ↔ y - x ∈ AddSubgroup.zmultiples (n : ℤ) := by
  simpa [Int.mem_zmultiples_iff] using
    (Int.modEq_iff_dvd : x ≡ y [ZMOD (n : ℤ)] ↔ (n : ℤ) ∣ y - x)
