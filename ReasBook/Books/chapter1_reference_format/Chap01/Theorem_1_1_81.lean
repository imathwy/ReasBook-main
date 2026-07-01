import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Proof sketch: rewrite solvability of the congruence by `Int.modEq_iff_dvd`,
-- let `d = Int.gcd a n`, use Bézout coefficients for `a` and `n`
-- to prove the divisibility criterion, and conversely divide
-- the congruence by `d` to reduce to the coprime case, where a modular inverse gives a solution.
/-- Helper for Theorem 1.1.81: any solution of the linear congruence forces the gcd
to divide the right-hand side. -/
lemma gcd_dvd_of_linear_congruence {a b : ℤ} {n : ℕ} :
    (∃ x : ℤ, a * x ≡ b [ZMOD n]) → (Int.gcd a n : ℤ) ∣ b := by
  rintro ⟨x, hx⟩
  -- Rewrite the congruence as divisibility of the difference by the modulus.
  have hdiff : (n : ℤ) ∣ b - a * x := Int.modEq_iff_dvd.mp hx
  have hdiff' : (Int.gcd a n : ℤ) ∣ b - a * x := dvd_trans (Int.gcd_dvd_right a n) hdiff
  have hax : (Int.gcd a n : ℤ) ∣ a * x := dvd_mul_of_dvd_left (Int.gcd_dvd_left a n) x
  -- Add the two divisible pieces to recover `b` itself.
  have hsum : (Int.gcd a n : ℤ) ∣ (b - a * x) + a * x := Int.dvd_add hdiff' hax
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum

/-- Helper for Theorem 1.1.81: scaling Bézout's identity gives the exact
difference needed for the converse direction. -/
lemma bezout_scaled_difference {a : ℤ} {n : ℕ} {c : ℤ} :
    (Int.gcd a n : ℤ) * c - a * (c * Int.gcdA a n) = (n : ℤ) * (c * Int.gcdB a n) := by
  -- Expand the gcd via Bézout coefficients and normalize the arithmetic.
  rw [Int.gcd_eq_gcd_ab a n]
  ring

/-- Helper for Theorem 1.1.81: divisibility by the gcd yields an explicit
solution of the linear congruence. -/
lemma exists_linear_congruence_of_gcd_dvd {a b : ℤ} {n : ℕ} :
    (Int.gcd a n : ℤ) ∣ b → ∃ x : ℤ, a * x ≡ b [ZMOD n] := by
  rintro ⟨c, rfl⟩
  -- Use the Bézout coefficient of `a` as the canonical witness.
  refine ⟨c * Int.gcdA a n, ?_⟩
  -- The resulting difference is an explicit multiple of `n`.
  apply Int.modEq_of_dvd
  rw [bezout_scaled_difference]
  exact dvd_mul_right (n : ℤ) (c * Int.gcdB a n)

/-- Theorem 1.1.81: for integers `a` and `b` and a natural modulus `n`, the linear congruence
`a * x ≡ b [ZMOD n]` is solvable if and only if `Int.gcd a n` divides `b`. -/
theorem linear_congruence_solvable_iff_gcd_dvd (a b : ℤ) (n : ℕ) :
    (∃ x : ℤ, a * x ≡ b [ZMOD n]) ↔ (Int.gcd a n : ℤ) ∣ b := by
  constructor
  · -- A solution forces the gcd divisibility condition.
    exact gcd_dvd_of_linear_congruence
  · -- Bézout's identity turns gcd divisibility into an explicit solution.
    exact exists_linear_congruence_of_gcd_dvd
