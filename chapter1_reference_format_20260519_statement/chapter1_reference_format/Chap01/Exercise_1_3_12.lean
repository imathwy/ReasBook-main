import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial

universe u

noncomputable section

section PolynomialGcd

attribute [local instance] Classical.decEq

/-- Helper for Exercise 1.3.12: subtracting the Euclidean remainder polynomial from `X^m - 1`
produces a multiple of `X^n - 1`. -/
lemma pow_sub_one_sub_dvd {K : Type u} [Field K] (m n : ℕ) :
    (X ^ n - 1 : K[X]) ∣ (X ^ m - 1 : K[X]) - (X ^ (m % n) - 1 : K[X]) := by
  -- Rewrite the difference so the standard divisibility `X^n - 1 ∣ X^(n * q) - 1`
  -- factors out on the left.
  rw [sub_sub_sub_cancel_right]
  by_cases hn : n = 0
  · simp [hn]
  · have hd : (X ^ n - 1 : K[X]) ∣ (X ^ (n * (m / n)) - 1 : K[X]) := by
      exact dvd_pow_sub_one_of_dvd (r := (X : K[X]))
        (show n ∣ n * (m / n) by exact dvd_mul_of_dvd_left (dvd_refl n) _)
    have hdiff : (X ^ m - X ^ (m % n) : K[X]) = (X ^ (n * (m / n)) - 1) * X ^ (m % n) := by
      -- This is the polynomial translation of `m = n * (m / n) + (m % n)`.
      calc
        (X ^ m - X ^ (m % n) : K[X])
            = X ^ (n * (m / n) + m % n) - X ^ (m % n) := by rw [Nat.div_add_mod m n]
        _ = X ^ (n * (m / n)) * X ^ (m % n) - 1 * X ^ (m % n) := by rw [pow_add, one_mul]
        _ = (X ^ (n * (m / n)) - 1) * X ^ (m % n) := by rw [sub_mul]
    rw [hdiff]
    exact dvd_mul_of_dvd_left hd _

-- Proof sketch: factor `X^a - 1` and `X^b - 1` into cyclotomic factors; the common
-- factors are exactly those indexed by divisors of both `a` and `b`, namely the
-- divisors of `Nat.gcd a b`.
/-- Exercise 1.3.12 (1): over a field, the greatest common divisor of `X^a - 1`
and `X^b - 1` is `X^(gcd(a,b)) - 1`. -/
theorem gcd_X_pow_sub_one_eq_X_pow_gcd_sub_one {K : Type u} [Field K] (a b : ℕ) :
    gcd (X ^ a - 1 : K[X]) (X ^ b - 1) = (X ^ Nat.gcd a b - 1 : K[X]) := by
  revert a
  refine Nat.strong_induction_on b ?_
  intro b ih a
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    · -- The base case is just `gcd(f, 0) = f`, and `X^a - 1` is already normalized.
      simpa using (show gcd (X ^ a - 1 : K[X]) 0 = (X ^ a - 1 : K[X]) by
        rw [gcd_zero_right]
        exact Polynomial.Monic.normalize_eq_self (by
          simpa using
            (monic_X_pow_sub_C (R := K) (1 : K) (show a ≠ 0 by exact Nat.ne_of_gt ha))))
  · -- Follow the Euclidean algorithm on the exponents via the polynomial difference lemma.
    rw [gcd_eq_of_dvd_sub_left (pow_sub_one_sub_dvd a b), gcd_comm]
    rw [ih (a % b) (Nat.mod_lt _ hb) b]
    rw [Nat.gcd_comm b (a % b), ← Nat.gcd_rec, Nat.gcd_comm]

end PolynomialGcd

section PolynomialCongruenceSystem

variable {K : Type u} [CommRing K] [Invertible (2 : K)]

/-- The explicit odd degree-`< 6` polynomial appearing in Exercise 1.3.12 (2), written over the
canonical `⅟2` layer. -/
def exercise_1_3_12_interpolationPolynomial (K : Type u) [CommRing K] [Invertible (2 : K)] : K[X] :=
  C ((⅟2 : K) ^ 3) * (C (3 : K) * X ^ 5 - C (10 : K) * X ^ 3 + C (15 : K) * X)

/-- Helper for Exercise 1.3.12: the scalar `((⅟2)^3)` sends `8` to `1`. -/
lemma invOf_two_cube_mul_eight : (8 : K) * (⅟ (2 : K)) ^ 3 = 1 := by
  -- Collapse the cubic power to the basic inverse relation `2 * ⅟2 = 1`.
  calc
    (8 : K) * (⅟ (2 : K)) ^ 3 = ((2 : K) * ⅟ (2 : K)) ^ 3 := by ring
    _ = 1 := by simp

section ShiftedFactorizations

variable {K : Type u} [CommRing K]

/-- Helper for Exercise 1.3.12: the quintic numerator shifted by `X ↦ X + 1` has an `X^3`
factor. -/
lemma shifted_quintic_sub_eight_factor :
    (C (3 : K) * (X + 1) ^ 5 - C (10 : K) * (X + 1) ^ 3 + C (15 : K) * (X + 1) - C (8 : K) :
      K[X]) =
      X ^ 3 * (C (3 : K) * X ^ 2 + C (15 : K) * X + C (20 : K)) := by
  -- Prove the integer polynomial identity once, then transport it to `K[X]`.
  have h :
      (3 * (X + 1) ^ 5 - 10 * (X + 1) ^ 3 + 15 * (X + 1) - 8 : ℤ[X]) =
        X ^ 3 * (3 * X ^ 2 + 15 * X + 20) := by
    ring_nf
  simpa using congrArg (Polynomial.map (Int.castRingHom K)) h

/-- Helper for Exercise 1.3.12: the quintic numerator shifted by `X ↦ X - 1` has an `X^3`
factor. -/
lemma shifted_quintic_add_eight_factor :
    (C (3 : K) * (X - 1) ^ 5 - C (10 : K) * (X - 1) ^ 3 + C (15 : K) * (X - 1) + C (8 : K) :
      K[X]) =
      X ^ 3 * (C (3 : K) * X ^ 2 - C (15 : K) * X + C (20 : K)) := by
  -- The same transport argument handles the symmetric shift at `-1`.
  have h :
      (3 * (X - 1) ^ 5 - 10 * (X - 1) ^ 3 + 15 * (X - 1) + 8 : ℤ[X]) =
        X ^ 3 * (3 * X ^ 2 - 15 * X + 20) := by
    ring_nf
  simpa using congrArg (Polynomial.map (Int.castRingHom K)) h

end ShiftedFactorizations

/-- Helper for Exercise 1.3.12: after shifting by `X ↦ X + 1`, the polynomial
`exercise_1_3_12_interpolationPolynomial K - 1` becomes an explicit multiple of `X^3`. -/
lemma interpolationPolynomial_sub_one_shifted :
    (exercise_1_3_12_interpolationPolynomial K - 1).comp (X + 1) =
      C ((⅟2 : K) ^ 3) * X ^ 3 * (C (3 : K) * X ^ 2 + C (15 : K) * X + C (20 : K)) := by
  have hC8 : (1 : K[X]) = C ((⅟2 : K) ^ 3) * C (8 : K) := by
    rw [← C_mul, mul_comm, invOf_two_cube_mul_eight, C_1]
  -- Rewrite the constant term using the same scalar, then pull the shift through the product.
  calc
    (exercise_1_3_12_interpolationPolynomial K - 1).comp (X + 1)
        =
          (C ((⅟2 : K) ^ 3) *
              (C (3 : K) * X ^ 5 - C (10 : K) * X ^ 3 + C (15 : K) * X) -
            C ((⅟2 : K) ^ 3) * C (8 : K)).comp (X + 1) := by
              rw [exercise_1_3_12_interpolationPolynomial, hC8]
    _ =
        C ((⅟2 : K) ^ 3) *
          (C (3 : K) * (X + 1) ^ 5 - C (10 : K) * (X + 1) ^ 3 + C (15 : K) * (X + 1) -
            C (8 : K)) := by
              simp [sub_eq_add_neg, mul_add]
    _ =
        C ((⅟2 : K) ^ 3) *
          (X ^ 3 * (C (3 : K) * X ^ 2 + C (15 : K) * X + C (20 : K))) := by
            rw [shifted_quintic_sub_eight_factor]
    _ = C ((⅟2 : K) ^ 3) * X ^ 3 * (C (3 : K) * X ^ 2 + C (15 : K) * X + C (20 : K)) := by
          rw [mul_assoc]

/-- Helper for Exercise 1.3.12: after shifting by `X ↦ X - 1`, the polynomial
`exercise_1_3_12_interpolationPolynomial K + 1` becomes an explicit multiple of `X^3`. -/
lemma interpolationPolynomial_add_one_shifted :
    (exercise_1_3_12_interpolationPolynomial K + 1).comp (X - 1) =
      C ((⅟2 : K) ^ 3) * X ^ 3 * (C (3 : K) * X ^ 2 - C (15 : K) * X + C (20 : K)) := by
  have hC8 : (1 : K[X]) = C ((⅟2 : K) ^ 3) * C (8 : K) := by
    rw [← C_mul, mul_comm, invOf_two_cube_mul_eight, C_1]
  -- The same shifted-factor argument handles the congruence at `X = -1`.
  calc
    (exercise_1_3_12_interpolationPolynomial K + 1).comp (X - 1)
        =
          (C ((⅟2 : K) ^ 3) *
              (C (3 : K) * X ^ 5 - C (10 : K) * X ^ 3 + C (15 : K) * X) +
            C ((⅟2 : K) ^ 3) * C (8 : K)).comp (X - 1) := by
              rw [exercise_1_3_12_interpolationPolynomial, hC8]
    _ =
        C ((⅟2 : K) ^ 3) *
          (C (3 : K) * (X - 1) ^ 5 - C (10 : K) * (X - 1) ^ 3 + C (15 : K) * (X - 1) +
            C (8 : K)) := by
              simp [sub_eq_add_neg, mul_add]
    _ =
        C ((⅟2 : K) ^ 3) *
          (X ^ 3 * (C (3 : K) * X ^ 2 - C (15 : K) * X + C (20 : K))) := by
            rw [shifted_quintic_add_eight_factor]
    _ = C ((⅟2 : K) ^ 3) * X ^ 3 * (C (3 : K) * X ^ 2 - C (15 : K) * X + C (20 : K)) := by
          rw [mul_assoc]

/-- Helper for Exercise 1.3.12: the two cubic moduli at `1` and `-1` are coprime. -/
lemma isCoprime_X_sub_one_cube_X_add_one_cube :
    IsCoprime ((X - 1 : K[X]) ^ 3) ((X + 1 : K[X]) ^ 3) := by
  -- Reduce to the linear factors, using that `1 - (-1) = 2` is a unit.
  have hbase : IsCoprime (X - C (1 : K)) (X - C (-1 : K)) := by
    refine Polynomial.isCoprime_X_sub_C_of_isUnit_sub ?_
    simpa [sub_eq_add_neg, one_add_one_eq_two] using (isUnit_of_invertible (2 : K))
  simpa [sub_eq_add_neg] using hbase.pow

-- Proof sketch: expand the explicit formula and compare Taylor expansions at `X = 1`
-- and `X = -1` up to order `2`, which is equivalent to divisibility by the
-- corresponding cubic powers.
/-- Over a commutative ring in which `2` is invertible, this interpolation polynomial satisfies
the required simultaneous congruences modulo `(X - 1)^3` and `(X + 1)^3`. -/
theorem exercise_1_3_12_interpolationPolynomial_spec
    (K : Type u) [CommRing K] [Invertible (2 : K)] :
    ((X - 1 : K[X]) ^ 3 ∣ exercise_1_3_12_interpolationPolynomial K - 1) ∧
      ((X + 1 : K[X]) ^ 3 ∣ exercise_1_3_12_interpolationPolynomial K + 1) := by
  constructor
  · -- Shift to the point `1`, where divisibility by `(X - 1)^3` becomes divisibility by `X^3`.
    simpa using (Polynomial.X_sub_C_pow_dvd_iff (p := exercise_1_3_12_interpolationPolynomial K - 1)
      (n := 3) (t := (1 : K))).2
      ⟨C ((⅟2 : K) ^ 3) * (C (3 : K) * X ^ 2 + C (15 : K) * X + C (20 : K)),
        by
          have hshift :
              (exercise_1_3_12_interpolationPolynomial K - 1).comp (X + C (1 : K)) =
                C ((⅟2 : K) ^ 3) * X ^ 3 * (C (3 : K) * X ^ 2 + C (15 : K) * X + C (20 : K)) := by
            simpa using interpolationPolynomial_sub_one_shifted (K := K)
          calc
            (exercise_1_3_12_interpolationPolynomial K - 1).comp (X + C (1 : K))
                = C ((⅟2 : K) ^ 3) * X ^ 3 * (C (3 : K) * X ^ 2 + C (15 : K) * X + C (20 : K)) :=
                    hshift
            _ = X ^ 3 * (C ((⅟2 : K) ^ 3) * (C (3 : K) * X ^ 2 + C (15 : K) * X + C (20 : K))) := by
                  rw [← mul_assoc, mul_comm (C ((⅟2 : K) ^ 3)) (X ^ 3), mul_assoc]⟩
  · -- Shift to the point `-1`, where divisibility by `(X + 1)^3` becomes divisibility by `X^3`.
    simpa [sub_eq_add_neg] using
      (Polynomial.X_sub_C_pow_dvd_iff (p := exercise_1_3_12_interpolationPolynomial K + 1)
        (n := 3) (t := (-1 : K))).2
        ⟨C ((⅟2 : K) ^ 3) * (C (3 : K) * X ^ 2 - C (15 : K) * X + C (20 : K)),
          by
            have hshift :
                (exercise_1_3_12_interpolationPolynomial K + 1).comp (X + C (-1 : K)) =
                  C ((⅟2 : K) ^ 3) * X ^ 3 * (C (3 : K) * X ^ 2 - C (15 : K) * X + C (20 : K)) := by
              simpa [sub_eq_add_neg] using interpolationPolynomial_add_one_shifted (K := K)
            calc
              (exercise_1_3_12_interpolationPolynomial K + 1).comp (X + C (-1 : K))
                  =
                    C ((⅟2 : K) ^ 3) * X ^ 3 * (C (3 : K) * X ^ 2 - C (15 : K) * X + C (20 : K)) :=
                      hshift
              _ =
                  X ^ 3 *
                    (C ((⅟2 : K) ^ 3) * (C (3 : K) * X ^ 2 - C (15 : K) * X + C (20 : K))) := by
                    rw [← mul_assoc, mul_comm (C ((⅟2 : K) ^ 3)) (X ^ 3), mul_assoc]⟩

-- Proof sketch: the difference of two solutions is divisible by both coprime factors
-- `(X - 1)^3` and `(X + 1)^3`, hence by their product via the polynomial Chinese
-- remainder principle; conversely, adding any multiple of that product preserves
-- both congruences.
/-- Exercise 1.3.12 (2): over a commutative ring in which `2` is invertible, a polynomial
satisfies `P ≡ 1 mod (X - 1)^3` and `P ≡ -1 mod (X + 1)^3` exactly when it differs from
`exercise_1_3_12_interpolationPolynomial K` by a polynomial divisible by
`((X - 1)^3) * ((X + 1)^3)`. -/
theorem polynomial_cubic_congruence_at_plus_minus_one_iff (P : K[X]) :
    (((X - 1 : K[X]) ^ 3 ∣ P - 1) ∧ ((X + 1 : K[X]) ^ 3 ∣ P + 1)) ↔
      ((X - 1 : K[X]) ^ 3 * (X + 1) ^ 3) ∣ P - exercise_1_3_12_interpolationPolynomial K := by
  let A : K[X] := (X - 1) ^ 3
  let B : K[X] := (X + 1) ^ 3
  have hspec := exercise_1_3_12_interpolationPolynomial_spec (K := K)
  have hcoprime : IsCoprime A B := by
    simpa [A, B] using isCoprime_X_sub_one_cube_X_add_one_cube (K := K)
  constructor
  · rintro ⟨hA, hB⟩
    have hA' : A ∣ P - exercise_1_3_12_interpolationPolynomial K := by
      -- Subtract the two congruences at `1`.
      simpa [A, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using dvd_sub hA hspec.1
    have hB' : B ∣ P - exercise_1_3_12_interpolationPolynomial K := by
      -- Subtract the two congruences at `-1`.
      simpa [B, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using dvd_sub hB hspec.2
    exact hcoprime.mul_dvd hA' hB'
  · intro hprod
    have hAprod : A ∣ P - exercise_1_3_12_interpolationPolynomial K :=
      (dvd_mul_of_dvd_left (dvd_refl A) B).trans hprod
    have hBprod : B ∣ P - exercise_1_3_12_interpolationPolynomial K :=
      (dvd_mul_of_dvd_right (dvd_refl B) A).trans hprod
    constructor
    · -- Add back the fixed solution at `1`.
      simpa [A, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using dvd_add hAprod hspec.1
    · -- Add back the fixed solution at `-1`.
      simpa [B, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using dvd_add hBprod hspec.2

end PolynomialCongruenceSystem

end
