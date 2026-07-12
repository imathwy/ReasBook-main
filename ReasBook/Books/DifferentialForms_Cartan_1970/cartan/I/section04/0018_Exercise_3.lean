import Mathlib.RingTheory.PowerSeries.Substitution

-- Declarations for this item will be appended below by the statement pipeline.

open scoped PowerSeries
open PowerSeries

noncomputable section

-- Domain sampling / source-core-bridge triage:
-- * source-facing: the low-degree coefficients of the substitution inverse of a series tangent to
--   the identity, and the concrete Exercise 3 series.
-- * core/canonical owner: Mathlib's `PowerSeries.substInvOfIsUnit`.
-- * sampled derived API: `PowerSeries.coeff_one_substInvOfIsUnit`,
--   `PowerSeries.subst_substInvOfIsUnit_right`, and the project bridge
--   `powerSeries_subst_right_inverse_eq_substInvOfIsUnit` from section01.

section SubstInvOfIsUnitCoeffs

variable {K : Type*} [CommRing K] (P : K⟦X⟧)
variable (hP1 : P.coeff 1 = 1)

/-- A series with linear coefficient `1` has unit linear coefficient, so the canonical owner
`PowerSeries.substInvOfIsUnit` applies directly. -/
theorem isUnit_coeff_one_of_coeff_one_eq_one (hP1 : P.coeff 1 = 1) : IsUnit (P.coeff 1) := by
  simp [hP1]

/-- Exercise 3 (1): for the canonical recursive inverse `P.substInvOfIsUnit` of a series with
linear coefficient `1`, the quadratic coefficient is `-a₂`.

When `P.constantCoeff = 0`, this is the quadratic coefficient of the formal compositional
inverse. -/
theorem coeff_two_substInvOfIsUnit_of_coeff_one_eq_one :
    (P.substInvOfIsUnit (isUnit_coeff_one_of_coeff_one_eq_one P hP1)).coeff 2 = -P.coeff 2 := by
  -- Read the quadratic coefficient directly from the recursive definition of `substInvFun`.
  letI := (isUnit_coeff_one_of_coeff_one_eq_one P hP1).invertible
  rw [PowerSeries.substInvOfIsUnit_eq_substInv]
  have hinv : ⅟(P.coeff 1) = 1 := by
    apply invOf_eq_right_inv
    simp [hP1]
  simp [PowerSeries.substInv, PowerSeries.substInvFun, hP1, hinv]

/-- Helper for Exercise 3: if the inner series has zero constant term, then the `n`th coefficient
of a substitution only depends on the first `n + 1` coefficients of the outer series. -/
theorem coeff_subst_eq_sum_range_of_constantCoeff_zero {b : K⟦X⟧} (hb0 : b.constantCoeff = 0)
    (f : K⟦X⟧) (n : ℕ) :
    coeff n (f.subst b) = ∑ d ∈ Finset.range (n + 1), coeff d f * coeff n (b ^ d) := by
  -- Replace the infinite `finsum` in `coeff_subst'` by a finite range using the order bound.
  have hb : HasSubst b := HasSubst.of_constantCoeff_zero' hb0
  rw [coeff_subst' hb, finsum_eq_sum_of_support_subset (s := Finset.range (n + 1))]
  · simp [smul_eq_mul]
  · intro d hd
    rw [Function.mem_support] at hd
    by_contra hdn
    have hdn' : ¬ d < n + 1 := by
      simpa [Finset.mem_range] using hdn
    have hnd : n < d := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.not_lt.mp hdn')
    have hzero : coeff n (b ^ d) = 0 := by
      apply coeff_of_lt_order
      exact lt_of_lt_of_le (by exact_mod_cast hnd) (le_order_pow_of_constantCoeff_eq_zero d hb0)
    exact hd <| by simp [hzero]

/-- Helper for Exercise 3: substituting `X + a X^2` into a series changes the cubic coefficient by
`2 a₂ a + a₃`. -/
theorem coeff_three_subst_quadratic_trunc (P : K⟦X⟧) (a : K) :
    coeff 3 (P.subst (X + C a * X ^ 2)) = 2 * P.coeff 2 * a + P.coeff 3 := by
  -- Truncate the substitution formula at degree `3`, where only powers `≤ 3` contribute.
  have hb0 : (X + C a * X ^ 2 : K⟦X⟧).constantCoeff = 0 := by
    simp
  have hB1 : coeff 3 (X + C a * X ^ 2 : K⟦X⟧) = 0 := by
    simp [coeff_X, coeff_X_pow]
  have hB2 : coeff 3 ((X + C a * X ^ 2 : K⟦X⟧) ^ 2) = 2 * a := by
    -- Expand the square and read off the `X^3` coefficient.
    have hsq : ((X + C a * X ^ 2 : K⟦X⟧) ^ 2) = X ^ 2 + X ^ 3 * C a * 2 + X ^ 4 * C a ^ 2 := by
      ring
    rw [hsq]
    have hterm : coeff 3 ((X : K⟦X⟧) ^ 3 * C a * 2) = a * 2 := by
      rw [show (X : K⟦X⟧) ^ 3 * C a * 2 = ((X : K⟦X⟧) ^ 3 * C a) * C (2 : K) by rfl]
      rw [coeff_mul_C, coeff_X_pow_mul']
      simp
    have hterm4 : coeff 3 ((X : K⟦X⟧) ^ 4 * C a ^ 2) = 0 := by
      rw [coeff_X_pow_mul']
      simp
    calc
      coeff 3 (X ^ 2 + X ^ 3 * C a * 2 + X ^ 4 * C a ^ 2) = a * 2 := by
        simp [coeff_X_pow, hterm, hterm4]
      _ = 2 * a := by ring
  have hB3 : coeff 3 ((X + C a * X ^ 2 : K⟦X⟧) ^ 3) = 1 := by
    -- The cubic power starts with `X^3`, and all higher terms have degree at least `4`.
    have hcub : ((X + C a * X ^ 2 : K⟦X⟧) ^ 3) =
        X ^ 3 + X ^ 4 * C a * 3 + X ^ 5 * C a ^ 2 * 3 + X ^ 6 * C a ^ 3 := by
      ring
    rw [hcub]
    have hterm4 : coeff 3 ((X : K⟦X⟧) ^ 4 * C a * 3) = 0 := by
      rw [show (X : K⟦X⟧) ^ 4 * C a * 3 = ((X : K⟦X⟧) ^ 4 * C a) * C (3 : K) by rfl]
      rw [coeff_mul_C, coeff_X_pow_mul']
      simp
    have hterm5 : coeff 3 ((X : K⟦X⟧) ^ 5 * C a ^ 2 * 3) = 0 := by
      rw [show (X : K⟦X⟧) ^ 5 * C a ^ 2 * 3 = ((X : K⟦X⟧) ^ 5 * C a ^ 2) * C (3 : K) by rfl]
      rw [coeff_mul_C, coeff_X_pow_mul']
      simp
    have hterm6 : coeff 3 ((X : K⟦X⟧) ^ 6 * C a ^ 3) = 0 := by
      rw [coeff_X_pow_mul']
      simp
    simp [hterm4, hterm5, hterm6]
  -- The finite substitution formula now collapses to the three contributing powers.
  have hseries : (X + X ^ 2 * C a : K⟦X⟧) = X + C a * X ^ 2 := by
    ring
  simpa [Finset.sum_range_succ, coeff_X, coeff_X_pow, hseries, hB1, hB2, hB3,
    pow_zero, pow_one, mul_assoc, mul_comm, mul_left_comm] using
    coeff_subst_eq_sum_range_of_constantCoeff_zero (b := (X + C a * X ^ 2 : K⟦X⟧)) hb0 P 3

/-- Exercise 3 (2): for the canonical recursive inverse `P.substInvOfIsUnit` of a series with
linear coefficient `1`, the cubic coefficient is `2 a₂² - a₃`.

When `P.constantCoeff = 0`, this is the cubic coefficient of the formal compositional inverse. -/
theorem coeff_three_substInvOfIsUnit_of_coeff_one_eq_one :
    (P.substInvOfIsUnit (isUnit_coeff_one_of_coeff_one_eq_one P hP1)).coeff 3 =
      2 * P.coeff 2 ^ 2 - P.coeff 3 := by
  -- Route correction: compute the next recursive truncation explicitly as `X - a₂ X^2`.
  letI := (isUnit_coeff_one_of_coeff_one_eq_one P hP1).invertible
  rw [PowerSeries.substInvOfIsUnit_eq_substInv]
  have hinv : ⅟(P.coeff 1) = 1 := by
    apply invOf_eq_right_inv
    simp [hP1]
  have hq2coeff : (P.substInv).coeff 2 = -P.coeff 2 := by
    simpa [PowerSeries.substInvOfIsUnit_eq_substInv] using
      coeff_two_substInvOfIsUnit_of_coeff_one_eq_one (P := P) (hP1 := hP1)
  have hq2 : P.substInvFun 2 = -P.coeff 2 := by
    simpa [PowerSeries.substInv] using hq2coeff
  -- Identify the rank-`3` truncation used by the recursion.
  have htrunc :
      (∑ i : Fin 3, C (P.substInvFun i.1) * X ^ i.1) = X + C (-P.coeff 2) * X ^ 2 := by
    rw [Fin.sum_univ_three]
    simp [PowerSeries.substInvFun, hinv, hq2]
  -- Substitute the explicit quadratic truncation and simplify the resulting polynomial identity.
  simp [PowerSeries.substInv, PowerSeries.substInvFun, hP1, hinv]
  rw [htrunc, coeff_three_subst_quadratic_trunc]
  ring_nf

/-- Helper for Exercise 3: substituting `X + a X^2 + b X^3` into a series changes the quartic
coefficient by `a₂ (a² + 2 b) + a₃ (3 a) + a₄`. -/
theorem coeff_four_subst_cubic_trunc (P : K⟦X⟧) (a b : K) :
    coeff 4 (P.subst (X + C a * X ^ 2 + C b * X ^ 3)) =
      P.coeff 2 * (a ^ 2 + 2 * b) + P.coeff 3 * (3 * a) + P.coeff 4 := by
  let B : K⟦X⟧ := X + C a * X ^ 2 + C b * X ^ 3
  have hb0 : B.constantCoeff = 0 := by
    simp [B]
  have hB1 : coeff 4 B = 0 := by
    -- The cubic truncation has no quartic term of its own.
    simp [B, coeff_X, coeff_X_pow]
  have hB2 : coeff 4 (B ^ 2) = a ^ 2 + 2 * b := by
    -- The quartic coefficient of the square comes from the `(2, 2)` and `(1, 3)` splittings.
    rw [show B ^ 2 = B * B by simp [pow_two], coeff_mul]
    norm_num [B, Finset.antidiagonal, coeff_X, coeff_X_pow, coeff_C]
    ring
  have hBsq1 : coeff 1 (B ^ 2) = 0 := by
    -- The square starts in degree `2`.
    rw [show B ^ 2 = B * B by simp [pow_two], coeff_mul]
    norm_num [B, Finset.antidiagonal, coeff_X, coeff_X_pow, coeff_C]
  have hBsq2 : coeff 2 (B ^ 2) = 1 := by
    -- The only quadratic contribution is `X * X`.
    rw [show B ^ 2 = B * B by simp [pow_two], coeff_mul]
    norm_num [B, Finset.antidiagonal, coeff_X, coeff_X_pow, coeff_C]
  have hBsq3 : coeff 3 (B ^ 2) = 2 * a := by
    -- The cubic contribution comes from one linear and one quadratic factor.
    rw [show B ^ 2 = B * B by simp [pow_two], coeff_mul]
    norm_num [B, Finset.antidiagonal, coeff_X, coeff_X_pow, coeff_C]
    ring
  have hB3 : coeff 4 (B ^ 3) = 3 * a := by
    -- For the cube, only the degree patterns `(2,1,1)` contribute to degree `4`.
    rw [show B ^ 3 = B ^ 2 * B by simp [pow_succ], coeff_mul]
    simp [B, Finset.antidiagonal, coeff_X, coeff_X_pow, hBsq1, hBsq2, hBsq3]
    ring
  have hBcub1 : coeff 1 (B ^ 3) = 0 := by
    -- The cube starts in degree `3`.
    rw [show B ^ 3 = B ^ 2 * B by simp [pow_succ], coeff_mul]
    simp [B, Finset.antidiagonal, coeff_X, coeff_X_pow, hBsq1]
  have hBcub2 : coeff 2 (B ^ 3) = 0 := by
    -- There is still no quadratic term in the cube.
    rw [show B ^ 3 = B ^ 2 * B by simp [pow_succ], coeff_mul]
    simp [B, Finset.antidiagonal, coeff_X, coeff_X_pow, hBsq1, hBsq2]
  have hBcub3 : coeff 3 (B ^ 3) = 1 := by
    -- The leading cubic term remains `X^3`.
    rw [show B ^ 3 = B ^ 2 * B by simp [pow_succ], coeff_mul]
    simp [B, Finset.antidiagonal, coeff_X, coeff_X_pow, hBsq1, hBsq2]
  have hB4 : coeff 4 (B ^ 4) = 1 := by
    -- The quartic term of the fourth power is just the leading term `X^4`.
    rw [show B ^ 4 = B ^ 3 * B by simp [pow_succ], coeff_mul]
    simp [B, Finset.antidiagonal, coeff_X, coeff_X_pow, hBcub1, hBcub2, hBcub3]
  have hsubst :
      coeff 4 (P.subst B) = P.coeff 2 * (a ^ 2 + 2 * b) + P.coeff 3 * (3 * a) + P.coeff 4 := by
    -- The finite substitution formula leaves only the powers `2`, `3`, and `4`.
    simpa [Finset.sum_range_succ, hB1, hB2, hB3, hB4, pow_zero, pow_one,
      mul_assoc, mul_comm, mul_left_comm] using
      coeff_subst_eq_sum_range_of_constantCoeff_zero (b := B) hb0 P 4
  simpa [B] using hsubst

/-- Exercise 3 (3): for the canonical recursive inverse `P.substInvOfIsUnit` of a series with
linear coefficient `1`, the quartic coefficient is `-5 a₂³ + 5 a₂ a₃ - a₄`.

When `P.constantCoeff = 0`, this is the quartic coefficient of the formal compositional
inverse. -/
theorem coeff_four_substInvOfIsUnit_of_coeff_one_eq_one :
    (P.substInvOfIsUnit (isUnit_coeff_one_of_coeff_one_eq_one P hP1)).coeff 4 =
      -5 * P.coeff 2 ^ 3 + 5 * P.coeff 2 * P.coeff 3 - P.coeff 4 := by
  -- Route correction: identify the rank-`4` truncation explicitly and compute its substituted
  -- quartic coefficient through the standalone cubic-truncation lemma above.
  letI := (isUnit_coeff_one_of_coeff_one_eq_one P hP1).invertible
  rw [PowerSeries.substInvOfIsUnit_eq_substInv]
  have hinv : ⅟(P.coeff 1) = 1 := by
    apply invOf_eq_right_inv
    simp [hP1]
  have hq2coeff : (P.substInv).coeff 2 = -P.coeff 2 := by
    simpa [PowerSeries.substInvOfIsUnit_eq_substInv] using
      coeff_two_substInvOfIsUnit_of_coeff_one_eq_one (P := P) (hP1 := hP1)
  have hq2 : P.substInvFun 2 = -P.coeff 2 := by
    simpa [PowerSeries.substInv] using hq2coeff
  have hq3coeff : (P.substInv).coeff 3 = 2 * P.coeff 2 ^ 2 - P.coeff 3 := by
    simpa [PowerSeries.substInvOfIsUnit_eq_substInv] using
      coeff_three_substInvOfIsUnit_of_coeff_one_eq_one (P := P) (hP1 := hP1)
  have hq3 : P.substInvFun 3 = 2 * P.coeff 2 ^ 2 - P.coeff 3 := by
    simpa [PowerSeries.substInv] using hq3coeff
  have htrunc :
      (∑ i : Fin 4, C (P.substInvFun i.1) * X ^ i.1) =
        X + C (-P.coeff 2) * X ^ 2 + C (2 * P.coeff 2 ^ 2 - P.coeff 3) * X ^ 3 := by
    -- The recursive truncation is the source-faithful cubic approximation to the inverse.
    rw [Fin.sum_univ_four]
    simp [PowerSeries.substInvFun, hinv, hq2, hq3]
  -- Read the quartic recursion step and rewrite the substituted truncation explicitly.
  simp [PowerSeries.substInv, PowerSeries.substInvFun, hP1, hinv]
  rw [htrunc, coeff_four_subst_cubic_trunc]
  ring_nf

/-- Helper for Exercise 3: substituting `X + a X^2 + b X^3 + c X^4` into a series changes the
quintic coefficient by `a₂ (2ab + 2c) + a₃ (3b + 3a²) + a₄ (4a) + a₅`. -/
theorem coeff_five_subst_quartic_trunc (P : K⟦X⟧) (a b c : K) :
    coeff 5 (P.subst (X + C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4)) =
      P.coeff 2 * (2 * a * b + 2 * c) + P.coeff 3 * (3 * b + 3 * a ^ 2) +
        P.coeff 4 * (4 * a) + P.coeff 5 := by
  let B : K⟦X⟧ := X + C a * X ^ 2 + C b * X ^ 3 + C c * X ^ 4
  have hb0 : B.constantCoeff = 0 := by
    simp [B]
  have hB1 : coeff 5 B = 0 := by
    -- The quartic truncation has no quintic term of its own.
    simp [B, coeff_X, coeff_X_pow]
  have hB2 : coeff 5 (B ^ 2) = 2 * a * b + 2 * c := by
    -- Degree `5` in the square comes from the splittings `(1,4)` and `(2,3)`.
    rw [show B ^ 2 = B * B by simp [pow_two], coeff_mul]
    norm_num [B, Finset.antidiagonal, coeff_X, coeff_X_pow, coeff_C]
    ring
  have hBsq1 : coeff 1 (B ^ 2) = 0 := by
    -- The square still starts in degree `2`.
    rw [show B ^ 2 = B * B by simp [pow_two], coeff_mul]
    norm_num [B, Finset.antidiagonal, coeff_X, coeff_X_pow, coeff_C]
  have hBsq2 : coeff 2 (B ^ 2) = 1 := by
    -- The quadratic term is again the leading `X^2`.
    rw [show B ^ 2 = B * B by simp [pow_two], coeff_mul]
    norm_num [B, Finset.antidiagonal, coeff_X, coeff_X_pow, coeff_C]
  have hBsq3 : coeff 3 (B ^ 2) = 2 * a := by
    -- Degree `3` comes from one linear and one quadratic factor.
    rw [show B ^ 2 = B * B by simp [pow_two], coeff_mul]
    norm_num [B, Finset.antidiagonal, coeff_X, coeff_X_pow, coeff_C]
    ring
  have hBsq4 : coeff 4 (B ^ 2) = a ^ 2 + 2 * b := by
    -- Degree `4` comes from `(2,2)` and `(1,3)`.
    rw [show B ^ 2 = B * B by simp [pow_two], coeff_mul]
    norm_num [B, Finset.antidiagonal, coeff_X, coeff_X_pow, coeff_C]
    ring
  have hB3 : coeff 5 (B ^ 3) = 3 * b + 3 * a ^ 2 := by
    -- For the cube, only degree patterns `(3,1,1)` and `(2,2,1)` reach degree `5`.
    rw [show B ^ 3 = B ^ 2 * B by simp [pow_succ], coeff_mul]
    simp [B, Finset.antidiagonal, coeff_X, coeff_X_pow, hBsq1, hBsq2, hBsq3, hBsq4]
    ring
  have hBcub1 : coeff 1 (B ^ 3) = 0 := by
    -- The cube starts in degree `3`.
    rw [show B ^ 3 = B ^ 2 * B by simp [pow_succ], coeff_mul]
    simp [B, Finset.antidiagonal, coeff_X, coeff_X_pow, hBsq1]
  have hBcub2 : coeff 2 (B ^ 3) = 0 := by
    -- There is still no quadratic term in the cube.
    rw [show B ^ 3 = B ^ 2 * B by simp [pow_succ], coeff_mul]
    simp [B, Finset.antidiagonal, coeff_X, coeff_X_pow, hBsq1, hBsq2]
  have hBcub3 : coeff 3 (B ^ 3) = 1 := by
    -- The leading cubic term is `X^3`.
    rw [show B ^ 3 = B ^ 2 * B by simp [pow_succ], coeff_mul]
    simp [B, Finset.antidiagonal, coeff_X, coeff_X_pow, hBsq1, hBsq2]
  have hBcub4 : coeff 4 (B ^ 3) = 3 * a := by
    -- Degree `4` in the cube is the already-computed cubic-truncation contribution.
    rw [show B ^ 3 = B ^ 2 * B by simp [pow_succ], coeff_mul]
    simp [B, Finset.antidiagonal, coeff_X, coeff_X_pow, hBsq1, hBsq2, hBsq3]
    ring
  have hB4 : coeff 5 (B ^ 4) = 4 * a := by
    -- In the fourth power, only the patterns `(2,1,1,1)` contribute to degree `5`.
    rw [show B ^ 4 = B ^ 3 * B by simp [pow_succ], coeff_mul]
    simp [B, Finset.antidiagonal, coeff_X, coeff_X_pow, hBcub1, hBcub2, hBcub3, hBcub4]
    ring
  have hBquad1 : coeff 1 (B ^ 4) = 0 := by
    -- The fourth power starts in degree `4`.
    rw [show B ^ 4 = B ^ 3 * B by simp [pow_succ], coeff_mul]
    simp [B, Finset.antidiagonal, coeff_X, coeff_X_pow, hBcub1]
  have hBquad2 : coeff 2 (B ^ 4) = 0 := by
    -- There is no quadratic term in the fourth power.
    rw [show B ^ 4 = B ^ 3 * B by simp [pow_succ], coeff_mul]
    simp [B, Finset.antidiagonal, coeff_X, coeff_X_pow, hBcub1, hBcub2]
  have hBquad3 : coeff 3 (B ^ 4) = 0 := by
    -- There is no cubic term in the fourth power either.
    rw [show B ^ 4 = B ^ 3 * B by simp [pow_succ], coeff_mul]
    simp [B, Finset.antidiagonal, coeff_X, coeff_X_pow, hBcub1, hBcub2, hBcub3]
  have hBquad4 : coeff 4 (B ^ 4) = 1 := by
    -- The leading quartic term of the fourth power is `X^4`.
    rw [show B ^ 4 = B ^ 3 * B by simp [pow_succ], coeff_mul]
    simp [B, Finset.antidiagonal, coeff_X, coeff_X_pow, hBcub1, hBcub2, hBcub3]
  have hB5 : coeff 5 (B ^ 5) = 1 := by
    -- The leading quintic term of the fifth power is `X^5`.
    rw [show B ^ 5 = B ^ 4 * B by simp [pow_succ], coeff_mul]
    simp [B, Finset.antidiagonal, coeff_X, coeff_X_pow, hBquad1, hBquad2, hBquad3, hBquad4]
  have hsubst :
      coeff 5 (P.subst B) =
        P.coeff 2 * (2 * a * b + 2 * c) + P.coeff 3 * (3 * b + 3 * a ^ 2) +
          P.coeff 4 * (4 * a) + P.coeff 5 := by
    -- The finite substitution formula leaves only the powers `2`, `3`, `4`, and `5`.
    simpa [Finset.sum_range_succ, hB1, hB2, hB3, hB4, hB5, pow_zero, pow_one,
      mul_assoc, mul_comm, mul_left_comm] using
      coeff_subst_eq_sum_range_of_constantCoeff_zero (b := B) hb0 P 5
  simpa [B] using hsubst

/-- Exercise 3 (4): for the canonical recursive inverse `P.substInvOfIsUnit` of a series with
linear coefficient `1`, the quintic coefficient is
`14 a₂⁴ - 21 a₂² a₃ + 6 a₂ a₄ + 3 a₃² - a₅`.

When `P.constantCoeff = 0`, this is the quintic coefficient of the formal compositional
inverse. -/
theorem coeff_five_substInvOfIsUnit_of_coeff_one_eq_one :
    (P.substInvOfIsUnit (isUnit_coeff_one_of_coeff_one_eq_one P hP1)).coeff 5 =
      14 * P.coeff 2 ^ 4 - 21 * P.coeff 2 ^ 2 * P.coeff 3 + 6 * P.coeff 2 * P.coeff 4 +
        3 * P.coeff 3 ^ 2 - P.coeff 5 := by
  -- Route correction: identify the rank-`5` truncation explicitly and compute its substituted
  -- quintic coefficient through the standalone quartic-truncation lemma above.
  letI := (isUnit_coeff_one_of_coeff_one_eq_one P hP1).invertible
  rw [PowerSeries.substInvOfIsUnit_eq_substInv]
  have hinv : ⅟(P.coeff 1) = 1 := by
    apply invOf_eq_right_inv
    simp [hP1]
  have hq2coeff : (P.substInv).coeff 2 = -P.coeff 2 := by
    simpa [PowerSeries.substInvOfIsUnit_eq_substInv] using
      coeff_two_substInvOfIsUnit_of_coeff_one_eq_one (P := P) (hP1 := hP1)
  have hq2 : P.substInvFun 2 = -P.coeff 2 := by
    simpa [PowerSeries.substInv] using hq2coeff
  have hq3coeff : (P.substInv).coeff 3 = 2 * P.coeff 2 ^ 2 - P.coeff 3 := by
    simpa [PowerSeries.substInvOfIsUnit_eq_substInv] using
      coeff_three_substInvOfIsUnit_of_coeff_one_eq_one (P := P) (hP1 := hP1)
  have hq3 : P.substInvFun 3 = 2 * P.coeff 2 ^ 2 - P.coeff 3 := by
    simpa [PowerSeries.substInv] using hq3coeff
  have hq4coeff :
      (P.substInv).coeff 4 = -5 * P.coeff 2 ^ 3 + 5 * P.coeff 2 * P.coeff 3 - P.coeff 4 := by
    simpa [PowerSeries.substInvOfIsUnit_eq_substInv] using
      coeff_four_substInvOfIsUnit_of_coeff_one_eq_one (P := P) (hP1 := hP1)
  have hq4 : P.substInvFun 4 = -5 * P.coeff 2 ^ 3 + 5 * P.coeff 2 * P.coeff 3 - P.coeff 4 := by
    simpa [PowerSeries.substInv] using hq4coeff
  have htrunc :
      (∑ i : Fin 5, C (P.substInvFun i.1) * X ^ i.1) =
        X + C (-P.coeff 2) * X ^ 2 + C (2 * P.coeff 2 ^ 2 - P.coeff 3) * X ^ 3 +
          C (-5 * P.coeff 2 ^ 3 + 5 * P.coeff 2 * P.coeff 3 - P.coeff 4) * X ^ 4 := by
    -- The recursive truncation is the source-faithful quartic approximation to the inverse.
    rw [Fin.sum_univ_five]
    simp [PowerSeries.substInvFun, hinv, hq2, hq3, hq4]
  -- Read the quintic recursion step and rewrite the substituted truncation explicitly.
  simp [PowerSeries.substInv, PowerSeries.substInvFun, hP1, hinv]
  rw [htrunc, coeff_five_subst_quartic_trunc]
  ring_nf

end SubstInvOfIsUnitCoeffs

/-- The formal power series `X - X^3 / 3 + X^5 / 5 - ⋯` from Exercise 3. -/
def exercise3Series : ℚ⟦X⟧ :=
  mk fun n ↦ if n % 2 = 1 then ((-1 : ℚ) ^ (n / 2)) / n else 0

/-- The coefficient formula for `exercise3Series`. -/
@[simp] theorem coeff_exercise3Series (n : ℕ) :
    exercise3Series.coeff n = if n % 2 = 1 then ((-1 : ℚ) ^ (n / 2)) / n else 0 := by
  simp [exercise3Series]

/-- The series from Exercise 3 has vanishing constant term. -/
theorem exercise3Series_constantCoeff_zero : exercise3Series.constantCoeff = 0 := by
  simpa [coeff_zero_eq_constantCoeff_apply] using coeff_exercise3Series 0

/-- The linear coefficient of `exercise3Series` is `1`. -/
theorem exercise3Series_coeff_one_eq_one : exercise3Series.coeff 1 = 1 := by
  simp

/-- The series from Exercise 3 has unit linear coefficient, so its canonical
compositional inverse is available via `PowerSeries.substInvOfIsUnit`. -/
theorem exercise3Series_coeff_one_isUnit : IsUnit (exercise3Series.coeff 1) :=
  isUnit_coeff_one_of_coeff_one_eq_one exercise3Series exercise3Series_coeff_one_eq_one

/-- The degree-`≤ 5` truncation `X + X^3 / 3 + 2 X^5 / 15` of the inverse series from Exercise 3.
-/
def exercise3InverseDegreeFive : ℚ⟦X⟧ :=
  X + C ((1 : ℚ) / 3) * X ^ 3 + C ((2 : ℚ) / 15) * X ^ 5

/-- Exercise 3 (5): for
`S(X) = X - X^3 / 3 + X^5 / 5 - ⋯`,
the formal compositional inverse agrees through degree `5` with
`X + X^3 / 3 + 2 X^5 / 15`. -/
theorem exercise3_inverse_coeffs_up_to_five (n : ℕ) (hn : n ≤ 5) :
    (exercise3Series.substInvOfIsUnit exercise3Series_coeff_one_isUnit).coeff n =
      exercise3InverseDegreeFive.coeff n := by
  -- The generic inverse-coefficient formulas determine the coefficients case by case up to degree
  -- `5`, and the concrete Exercise 3 coefficients then simplify to the claimed truncation.
  have hcases :
      n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · -- Constant coefficients vanish for both series.
    simp [exercise3InverseDegreeFive]
  · -- Both series have linear coefficient `1`.
    have hcoeff1 : exercise3InverseDegreeFive.coeff 1 = 1 := by
      rw [exercise3InverseDegreeFive]
      simp [coeff_X_pow, coeff_X]
    have hsubst1 :
        (exercise3Series.substInvOfIsUnit exercise3Series_coeff_one_isUnit).coeff 1 = 1 := by
      simpa using
        (coeff_one_substInvOfIsUnit
          (P := exercise3Series) (hP' := exercise3Series_coeff_one_isUnit))
    calc
      (exercise3Series.substInvOfIsUnit exercise3Series_coeff_one_isUnit).coeff 1 = 1 := hsubst1
      _ = exercise3InverseDegreeFive.coeff 1 := by
        exact hcoeff1.symm
  · -- The quadratic coefficient is `0`.
    have hcoeff2 : exercise3InverseDegreeFive.coeff 2 = 0 := by
      rw [exercise3InverseDegreeFive]
      simp [coeff_X_pow, coeff_X]
    calc
      (exercise3Series.substInvOfIsUnit exercise3Series_coeff_one_isUnit).coeff 2 = 0 := by
        simpa [exercise3Series_coeff_one_isUnit, coeff_exercise3Series] using
          coeff_two_substInvOfIsUnit_of_coeff_one_eq_one
            (P := exercise3Series) (hP1 := exercise3Series_coeff_one_eq_one)
      _ = exercise3InverseDegreeFive.coeff 2 := by
        exact hcoeff2.symm
  · -- The cubic coefficient specializes to `1 / 3`.
    have hcoeff3 : exercise3InverseDegreeFive.coeff 3 = (1 : ℚ) / 3 := by
      rw [exercise3InverseDegreeFive]
      simp [coeff_X_pow, coeff_X]
    have hsubst3 :
        (exercise3Series.substInvOfIsUnit exercise3Series_coeff_one_isUnit).coeff 3 =
          2 * exercise3Series.coeff 2 ^ 2 - exercise3Series.coeff 3 := by
      simpa [exercise3Series_coeff_one_isUnit] using
        coeff_three_substInvOfIsUnit_of_coeff_one_eq_one
          (P := exercise3Series) (hP1 := exercise3Series_coeff_one_eq_one)
    calc
      (exercise3Series.substInvOfIsUnit exercise3Series_coeff_one_isUnit).coeff 3 =
          2 * exercise3Series.coeff 2 ^ 2 - exercise3Series.coeff 3 := hsubst3
      _ = (1 : ℚ) / 3 := by
        norm_num [coeff_exercise3Series]
      _ = exercise3InverseDegreeFive.coeff 3 := by
        exact hcoeff3.symm
  · -- The quartic coefficient vanishes after specialization.
    have hcoeff4 : exercise3InverseDegreeFive.coeff 4 = 0 := by
      rw [exercise3InverseDegreeFive]
      simp [coeff_X_pow, coeff_X]
    calc
      (exercise3Series.substInvOfIsUnit exercise3Series_coeff_one_isUnit).coeff 4 = 0 := by
        simpa [exercise3Series_coeff_one_isUnit, coeff_exercise3Series] using
          coeff_four_substInvOfIsUnit_of_coeff_one_eq_one
            (P := exercise3Series) (hP1 := exercise3Series_coeff_one_eq_one)
      _ = exercise3InverseDegreeFive.coeff 4 := by
        exact hcoeff4.symm
  · -- The quintic coefficient specializes to `2 / 15`.
    have hcoeff5 : exercise3InverseDegreeFive.coeff 5 = (2 : ℚ) / 15 := by
      rw [exercise3InverseDegreeFive]
      simp [coeff_X_pow, coeff_X]
    calc
      (exercise3Series.substInvOfIsUnit exercise3Series_coeff_one_isUnit).coeff 5 =
          3 * (-(1 : ℚ) / 3) ^ 2 - (1 : ℚ) / 5 := by
        simpa [exercise3Series_coeff_one_isUnit, coeff_exercise3Series] using
          coeff_five_substInvOfIsUnit_of_coeff_one_eq_one
            (P := exercise3Series) (hP1 := exercise3Series_coeff_one_eq_one)
      _ = (2 : ℚ) / 15 := by
        norm_num
      _ = exercise3InverseDegreeFive.coeff 5 := by
        exact hcoeff5.symm
