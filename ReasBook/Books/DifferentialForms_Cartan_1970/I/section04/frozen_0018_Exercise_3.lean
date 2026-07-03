import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped PowerSeries
open PowerSeries

noncomputable section

/-- The formal power series `X - X^3 / 3 + X^5 / 5 - ⋯` from Exercise 3. -/
def exercise3Series : ℚ⟦X⟧ :=
  mk fun n ↦ if n % 2 = 1 then ((-1 : ℚ) ^ (n / 2)) / n else 0

@[simp] theorem coeff_exercise3Series (n : ℕ) :
    coeff n exercise3Series = if n % 2 = 1 then ((-1 : ℚ) ^ (n / 2)) / n else 0 := by
  simp [exercise3Series]

-- Proof sketch: compute `coeff 1 exercise3Series` from the defining odd-coefficient formula and
-- rewrite `1` as a unit in `ℚ`.
/-- The linear coefficient of the Exercise 3 series is a unit, so its canonical compositional
inverse `substInvOfIsUnit` is available. -/
theorem exercise3Series_coeff_one_isUnit : IsUnit (coeff 1 exercise3Series) := sorry

section NormalizedSubstInv

variable {K : Type*} [CommRing K] (P : K⟦X⟧) (hP1 : coeff 1 P = 1)

-- Proof sketch: rewrite `P.substInvOfIsUnit (hP1 ▸ isUnit_one)` to `P.substInv` via
-- `PowerSeries.substInvOfIsUnit_eq_substInv`, compute the coefficient recursively from
-- `PowerSeries.substInvFun`, and use `hP1` to simplify every occurrence of `⅟ (P.coeff 1)` to `1`.
/-- For a normalized series `P(X) = X + a₂ X² + ⋯`, the quadratic coefficient of its canonical
compositional inverse is `-a₂`. -/
theorem coeff_two_substInv_of_coeff_one_eq_one :
    coeff 2 (P.substInvOfIsUnit (hP1 ▸ isUnit_one)) = -coeff 2 P := sorry

-- Proof sketch: reduce to `P.substInv` using `PowerSeries.substInvOfIsUnit_eq_substInv`, continue
-- the recursion defining `PowerSeries.substInvFun`, expand the coefficient of `P` composed with the
-- degree-`≤ 2` truncation of its inverse, and simplify using `hP1`.
/-- For a normalized series `P(X) = X + a₂ X² + a₃ X³ + ⋯`, the cubic inverse coefficient is the
polynomial `2 a₂² - a₃`. -/
theorem coeff_three_substInv_of_coeff_one_eq_one :
    coeff 3 (P.substInvOfIsUnit (hP1 ▸ isUnit_one)) = 2 * coeff 2 P ^ 2 - coeff 3 P := sorry

-- Proof sketch: rewrite `P.substInvOfIsUnit (hP1 ▸ isUnit_one)` as `P.substInv`, evaluate the next
-- recursive step for `PowerSeries.substInvFun`, collect the degree-`4` terms in the substitution
-- expansion, and simplify with `hP1`.
/-- For a normalized series `P(X) = X + a₂ X² + a₃ X³ + a₄ X⁴ + ⋯`, the quartic inverse
coefficient is the polynomial `-5 a₂³ + 5 a₂ a₃ - a₄`. -/
theorem coeff_four_substInv_of_coeff_one_eq_one :
    coeff 4 (P.substInvOfIsUnit (hP1 ▸ isUnit_one)) =
      -5 * coeff 2 P ^ 3 + 5 * coeff 2 P * coeff 3 P - coeff 4 P := sorry

-- Proof sketch: rewrite `P.substInvOfIsUnit (hP1 ▸ isUnit_one)` as `P.substInv`, apply one more
-- step of the `substInvFun` recursion, expand the degree-`5` substitution coefficient, and gather
-- the resulting monomials in the coefficients of `P`.
/-- For a normalized series `P(X) = X + a₂ X² + a₃ X³ + a₄ X⁴ + a₅ X⁵ + ⋯`, the quintic inverse
coefficient is the polynomial
`14 a₂⁴ - 21 a₂² a₃ + 6 a₂ a₄ + 3 a₃² - a₅`. -/
theorem coeff_five_substInv_of_coeff_one_eq_one :
    coeff 5 (P.substInvOfIsUnit (hP1 ▸ isUnit_one)) =
      14 * coeff 2 P ^ 4 - 21 * coeff 2 P ^ 2 * coeff 3 P + 6 * coeff 2 P * coeff 4 P +
        3 * coeff 3 P ^ 2 - coeff 5 P := sorry

end NormalizedSubstInv

/-- The degree-`≤ 5` truncation `X + X^3 / 3 + 2 X^5 / 15` of the inverse series from
Exercise 3. -/
def exercise3InverseDegreeFive : ℚ⟦X⟧ :=
  X + C ((1 : ℚ) / 3) * X ^ 3 + C ((2 : ℚ) / 15) * X ^ 5

-- Proof sketch: apply the companion formulas for the coefficients of a normalized compositional
-- inverse to `exercise3Series`, compute its coefficients in degrees `2` through `5`, and compare
-- with `exercise3InverseDegreeFive`.
/-- Exercise 3: the companion formulas above give the low-degree polynomials `P₂`, `P₃`, `P₄`,
and `P₅`, and for the series
`S(X) = X - X^3 / 3 + X^5 / 5 - ⋯` the canonical formal compositional inverse agrees through
degree `5` with `X + X^3 / 3 + 2 X^5 / 15`. -/
theorem exercise3_inverse_coeffs_up_to_five (n : ℕ) (hn : n ≤ 5) :
    coeff n (exercise3Series.substInvOfIsUnit exercise3Series_coeff_one_isUnit) =
      coeff n exercise3InverseDegreeFive := sorry
