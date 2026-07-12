import ProbabilityTheory_Klenke_2020.Items.Chap18.Example_18_20

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial

noncomputable section

namespace ProbabilityTheory

/-- The source-facing shifted family `chi_(N+1)` from Example 18.20, determined by the initial
values `chi_1 = (1 - X)^2`, `chi_2 = -X (1 - X)^2`, and the recursion `(18.15)`. Its canonical
owner is the characteristic polynomial of `gamblerRuinTransitionMatrixReal`, related below by
`gamblerRuinTransitionMatrix_charpoly_eq`. -/
def gamblerRuinCharacteristicPolynomial (r : ℝ) : ℕ → ℝ[X]
  | 0 => (1 - X) ^ 2
  | 1 => -X * (1 - X) ^ 2
  | n + 2 =>
      -X * gamblerRuinCharacteristicPolynomial r (n + 1) -
        C (r * (1 - r)) * gamblerRuinCharacteristicPolynomial r n

-- Proof sketch: unfold the recursive definition at index `0`; this is exactly the chosen initial
-- value corresponding to `chi_1` in Example 18.20.
/-- The initial polynomial `chi_1` in the shifted family. -/
theorem gamblerRuinCharacteristicPolynomial_chi_one (r : ℝ) :
    gamblerRuinCharacteristicPolynomial r 0 = (1 - X) ^ 2 := rfl

-- Proof sketch: unfold the recursive definition at index `1`; this is exactly the chosen initial
-- value corresponding to `chi_2` in Example 18.20.
/-- The initial polynomial `chi_2` in the shifted family. -/
theorem gamblerRuinCharacteristicPolynomial_chi_two (r : ℝ) :
    gamblerRuinCharacteristicPolynomial r 1 = -X * (1 - X) ^ 2 := rfl

-- Proof sketch: unfold the recursive clause of `gamblerRuinCharacteristicPolynomial`; it is the
-- recursion `(18.15)` rewritten in the shifted indexing used by this file.
/-- The recursion `(18.15)` for the shifted characteristic-polynomial family. -/
theorem gamblerRuinCharacteristicPolynomial_recurrence (r : ℝ) (N : ℕ) :
    gamblerRuinCharacteristicPolynomial r (N + 2) =
      -X * gamblerRuinCharacteristicPolynomial r (N + 1) -
        C (r * (1 - r)) * gamblerRuinCharacteristicPolynomial r N := rfl

-- Proof sketch: `Matrix.charpoly` is the canonical owner for characteristic polynomials in
-- mathlib. The source-facing `chi_(N+1)` is the same polynomial as
-- `det (gamblerRuinTransitionMatrixReal (N + 1) r - X • I)`, while `Matrix.charpoly` is
-- `det (X • I - gamblerRuinTransitionMatrixReal (N + 1) r)`; comparing the two determinants gives
-- the sign `(-1)^N` because the matrix size is `N + 2`.
/-- The canonical owner statement for the shifted family `chi_(N+1)`: up to the usual sign change
between `det (A - X • I)` and `det (X • I - A)`, it is the characteristic polynomial of the
real gambler's ruin transition matrix on `{0, ..., N + 1}`. -/
theorem gamblerRuinTransitionMatrix_charpoly_eq (r : ℝ) (N : ℕ) :
    (gamblerRuinTransitionMatrixReal (N + 1) r).charpoly =
      C ((-1 : ℝ) ^ N) * gamblerRuinCharacteristicPolynomial r N := sorry

-- Proof sketch: prove the closed form by induction on `N` using the two initial values and the
-- recurrence `(18.15)`, together with the standard recursion for `Polynomial.Chebyshev.U`.
/-- Exercise 18.4.1: for `r in (0,1)`, the polynomial `chi_(N+1)` from Example 18.20 satisfies
the closed formula `(18.16)` in terms of the Chebyshev polynomial of the second kind. -/
theorem gamblerRuinCharacteristicPolynomial_eq_chebyshevU
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (N : ℕ) :
    gamblerRuinCharacteristicPolynomial r (N + 1) =
      C (((-1 : ℝ) ^ N) * ((gamblerRuinSigma r / 2) ^ N)) *
        (1 - X) ^ 2 *
        (Polynomial.Chebyshev.U ℝ (N : ℤ)).comp (C ((gamblerRuinSigma r)⁻¹) * X) := sorry

end ProbabilityTheory
