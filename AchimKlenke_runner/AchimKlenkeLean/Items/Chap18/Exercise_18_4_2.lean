import AchimKlenkeLean.Items.Chap18.Exercise_18_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

namespace ProbabilityTheory

-- Proof sketch: rewrite the Chebyshev term in `(18.16)` using the standard identity
-- `U_{n-1}(cos θ) = sin (n θ) / sin θ` with `θ = arccos (x / σ)`, then use
-- `sin (arccos t) = √(1 - t^2)` and the factorization of the Chebyshev polynomial into its real
-- roots `cos (π k / N)` to obtain the product formula.
/-- Exercise 18.4.2: for the gambler's ruin characteristic polynomial from Example 18.20, the
Chebyshev formula from `(18.16)` for `χ_N`, namely
`(gamblerRuinCharacteristicPolynomial r (N - 1)).eval x`, agrees on `(-σ, σ)` both with the
trigonometric de Moivre formula and with the product factorization over the roots
`σ cos (π k / N)`. -/
theorem gamblerRuinCharacteristicPolynomial_eq_trigonometric_and_product_forms
    (r : ℝ) (N : ℕ) (hN : 2 ≤ N) {x : ℝ}
    (hx : x ∈ Set.Ioo (-(gamblerRuinSigma r)) (gamblerRuinSigma r)) :
    (gamblerRuinCharacteristicPolynomial r (N - 1)).eval x =
        (-1 : ℝ) ^ (N - 1) * (gamblerRuinSigma r / 2) ^ (N - 1) * (1 - x) ^ (2 : ℕ) *
          (Real.sin (N * Real.arccos (x / gamblerRuinSigma r)) /
            Real.sqrt (1 - (x / gamblerRuinSigma r) ^ (2 : ℕ))) ∧
      (gamblerRuinCharacteristicPolynomial r (N - 1)).eval x =
        (1 - x) ^ (2 : ℕ) *
          ∏ k ∈ Finset.Icc 1 (N - 1),
            (gamblerRuinSigma r * Real.cos (Real.pi * k / N) - x) := sorry

end ProbabilityTheory
