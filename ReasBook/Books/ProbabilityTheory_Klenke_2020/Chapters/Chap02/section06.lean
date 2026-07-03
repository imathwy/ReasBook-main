import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_2_6 (from Items/Chap02) -/
-- Proof sketch: specialize mathlib's Euler-product theorem `riemannZeta_eulerProduct_tprod` to
-- the real argument `(s : ℂ)` and simplify `((s : ℂ)).re = s`.
/-- Example 2.6: Euler's prime number formula expresses the Riemann zeta function for real `s > 1`
as the infinite product over all primes. -/
theorem euler_prime_number_formula {s : ℝ} (hs : 1 < s) :
    ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-(s : ℂ)))⁻¹ = riemannZeta (s : ℂ) := by
  have hs' : 1 < ((s : ℂ)).re := by
    simpa
  simpa using
    (riemannZeta_eulerProduct_tprod hs' :
      ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-(s : ℂ)))⁻¹ = riemannZeta (s : ℂ))
