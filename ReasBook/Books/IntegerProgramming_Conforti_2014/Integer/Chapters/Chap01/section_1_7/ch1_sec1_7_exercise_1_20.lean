import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic Lean search was unavailable in this session; this item uses the
-- standard ideal-span formulation of relative primality in `ℤ`.

/-- A Bézout relation for the coefficients produces an integer point on every
translated hyperplane with the same normal vector. -/
theorem integer_points_on_hyperplane_of_bezout
    {n : ℕ} (a : Fin n → ℤ)
    (hbezout : ∃ u : Fin n → ℤ, Finset.univ.sum (fun i => a i * u i) = 1)
    (b : ℤ) :
    ∃ x : Fin n → ℤ, Finset.univ.sum (fun i => a i * x i) = b := sorry

/-- Exercise 1.20. If integers `a₁, ..., aₙ` are relatively prime, then for every
`b : ℤ` the hyperplane `a₁ x₁ + ... + aₙ xₙ = b` contains an integer point. Here
relative primality is expressed by the condition that the coefficients generate
the unit ideal in `ℤ`. -/
theorem integer_points_on_coprime_hyperplane
    {n : ℕ} (hn : 0 < n) (a : Fin n → ℤ)
    (hcoprime : (Ideal.span (Set.range a) : Ideal ℤ) = ⊤)
    (b : ℤ) :
    ∃ x : Fin n → ℤ, Finset.univ.sum (fun i => a i * x i) = b := sorry
