import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_8_30 (from Items/Chap08) -/
open MeasureTheory ProbabilityTheory
open scoped NNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: use `lam1 ≤ lam1 + lam2`, which follows from `0 ≤ lam2`, and divide by the
-- nonnegative denominator `lam1 + lam2`.
private theorem poisson_split_parameter_le_one (lam1 lam2 : ℝ≥0) :
    lam1 / (lam1 + lam2) ≤ 1 := sorry

section PoissonSplit

variable (P : Measure Ω) [IsProbabilityMeasure P]
variable {Z1 Z2 : Ω → ℕ} {lam1 lam2 : ℝ≥0}
variable (hZ1 : HasLaw Z1 (poissonMeasure lam1) P)
variable (hZ2 : HasLaw Z2 (poissonMeasure lam2) P)
variable (hindep : IndepFun Z1 Z2 P)

-- Proof sketch: combine the Poisson laws of `Z₁` and `Z₂` with independence to identify the law
-- of `Z₁ + Z₂`, then compute the conditional point masses given `Z₁ + Z₂ = n`. These point masses
-- agree with the canonical binomial `PMF`, so the conditional law itself is the corresponding
-- measure on `ℕ`.
/-- Example 8.30: if `Z₁` and `Z₂` are independent Poisson random variables with parameters `λ₁`
and `λ₂`, then, whenever `P[Z₁ + Z₂ = n] > 0`, the conditional law of `Z₁` given `Z₁ + Z₂ = n`
is the binomial distribution with parameters `n` and `λ₁ / (λ₁ + λ₂)`, viewed as a measure on
`ℕ` via the canonical inclusion `Fin (n + 1) → ℕ`. -/
theorem condDistrib_poisson_left_given_sum_eq_binomial
    (n : ℕ)
    (hn : P.map (fun ω ↦ Z1 ω + Z2 ω) {n} ≠ 0) :
    condDistrib Z1 (fun ω ↦ Z1 ω + Z2 ω) P n =
      ((PMF.binomial (lam1 / (lam1 + lam2)) (poisson_split_parameter_le_one lam1 lam2) n).map
        Fin.val).toMeasure := sorry

/-- The singleton-mass view of `condDistrib_poisson_left_given_sum_eq_binomial`. -/
theorem condDistrib_poisson_left_given_sum_apply_singleton
    (n k : ℕ) (hk : k ≤ n)
    (hn : P.map (fun ω ↦ Z1 ω + Z2 ω) {n} ≠ 0) :
    condDistrib Z1 (fun ω ↦ Z1 ω + Z2 ω) P n {k} =
      PMF.binomial (lam1 / (lam1 + lam2)) (poisson_split_parameter_le_one lam1 lam2) n
        (Fin.ofNat (n + 1) k) := sorry

end PoissonSplit
