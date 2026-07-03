import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

universe u

noncomputable section

/- Exercise 15.2.2 is `source-facing`: the public item is the existence statement. The relevant
owner abstractions are the canonical mathlib notions `PMF`, `IdentDistrib`, and `IndepFun`. The
finite-support data below stay private; they only record a concrete witness built from a
non-product coupling on `Fin 4 × Fin 4` whose row sums, column sums, and anti-diagonal sums agree
with the uniform product law. -/

private def sameSumCounterexampleWeight : (Fin 4 × Fin 4) → ℝ≥0
  | (0, 0) => 1 / 16
  | (0, 1) => 1 / 32
  | (0, 2) => 3 / 32
  | (0, 3) => 1 / 16
  | (1, 0) => 3 / 32
  | (1, 1) => 1 / 16
  | (1, 2) => 1 / 32
  | (1, 3) => 1 / 16
  | (2, 0) => 1 / 32
  | (2, 1) => 3 / 32
  | (2, 2) => 1 / 16
  | (2, 3) => 1 / 16
  | (_, _) => 1 / 16

private theorem sameSumCounterexampleWeight_sum :
    (∑ x : Fin 4 × Fin 4, sameSumCounterexampleWeight x) = 1 := by
  rw [Fintype.sum_prod_type]
  norm_num [sameSumCounterexampleWeight, Fin.sum_univ_four]

private def sameSumCounterexampleCoupling : PMF (Fin 4 × Fin 4) :=
  PMF.ofFintype (fun x ↦ (sameSumCounterexampleWeight x : ℝ≥0∞)) <| by
    change ((∑ x : Fin 4 × Fin 4, sameSumCounterexampleWeight x : ℝ≥0) : ℝ≥0∞) = 1
    exact_mod_cast sameSumCounterexampleWeight_sum

-- Proof sketch: let `(X, Y)` have the private coupling `sameSumCounterexampleCoupling` on
-- `Fin 4 × Fin 4`, and let `(X', Y')` have the uniform product law
-- `PMF.uniformOfFintype (Fin 4 × Fin 4)`. The row and column sums of the dependent coupling are
-- the same as the marginals of the uniform product law, so `X =ᵈ X'` and `Y =ᵈ Y'`. Its
-- anti-diagonal sums also match those of the uniform product law, so `X + Y =ᵈ X' + Y'`. Since
-- the uniform pair is a product law, `X'` and `Y'` are independent, while the dependent coupling
-- is not the product law, so `X` and `Y` are not independent.
/-- Exercise 15.2.2: there exists a probability space carrying real random variables `X`, `X'`,
`Y`, and `Y'` such that `X =ᵈ X'`, `Y =ᵈ Y'`, `X'` and `Y'` are independent,
`X + Y =ᵈ X' + Y'`, but `X` and `Y` are not independent. -/
theorem exists_same_sum_independent_copy_counterexample :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω),
      IsProbabilityMeasure μ ∧
      ∃ X X' Y Y' : Ω → ℝ,
        IdentDistrib X X' μ μ ∧
        IdentDistrib Y Y' μ μ ∧
        IndepFun X' Y' μ ∧
        IdentDistrib (fun ω ↦ X ω + Y ω) (fun ω ↦ X' ω + Y' ω) μ μ ∧
        ¬ IndepFun X Y μ := sorry
