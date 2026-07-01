import Mathlib
import AchimKlenkeLean.Items.Chap10.Definition_10_3

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} {m0 : MeasurableSpace Ω}
variable {μ : Measure Ω} {ℱ : Filtration ℕ m0}

section

variable {X : ℕ → Ω → ℝ}

local notation "squareProcess" => fun n ω ↦ X n ω ^ 2

-- Proof sketch: expand the predictable compensator of the squared process and rewrite each
-- squared-process increment `(X (i + 1))^2 - (X i)^2` using the martingale identity so that only
-- the conditional expectation of the squared increment remains; the canonical `condExp` API makes
-- this an almost-everywhere identity at each fixed time.
/-- Theorem 10.4 (1): For a square-integrable discrete-time martingale, the square variation
process `⟨X⟩` realized by the predictable part of the squared process satisfies formula (10.2)
almost everywhere at each time. -/
theorem predictablePart_sq_eq_sum_condExp_sq_increment
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (squareProcess n) μ) :
    ∀ n, ⟨X⟩[ℱ, μ] n =ᵐ[μ]
      fun ω ↦ ∑ i ∈ Finset.range n, μ[(fun ω ↦ (X (i + 1) ω - X i ω) ^ 2) | ℱ i] ω := sorry

/-- At each fixed time, Theorem 10.4 (1) is an almost-everywhere identity. -/
theorem squareVariation_eq_sum_condExp_sq_increment
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (squareProcess n) μ) (n : ℕ) :
    ⟨X⟩[ℱ, μ] n =ᵐ[μ]
      fun ω ↦ ∑ i ∈ Finset.range n, μ[(fun ω ↦ (X (i + 1) ω - X i ω) ^ 2) | ℱ i] ω := by
  simpa using predictablePart_sq_eq_sum_condExp_sq_increment hX hXsq n

-- Proof sketch: use the almost-everywhere identity from Theorem 10.4 (1) and linearity of
-- expectation to
-- rewrite the expectation of the square variation as a sum of second moments of the martingale
-- increments, then identify that sum with the variance of `X n - X 0` on the probability space.
/-- Theorem 10.4 (2): For a square-integrable discrete-time martingale, the expectation of the
square variation at time `n` equals the variance of the martingale increment `X n - X 0`. -/
theorem squareVariation_expectation_eq_variance [IsProbabilityMeasure μ]
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (squareProcess n) μ) (n : ℕ) :
    μ[⟨X⟩[ℱ, μ] n] = Var[fun ω ↦ X n ω - X 0 ω; μ] := sorry

end
