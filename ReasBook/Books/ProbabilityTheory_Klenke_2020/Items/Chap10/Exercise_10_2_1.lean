import ProbabilityTheory_Klenke_2020.Items.Chap10.Example_10_2

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

universe u

section

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
variable {ℱ : Filtration ℕ mΩ} [SigmaFiniteFiltration μ ℱ]
variable {X : ℕ → Ω → ℝ} {τ : Ω → ℕ}

/-
Exercise 10.2.1 is `source-facing`: it records the stopped identities for the canonical square
variation from Example 10.2. The owner abstraction in the chapter is
`ProbabilityTheory.IsSquareVariationProcess`, while the canonical bridge/view is
`predictablePart_sq_isSquareVariationProcess`. Since the source refers to the canonical square
variation itself rather than an arbitrary square-variation witness, the main statements stay
formulated with the predictable compensator of the squared process.
-/
local notation "τ∞" => fun ω ↦ (τ ω : ℕ∞)
local notation "squareProcess" => fun n ω ↦ (X n ω) ^ 2
local notation "squareVariation" => predictablePart squareProcess ℱ μ

-- Proof sketch: apply optional sampling to the square-integrable martingale
-- `fun n ω ↦ X n ω ^ 2 - predictablePart squareProcess ℱ μ n ω`, use the integrability
-- of the stopped predictable part to justify taking expectations at the finite stopping time `τ`,
-- and rearrange the resulting identity to isolate the second moment of `X_τ - X_0`.
/-- Exercise 10.2.1 (1): Part (i), if the stopped canonical square variation `⟨X⟩_τ` is
integrable, then the expected squared increment of the martingale up to the finite stopping time
`τ` equals the expectation of the stopped square variation. -/
theorem expectation_stopped_sq_sub_eq_expectation_stopped_squareVariation
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (fun ω ↦ (X n ω) ^ 2) μ)
    (hτ : IsStoppingTime ℱ τ∞) (hAτ : Integrable (stoppedValue squareVariation τ∞) μ) :
    μ[fun ω ↦ (stoppedValue X τ∞ ω - X 0 ω) ^ 2] = μ[stoppedValue squareVariation τ∞] := sorry

-- Proof sketch: use the same stopped-square-variation argument as in clause (1) to obtain
-- uniform integrability of the stopped martingale, then apply optional stopping for finite
-- stopping times to conclude that the expectation is preserved.
/-- Exercise 10.2.1 (2): Part (i), under the same integrability hypothesis on `⟨X⟩_τ`, the
expected value of the martingale at the finite stopping time `τ` agrees with the initial
expectation. -/
theorem expectation_stopped_martingale_eq_initial_of_squareVariation_integrable
    (hX : Martingale X ℱ μ) (hXsq : ∀ n, Integrable (fun ω ↦ (X n ω) ^ 2) μ)
    (hτ : IsStoppingTime ℱ τ∞) (hAτ : Integrable (stoppedValue squareVariation τ∞) μ) :
    μ[stoppedValue X τ∞] = μ[X 0] := sorry

end

-- Proof sketch: construct a square-integrable martingale on a filtered probability space together
-- with a finite stopping time whose stopped square variation is not integrable; then compute the
-- two sides of the identities in (10.7) and verify that neither equality holds in that example.
/-- Exercise 10.2.1 (3): Part (ii), if the stopped square variation fails to be integrable, then
there exists a square-integrable martingale and a finite stopping time for which both identities
from `(10.7)` fail. -/
theorem exists_counterexample_stopped_squareVariation_nonintegrable :
    ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
      (ℱ : Filtration ℕ mΩ) (_ : SigmaFiniteFiltration μ ℱ)
      (X : ℕ → Ω → ℝ) (τ : Ω → ℕ),
        let tauInf : Ω → ℕ∞ := fun ω ↦ (τ ω : ℕ∞)
        let squareVariation : ℕ → Ω → ℝ := predictablePart (fun n ω ↦ (X n ω) ^ 2) ℱ μ
        Martingale X ℱ μ ∧
          (∀ n, Integrable (fun ω ↦ (X n ω) ^ 2) μ) ∧
          IsStoppingTime ℱ tauInf ∧
          ¬ Integrable (stoppedValue squareVariation tauInf) μ ∧
          μ[fun ω ↦ (stoppedValue X tauInf ω - X 0 ω) ^ 2] ≠
            μ[stoppedValue squareVariation tauInf] ∧
          μ[stoppedValue X tauInf] ≠ μ[X 0] := sorry
