import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_11_18 (from Items/Chap11) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

noncomputable section

variable {Ω : Type u}

/- Lemma 11.18 is `source-facing`: it is about the normalized branching population
`W_n = Z_n / m^n`. Its `core/canonical` owners are the martingale API for
`Filtration.natural Z hZ_sm` and the discrete-time constructor `martingale_nat`. The abbreviation
below is only the minimal `bridge/view` layer needed to keep the textbook notation reusable in the
later branching-process items of this chapter. -/
/-- The normalized branching-process sequence `W_n = Z_n / m^n` attached to a real-valued
generation-size process `Z`. -/
abbrev branchingNormalizedProcess (Z : ℕ → Ω → ℝ) (m : ℝ) : ℕ → Ω → ℝ :=
  fun n ↦ (m ^ n)⁻¹ • Z n

variable [MeasurableSpace Ω]

section Martingale

variable {μ : Measure Ω} [IsFiniteMeasure μ]
variable {Z : ℕ → Ω → ℝ} {m : ℝ}

-- Proof sketch: show that the normalized process is strongly adapted to the natural filtration of
-- `Z`, use integrability of `Z_n / m^n`, and rewrite the assumed one-step conditional expectation
-- `E[Z_{n+1} | 𝓕_n] = m Z_n` into the normalized identity
-- `E[W_{n+1} | 𝓕_n] = W_n`; then apply `MeasureTheory.martingale_nat`.
/-- Lemma 11.18: if `W_n = Z_n / m^n` and the generation process satisfies the branching relation
`E[Z_{n+1} | 𝓕_n] = m Z_n` for the natural filtration of `Z`, then `W` is a martingale. -/
theorem branchingNormalizedProcess_martingale (hm : 0 < m)
    (hZ_sm : ∀ n, StronglyMeasurable (Z n)) (hZ_int : ∀ n, Integrable (Z n) μ)
    (h_step : ∀ n,
      μ[Z (n + 1) | (Filtration.natural Z hZ_sm) n] =ᵐ[μ] fun ω ↦ m * Z n ω) :
    Martingale (branchingNormalizedProcess Z m) (Filtration.natural Z hZ_sm) μ := sorry

end Martingale

section Expectation

variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {Z : ℕ → Ω → ℝ} {m : ℝ}

variable {ℱ : Filtration ℕ ‹MeasurableSpace Ω›} [SigmaFiniteFiltration μ ℱ]

-- Proof sketch: the martingale property makes the expectations of `W_n` constant in `n`. Since
-- `W_0 = Z_0 = 1` almost surely, `E[W_n] = 1`; multiplying by `m^n` gives `E[Z_n] = m^n`.
/-- If the normalized branching process is a martingale and the population starts from one
ancestor, then the expectations satisfy `E[Z_n] = m^n`. -/
theorem branchingProcess_expectation_eq_pow_mean (hm : 0 < m)
    (hW : Martingale (branchingNormalizedProcess Z m) ℱ μ) (hZ0 : ∀ᵐ ω ∂μ, Z 0 ω = 1)
    (n : ℕ) :
    μ[fun ω ↦ Z n ω] = m ^ n := sorry

end Expectation
