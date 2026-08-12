import Mathlib
import ProbabilityTheory_Klenke_2020.Chap16.Definition_16_26

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

/-- The two-sided tail probability `x ↦ P(|X| ≥ x)` of a real probability law. -/
def absTail (μ : ProbabilityMeasure ℝ) (x : ℝ) : ℝ :=
  ((μ : Measure ℝ) {y : ℝ | x ≤ |y|}).toReal

-- Proof sketch: unfold `absTail`; it is the real-valued mass of the event `{|X| ≥ x}`.
/-- The right-tail probability `x ↦ P(X ≥ x)` of a real probability law. -/
def rightTail (μ : ProbabilityMeasure ℝ) (x : ℝ) : ℝ :=
  ((μ : Measure ℝ) (Set.Ici x)).toReal

-- Proof sketch: this is the owner predicate `μ ∈ domainOfAttraction ν` plus the requirement that
-- the limiting law `ν` is non-Dirac, rewritten in the source's `n + 1` indexing convention.
/-- A real probability law lies in the domain of attraction of some nondegenerate distribution
exactly when it admits positive norming constants, a centering sequence, and weak convergence of
its normalized convolution laws to a non-Dirac limit. -/
theorem isInDomainOfAttraction_iff_exists_tendsto_normalizedConvolutionLaw
    (μ : ProbabilityMeasure ℝ) :
    (∃ ν : ProbabilityMeasure ℝ, (∀ x : ℝ, ν ≠ diracProba x) ∧ μ ∈ domainOfAttraction ν) ↔
      ∃ ν : ProbabilityMeasure ℝ,
        (∀ x : ℝ, ν ≠ diracProba x) ∧
          ∃ a b : ℕ+ → ℝ,
            (∀ n : ℕ+, 0 < a n) ∧
              Tendsto (fun n : ℕ+ ↦ normalizedConvolutionLaw μ a b n) atTop (𝓝 ν) := by
  constructor
  · rintro ⟨ν, hν, hμ⟩
    rcases (mem_domainOfAttraction_iff ν μ).1 hμ with ⟨a, b, ha, ht⟩
    exact ⟨ν, hν, a, b, ha, ht⟩
  · rintro ⟨ν, hν, a, b, ha, ht⟩
    exact ⟨ν, hν, (mem_domainOfAttraction_iff ν μ).2 ⟨a, b, ha, ht⟩⟩

/-- Condition `(16.29)` for a law on `ℝ`: the two-sided tail is regularly varying with index
`-α`. -/
def HasTailRegularVariation (μ : ProbabilityMeasure ℝ) (α : ℝ) : Prop :=
  ∀ c : ℝ, 0 < c →
    Tendsto (fun x : ℝ ↦ absTail μ (c * x) / absTail μ x) atTop (𝓝 (c ^ (-α)))

/-- The positive-tail share has a limit if the ratio `P(X ≥ x) / P(|X| ≥ x)` converges as
`x → ∞`. -/
def HasPositiveTailShareLimit (μ : ProbabilityMeasure ℝ) : Prop :=
  ∃ p : ℝ, Tendsto (fun x : ℝ ↦ rightTail μ x / absTail μ x) atTop (𝓝 p)

-- Proof sketch: identify any nondegenerate weak limit of normalized convolution powers as a
-- stable law, then apply the tail characterization of stable domains of attraction to obtain an
-- index `α ∈ (0,2]` for which the two-sided tail is regularly varying.
/-- Theorem 16.28 (1): source clause (i). If a real probability law is in the domain of
attraction of some distribution, then its two-sided tail satisfies `(16.29)` for some
`α ∈ (0, 2]`. -/
theorem exists_tailRegularVariation_index_of_isInDomainOfAttraction
    {μ : ProbabilityMeasure ℝ}
    (hμ : ∃ ν : ProbabilityMeasure ℝ, (∀ x : ℝ, ν ≠ diracProba x) ∧ μ ∈ domainOfAttraction ν) :
    ∃ α ∈ Set.Ioc (0 : ℝ) 2, HasTailRegularVariation μ α := sorry

-- Proof sketch: for the Gaussian index `α = 2`, use `(16.29)` to construct an admissible
-- norming sequence for the convolution powers; the non-Dirac assumption rules out degenerate
-- collapse of the normalized laws.
/-- Theorem 16.28 (2): source clause (ii). In the case `α = 2`, if the law is not concentrated at
one point and `(16.29)` holds, then the law lies in the domain of attraction of some
distribution. -/
theorem isInDomainOfAttraction_of_not_dirac_of_tailRegularVariation_index_two
    {μ : ProbabilityMeasure ℝ} (hμ_nontrivial : ∀ x : ℝ, μ ≠ diracProba x)
    (hμ_tail : HasTailRegularVariation μ 2) :
    ∃ ν : ProbabilityMeasure ℝ, (∀ x : ℝ, ν ≠ diracProba x) ∧ μ ∈ domainOfAttraction ν := sorry

-- Proof sketch: for `0 < α < 2`, the stable domain-of-attraction criterion is equivalent to the
-- combination of the regularly varying two-sided tail `(16.29)` and existence of the positive-tail
-- share limit `(16.30)`.
/-- Theorem 16.28 (3): source clause (iii). For `α ∈ (0, 2)`, a real probability law lies in the
domain of attraction of some distribution if and only if `(16.29)` holds with index `α` and the
limit in `(16.30)` exists. -/
theorem isInDomainOfAttraction_iff_tailRegularVariation_and_positiveTailShareLimit
    {μ : ProbabilityMeasure ℝ} {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) :
    (∃ ν : ProbabilityMeasure ℝ, (∀ x : ℝ, ν ≠ diracProba x) ∧ μ ∈ domainOfAttraction ν) ↔
      HasTailRegularVariation μ α ∧ HasPositiveTailShareLimit μ := sorry

end MeasureTheory.ProbabilityMeasure
