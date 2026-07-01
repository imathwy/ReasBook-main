import Mathlib
import AchimKlenkeLean.Items.Chap16.Definition_16_20

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped Topology

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

/-- The law of the normalized sum `(Sₙ - b n) / a n`, realized as the affine image of the `n`th
convolution power of `ν` with derived multiplier `(a n)⁻¹` and shift `-(a n)⁻¹ * b n`. This is
the chapter's owner object behind domains of attraction. -/
abbrev normalizedConvolutionLaw
    (ν : ProbabilityMeasure ℝ) (a b : ℕ+ → ℝ) (n : ℕ+) : ProbabilityMeasure ℝ :=
  map (ν ^ (n : ℕ)) (measurable_affineMap (a n)⁻¹ (-(a n)⁻¹ * b n)).aemeasurable

/-- Definition 16.26: the domain of attraction `Dom(μ)` is the set of probability laws `ν` on
`ℝ` for which some positive affine normalization of the convolution powers of `ν` converges weakly
to `μ`. -/
def domainOfAttraction (μ : ProbabilityMeasure ℝ) : Set (ProbabilityMeasure ℝ) :=
  { ν | ∃ a b : ℕ+ → ℝ,
      (∀ n : ℕ+, 0 < a n) ∧
        Tendsto (fun n : ℕ+ ↦ normalizedConvolutionLaw ν a b n) atTop (𝓝 μ) }

/-- Membership in `domainOfAttraction μ` is equivalent to the existence of positive scaling and
centering sequences whose affinely normalized convolution powers converge weakly to `μ`. -/
theorem mem_domainOfAttraction_iff (μ ν : ProbabilityMeasure ℝ) :
    ν ∈ domainOfAttraction μ ↔
      ∃ a b : ℕ+ → ℝ,
        (∀ n : ℕ+, 0 < a n) ∧
          Tendsto (fun n : ℕ+ ↦ normalizedConvolutionLaw ν a b n) atTop (𝓝 μ) := by
  rfl

/-- Definition 16.26: for a probability law `μ` and exponent `α`, the normal domain of attraction
consists of those laws whose convolution powers converge to `μ` after centering and division by
`n^(1 / α)`. When `μ` is broadly stable with index `α`, this is the textbook normal domain of
attraction. -/
def normalDomainOfAttraction (μ : ProbabilityMeasure ℝ) (α : ℝ) :
    Set (ProbabilityMeasure ℝ) :=
  { ν | ∃ d : ℕ+ → ℝ,
      Tendsto
        (fun n : ℕ+ ↦
          normalizedConvolutionLaw ν (fun n ↦ (n : ℝ) ^ (1 / α)) d n)
        atTop
        (𝓝 μ) }

/-- Every law in the normal domain of attraction of `μ` lies in the domain of attraction of `μ`. -/
theorem normalDomainOfAttraction_subset_domainOfAttraction
    (μ : ProbabilityMeasure ℝ) (α : ℝ) :
    normalDomainOfAttraction μ α ⊆ domainOfAttraction μ := by
  intro ν hν
  rcases hν with ⟨d, hd⟩
  refine ⟨fun n ↦ (n : ℝ) ^ (1 / α), d, ?_, hd⟩
  intro n
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast n.pos
  exact Real.rpow_pos_of_pos hn (1 / α)

end MeasureTheory.ProbabilityMeasure
