import Mathlib
import AchimKlenkeLean.Items.Chap12.Example_12_3
import AchimKlenkeLean.Items.Chap12.Theorem_12_26

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

private noncomputable def boolProbabilityParameter (ξ : ProbabilityMeasure Bool) : unitInterval :=
  ⟨(ξ : Measure Bool).real {true}, ⟨measureReal_nonneg, measureReal_le_one⟩⟩

-- Proof sketch: apply the chapter-owner de Finetti theorem to the `Bool`-valued exchangeable
-- sequence `X`, then convert the resulting directing `Bool`-valued probability measure into its
-- canonical Bernoulli parameter `ξ ↦ ξ{true} ∈ [0,1]`; this is exactly the bridge encoded by
-- `IsConditionallyBernoulliIID`.
/-- Example 12.28: every exchangeable `{0,1}`-valued sequence is conditionally i.i.d. Bernoulli
with a random parameter `Y : Ω → [0,1]`; equivalently, for each finite set of coordinates, the
conditional probability that all selected coordinates equal `1` is the corresponding power of
`Y`. -/
theorem exists_conditionalBernoulliParameter_of_isExchangeable
    {X : ℕ → Ω → Bool} (hX : IsExchangeable X μ) (hX_meas : ∀ n, Measurable (X n)) :
    ∃ Y : Ω → unitInterval,
      IsConditionallyBernoulliIID Y X μ := by
  have hXi :=
    (isExchangeable_iff_exists_directingProbabilityMeasure hX_meas).mp hX
  rcases hXi with ⟨xiInf, _, hxiInf⟩
  refine ⟨fun ω ↦ boolProbabilityParameter (xiInf ω), ?_⟩
  sorry
