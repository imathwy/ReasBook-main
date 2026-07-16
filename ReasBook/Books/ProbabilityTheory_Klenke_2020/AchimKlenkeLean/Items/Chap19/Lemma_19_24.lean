import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap01.Definition_1_34
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap19.Definition_19_23

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal

universe u v

namespace ProbabilityTheory

attribute [local instance] Classical.propDecidable

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable {Ω : Type v} [MeasurableSpace Ω]

/- Layering for Lemma 19.24:
- `source-facing`: the finite-boundary effective conductances
  `conductance C x₁ * escapeToSetProbability P X x₁ A₀`.
- `core/canonical`: `conductance`, `escapeToSetProbability`, and
  `effectiveConductanceToInfinity C P X x₁` from Definition 19.23.
- `bridge/view`: `Set.DecreasesTo A₀ ∅` encodes the decreasing cofinite exhaustion used in the
  limit statement. -/

-- Proof sketch: unfold `effectiveConductanceToInfinity`; it is the infimum of the finite-boundary
-- conductances `conductance C x₁ * escapeToSetProbability P X x₁ A₀` over cofinite `A₀`
-- avoiding `x₁`. A decreasing exhaustion `A₀ n ↓ ∅` is cofinal in that family, and monotonicity
-- of `A₀ ↦ escapeToSetProbability P X x₁ A₀`, supplied by the owner theorem
-- `escapeToSetProbability_mono`, identifies the limit with the same infimum. The extra hypothesis
-- `conductance C x₁ < ∞` is the minimal condition ensuring multiplication by `conductance C x₁`
-- preserves that decreasing limit in `ℝ≥0∞`.
/-- Lemma 19.24: if `A₀ n` decreases to `∅`, each complement `A₀ nᶜ` is finite,
`x₁ ∉ A₀ n`, and `conductance C x₁ < ∞`, then the finite-boundary effective conductances from `x₁`
to `A₀ n` converge to the effective conductance from `x₁` to infinity. -/
theorem effectiveConductanceToInfinity_tendsto_of_decreasing_finite_complement
    {C : E → E → ℝ≥0∞} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E} {x₁ : E}
    {A₀ : ℕ → Set E}
    (hA₀ : Set.DecreasesTo A₀ (∅ : Set E))
    (hfinite : ∀ n, (A₀ n)ᶜ.Finite)
    (hx₁ : ∀ n, x₁ ∉ A₀ n)
    (hconductance : conductance C x₁ < ∞) :
    Tendsto (fun n ↦ conductance C x₁ * escapeToSetProbability P X x₁ (A₀ n)) atTop
      (nhds (effectiveConductanceToInfinity C P X x₁)) := sorry

end ProbabilityTheory
