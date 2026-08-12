import ProbabilityTheory_Klenke_2020.Chap13.Definition_13_4
import ProbabilityTheory_Klenke_2020.Chap13.Definition_13_17

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.FiniteMeasure
open scoped Topology

universe u v w

section

variable {E₁ : Type u} {E₂ : Type v}
variable [MeasurableSpace E₁] [MetricSpace E₁] [BorelSpace E₁]
variable [MeasurableSpace E₂] [MetricSpace E₂] [BorelSpace E₂]

-- Proof sketch: use the bounded-measurable test-function clause of
-- `FiniteMeasure.portmanteau_subprobability_tfae`; for each bounded continuous `f` on `E₂`, the
-- composition `f ∘ φ` is bounded and measurable on `E₁`, and its discontinuity set is contained in
-- the discontinuity set of `φ`.
/-- Theorem 13.25 (1): if subprobability finite measures on `E₁` converge weakly to `μ` and the
discontinuity set of the measurable map `φ` is `μ`-null, then their pushforwards by `φ` converge
weakly to the pushforward of `μ`. -/
theorem finiteMeasure_tendsto_map_of_null_discontinuitySet
    (μs : ℕ → FiniteMeasure E₁) (μ : FiniteMeasure E₁) (φ : E₁ → E₂) (hφ : Measurable φ)
    (hμ : μ.mass ≤ 1) (hμs : ∀ n, (μs n).mass ≤ 1)
    (hdisc : μ {x : E₁ | ¬ ContinuousAt φ x} = 0) (hweak : Tendsto μs atTop (𝓝 μ)) :
    Tendsto (fun n ↦ (μs n).map φ) atTop (𝓝 (μ.map φ)) := sorry

end

section

variable {Ω : Type u} {E₁ : Type v} {E₂ : Type w}
variable [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable [MeasurableSpace E₁] [MetricSpace E₁] [BorelSpace E₁]
variable [MeasurableSpace E₂] [MetricSpace E₂] [BorelSpace E₂]

-- Proof sketch: pass to the laws of `X n` and `X`, apply the finite-measure statement of the
-- continuous mapping theorem to those laws, and rewrite the resulting pushed-forward laws as the
-- laws of `φ ∘ X n` and `φ ∘ X`.
/-- Theorem 13.25 (2): if `X n` converges in distribution to `X` and `X` hits the discontinuity
set of the measurable map `φ` only on a `P`-null event, then `φ ∘ X n` converges in distribution
to `φ ∘ X`. -/
theorem tendstoInDistribution_comp_of_preimage_null_discontinuitySet
    {Xn : ℕ → Ω → E₁} {X : Ω → E₁} {φ : E₁ → E₂} (hφ : Measurable φ)
    (hdisc : P (X ⁻¹' {x : E₁ | ¬ ContinuousAt φ x}) = 0)
    (hX : TendstoInDistribution Xn atTop X (fun _ ↦ P) P) :
    TendstoInDistribution (fun n ↦ φ ∘ Xn n) atTop (φ ∘ X) (fun _ ↦ P) P := sorry

end
