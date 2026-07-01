import AchimKlenkeLean.Items.Chap17.Theorem_17_56

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

universe u v

section LawLevel

variable {E : Type u} [MeasurableSpace E]

/- Exercise 13.2.15 is `source-facing`: the textbook assumption is a tail-first-moment condition
for one fixed observable `f` tested against a sequence of laws `μₙ`. The `core/canonical` owner
used downstream is `MeasureTheory.UniformIntegrable` on a single measure space. The local
predicate below is therefore the law-level `bridge/view`, while the bridge theorem records the
canonical reformulation through any common-space realization with the same one-dimensional laws. -/
/-- A real-valued function is uniformly integrable with respect to a sequence of probability
measures when the supremum of its tail first moments tends to `0`, written in the textbook form as
an infimum over positive cutoffs. -/
def uniformlyIntegrableWithRespectToProbabilitySequence
    (f : E → ℝ) (μs : ℕ → ProbabilityMeasure E) : Prop :=
  (⨅ a : {a : ℝ // 0 < a},
      ⨆ n : ℕ,
        ∫⁻ x in {x | a.1 < |f x|}, ENNReal.ofReal |f x| ∂(μs n : Measure E)) = 0

-- Proof sketch: compare the tail integrals under `μₙ` with those of any common-space real
-- sequence having the same one-dimensional laws, using `IdentDistrib` to transport the relevant
-- truncated first moments. In the exercise proof, the needed realization comes from a Skorohod
-- coupling of the pushforward laws, but that auxiliary convergence package is not part of the
-- bridge API itself.
/-- The law-level tail criterion for `f` along `μₙ` is equivalent to the canonical owner
predicate `MeasureTheory.UniformIntegrable` for any real sequence with the same one-dimensional
laws. -/
theorem uniformlyIntegrableWithRespectToProbabilitySequence_iff_uniformIntegrable_of_identDistrib
    {Ω : Type v} [MeasurableSpace Ω] {P : ProbabilityMeasure Ω}
    {f : E → ℝ} {μs : ℕ → ProbabilityMeasure E} {Ys : ℕ → Ω → ℝ}
    (hYs : ∀ n, IdentDistrib (Ys n) f (P : Measure Ω) (μs n : Measure E)) :
    uniformlyIntegrableWithRespectToProbabilitySequence f μs ↔
      UniformIntegrable Ys 1 (P : Measure Ω) := sorry

end LawLevel

section

variable {E : Type u} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]

-- Proof sketch: apply Exercise 13.2.14 to the pushforward probability measures `μₙ ∘ f⁻¹` on
-- `ℝ`, then use
-- `uniformlyIntegrableWithRespectToProbabilitySequence_iff_uniformIntegrable_of_identDistrib`
-- with the induced `IdentDistrib` family from the Skorohod realization to pass to the owner
-- predicate `UniformIntegrable` on the coupling space. The one-dimensional result yields
-- integrability of the limit law and convergence of first moments, which translate back to
-- integrability of `f` under `μ` and convergence of `∫ f dμₙ`.
/-- Exercise 13.2.15: if `f` is continuous, uniformly integrable with respect to the probability
measures `μₙ`, and `μₙ` converges weakly to `μ`, then `f` is integrable under `μ` and the
integrals `∫ f dμₙ` converge to `∫ f dμ`. -/
theorem integrable_and_tendsto_integral_of_continuous_of_uniformlyIntegrableProbabilitySequence
    {f : E → ℝ} {μs : ℕ → ProbabilityMeasure E} {μ : ProbabilityMeasure E}
    (hf_cont : Continuous f)
    (hf_ui : uniformlyIntegrableWithRespectToProbabilitySequence f μs)
    (hμs : Tendsto μs atTop (𝓝 μ)) :
    Integrable f (μ : Measure E) ∧
      Tendsto (fun n ↦ ∫ x, f x ∂(μs n : Measure E)) atTop
        (𝓝 (∫ x, f x ∂(μ : Measure E))) := sorry

end
