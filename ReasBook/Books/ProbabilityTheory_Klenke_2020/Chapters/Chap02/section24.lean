import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_2_24 (from Items/Chap02) -/
open MeasureTheory ProbabilityTheory

universe u v

variable {Ω : Type u} {ι : Type v} [Fintype ι] [Nonempty ι]

/-- The pointwise maximum of a finite nonempty family of real-valued random variables. -/
noncomputable def sampleMaximum (X : ι → Ω → ℝ) : Ω → ℝ :=
  fun ω ↦ Finset.univ.sup' Finset.univ_nonempty (fun i ↦ X i ω)

/-- The pointwise minimum of a finite nonempty family of real-valued random variables. -/
noncomputable def sampleMinimum (X : ι → Ω → ℝ) : Ω → ℝ :=
  fun ω ↦ Finset.univ.inf' Finset.univ_nonempty (fun i ↦ X i ω)

section

variable [MeasurableSpace Ω] (P : Measure Ω) (X : ι → Ω → ℝ) (θ : ι → ℝ)
variable (h_indep : iIndepFun X P) (h_exp : ∀ i, HasLaw (X i) (expMeasure (θ i)) P)
variable (hθ : ∀ i, 0 < θ i)

-- Proof sketch: identify the event `{sampleMaximum X ≤ x}` with the intersection of the events
-- `{X i ≤ x}`, use independence to factor its probability into a product, and identify each
-- marginal factor with the corresponding exponential cdf.
/-- The cumulative distribution function of the maximum of a finite independent family of
exponential random variables with positive rates `θ i` is the product of the marginal exponential
cumulative distribution functions. -/
theorem cdf_sampleMaximum_eq_prod_exp
    (x : ℝ) :
    cdf (P.map (sampleMaximum X)) x = ∏ i, cdf (expMeasure (θ i)) x := sorry

-- Proof sketch: rewrite `{sampleMinimum X ≤ x}` as the complement of the event that every
-- coordinate is larger than `x`, use independence to multiply the exponential survival
-- probabilities, and identify the resulting expression with the cdf of the exponential law of
-- rate `∑ i, θ i`.
/-- The cumulative distribution function of the minimum of a finite independent family of
exponential random variables with positive rates `θ i` agrees with the exponential cdf of rate
`∑ i, θ i`. -/
theorem cdf_sampleMinimum_eq_exp
    (x : ℝ) :
    cdf (P.map (sampleMinimum X)) x = cdf (expMeasure (∑ i, θ i)) x := sorry

-- Proof sketch: a probability law on `ℝ` is determined by its cdf, so the previous cdf identity
-- identifies the law of `sampleMinimum X` with `expMeasure (∑ i, θ i)`.
/-- Example 2.24: The minimum of a finite independent family of exponentially distributed real
random variables with rates `θ i` is exponentially distributed with rate `∑ i, θ i`. -/
theorem sampleMinimum_hasLaw_expMeasure_sum :
    HasLaw (sampleMinimum X) (expMeasure (∑ i, θ i)) P := sorry

end
