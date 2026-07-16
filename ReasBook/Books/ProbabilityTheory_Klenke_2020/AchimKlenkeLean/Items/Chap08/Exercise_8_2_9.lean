import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap08.Example_8_31

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

-- Proof sketch: identify the conditional expectation of `h ∘ X` given `Y` with the integral of
-- `h` against the regular conditional distribution of `X` given `Y`, then use the joint-density
-- hypothesis to compute that conditional distribution by disintegrating the joint law of `(X, Y)`
-- along the second coordinate and normalizing by the marginal density of `Y`.
/-- Exercise 8.2.9 (1): If `X` and `Y` have joint Lebesgue density `f` and `h(X)` is integrable,
then the conditional expectation of `h(X)` given `Y` is almost surely the ratio of the `x`-integral
of `h(x) f(x, Y)` and the marginal density integral of `Y`. -/
theorem condExp_transform_given_right_ae_eq_joint_density_ratio
    {X Y : Ω → ℝ} {f : ℝ → ℝ → ENNReal} {h : ℝ → ℝ}
    (hf : Measurable fun z : ℝ × ℝ ↦ f z.1 z.2)
    (h_joint : HasLaw (fun ω ↦ (X ω, Y ω))
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
        fun z : ℝ × ℝ ↦ f z.1 z.2) P)
    (hh_meas : Measurable h) (hh_int : Integrable (fun ω ↦ h (X ω)) P) :
    P[h ∘ X | MeasurableSpace.comap Y (borel ℝ)] =ᵐ[P]
      fun ω ↦
        (∫ x, h x * (f x (Y ω)).toReal) /
          (first_marginal_density (fun y x ↦ f x y) (Y ω)).toReal := sorry

section IidExp

variable {X Y : Ω → ℝ} {θ : ℝ}

local notation "mSum" => MeasurableSpace.comap (X + Y) (borel ℝ)

-- Proof sketch: compute the conditional law of `X` given `X + Y = s` from the joint exponential
-- density in the setting of Exercise 8.2.9 (2). It is the conditioned Lebesgue measure on
-- `[0, s]`.
private theorem condDistrib_left_given_sum_of_iid_exp_ae_eq_uniform_interval_aux
    (hX : HasLaw X (expMeasure θ) P) (hY : HasLaw Y (expMeasure θ) P) (hXY : X ⟂ᵢ[P] Y) :
    ∀ᵐ s ∂P.map (X + Y), condDistrib X (X + Y) P s = volume[|Set.Icc 0 s] := sorry

-- Proof sketch: the pair `(X, Y)` is exchangeable because `X` and `Y` are independent with the
-- same exponential law. Hence the conditional expectations of `X` and `Y` given `X + Y` agree
-- almost surely. Summing them and using that `X + Y` is measurable with respect to its own
-- generated σ-algebra yields `2 * E[X | X + Y] = X + Y`.
/-- Exercise 8.2.9 (2), expectation consequence: if `X` and `Y` are independent and both have
exponential law with common rate `θ`, then the conditional expectation of `X` given `X + Y` is
almost surely half of the sum. -/
theorem condExp_left_given_sum_of_iid_exp_ae_eq_half_sum
    (hX : HasLaw X (expMeasure θ) P) (hY : HasLaw Y (expMeasure θ) P) (hXY : X ⟂ᵢ[P] Y) :
    P[X | mSum] =ᵐ[P] (X + Y) / 2 := sorry

-- Proof sketch: evaluate the auxiliary conditional-distribution formula on the event `(-∞, x]`. The
-- conditioned Lebesgue measure on `[0, s]` gives mass `1` when `s ≤ x` and `x / s` when `s > x`.
/-- Exercise 8.2.9 (3): if `X` and `Y` are independent and both have
exponential law with common rate `θ`, then for every `x ≥ 0` the conditional probability of the
event `X ≤ x` given `X + Y` is almost surely the truncated-uniform cdf on the random interval
`[0, X + Y]`. -/
theorem condProb_left_le_given_sum_of_iid_exp_ae_eq {x : ℝ} (hx : 0 ≤ x)
    (hX : HasLaw X (expMeasure θ) P) (hY : HasLaw Y (expMeasure θ) P) (hXY : X ⟂ᵢ[P] Y) :
    P⟦X ⁻¹' Set.Iic x | mSum⟧ =ᵐ[P]
      fun ω ↦ if X ω + Y ω ≤ x then 1 else x / (X ω + Y ω) := sorry

end IidExp
