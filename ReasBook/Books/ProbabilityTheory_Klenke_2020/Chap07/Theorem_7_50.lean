import ProbabilityTheory_Klenke_2020.Chap07.Lemma_7_49

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ContinuousLinearMap ENNReal

noncomputable section

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

local instance : Fact (1 ≤ conjExponent p) :=
  ⟨HolderConjugate.one_le (conjExponent p) p⟩

section Duality

variable [SigmaFinite μ]
variable [Fact (p < ∞)]

omit [SigmaFinite μ] [Fact (p < ∞)] in
/-- Helper for Theorem 7.50: pairing against the indicator of a finite-measure set recovers the
corresponding set integral. -/
lemma lpPairing_indicatorConstLp_one
    (f : Lp ℝ (conjExponent p) μ) {s : Set Ω} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    (mul ℝ ℝ).lpPairing μ (conjExponent p) p f
        (indicatorConstLp p hs hμs (1 : ℝ)) = ∫ x in s, f x ∂μ := by
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  calc
    ∫ x, f x * indicatorConstLp p hs hμs (1 : ℝ) x ∂μ = ∫ x, s.indicator f x ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards
        [show (indicatorConstLp p hs hμs (1 : ℝ) : Ω → ℝ) =ᵐ[μ] s.indicator fun _ ↦ (1 : ℝ) from
          indicatorConstLp_coeFn] with x hx
      simp [hx, Set.indicator]
    _ = ∫ x in s, f x ∂μ := integral_indicator hs

omit [SigmaFinite μ] [Fact (p < ∞)] in
/-- Helper for Theorem 7.50: every continuous linear functional on `L^p(μ)` satisfies the
indicator estimate used to build the localized signed measures in the surjectivity argument. -/
lemma indicator_functional_bound
    (F : StrongDual ℝ (Lp ℝ p μ)) {s : Set Ω} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    ‖F (indicatorConstLp p hs hμs (1 : ℝ))‖ ≤ ‖F‖ * μ.real s ^ (1 / p.toReal) := by
  calc
    ‖F (indicatorConstLp p hs hμs (1 : ℝ))‖
      ≤ ‖F‖ * ‖indicatorConstLp p hs hμs (1 : ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖F‖ * (‖(1 : ℝ)‖ * μ.real s ^ (1 / p.toReal)) := by
      gcongr
      exact
        (show ‖indicatorConstLp p hs hμs (1 : ℝ)‖
            ≤ ‖(1 : ℝ)‖ * μ.real s ^ (1 / p.toReal) from norm_indicatorConstLp_le)
    _ = ‖F‖ * μ.real s ^ (1 / p.toReal) := by simp

-- Proof sketch: injectivity follows from `lpDualityMap_isometry`. For surjectivity, represent a
-- continuous linear functional on `L^p(μ)` by the signed measure `ν(A) = F(1_A)`, apply the
-- Radon-Nikodym theorem to obtain a density `f`, prove `f ∈ L^{p'}(μ)` by the usual `p = 1` and
-- `1 < p < ∞` cases, and then identify the resulting integral functional with `F` on a dense
-- class of simple functions.
/-- Theorem 7.50: on a sigma-finite measure space, if `1 ≤ p < ∞` and `q` satisfies
`1 / p + 1 / q = 1`, then the canonical map `κ : L^q(μ) → (L^p(μ))'` is bijective. Here `q` is
represented by `ENNReal.conjExponent p`. -/
theorem lpDualityMap_bijective :
    Function.Bijective
      ((mul ℝ ℝ).lpPairing μ (conjExponent p) p :
        Lp ℝ (conjExponent p) μ → StrongDual ℝ (Lp ℝ p μ)) := by
  have hκ :
      Isometry
        ((mul ℝ ℝ).lpPairing μ (conjExponent p) p :
          Lp ℝ (conjExponent p) μ → StrongDual ℝ (Lp ℝ p μ)) :=
    lpDualityMap_isometry
  constructor
  · exact hκ.injective
  · intro F
    -- TODO: localize `A ↦ F(1_A)` to finite-measure pieces, construct the corresponding signed
    -- measures, apply Radon-Nikodym on the sigma-finite exhaustion, and then extend the indicator
    -- formula from `lpPairing_indicatorConstLp_one` to all of `L^p(μ)` by density.
    sorry

end Duality
