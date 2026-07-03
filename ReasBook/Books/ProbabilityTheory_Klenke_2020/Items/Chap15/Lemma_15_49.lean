import ProbabilityTheory_Klenke_2020.Items.Chap15.Lemma_15_47
import ProbabilityTheory_Klenke_2020.Items.Chap15.Lemma_15_48

-- Declarations for this item will be appended below by the statement pipeline.

open Complex Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology

universe u

noncomputable section

variable {Ω : Type u} [MeasurableSpace Ω]

namespace RealRandomVariableArray

/- Lemma 15.49 has three layers in this file.

- `source-facing`: the textbook measures `μₙ(dx) = (1 + x^2)⁻¹ νₙ(dx)` and the two-term expression
  `∫ f_t(x) μₙ(dx) + i t ∫ (1 / x) μₙ(dx)`.
- `core/canonical`: the variance-weighted row laws `A.varianceWeightedRowLaw P n` from
  Lemma 15.48.
- `bridge/view`: rewriting the source expression as an integral against the canonical owner
  measure. -/

/-- The textbook measures `μₙ` from Lemma 15.49, obtained from the variance-weighted row measures
`νₙ` by multiplying with the canonical weight `(1 + x^2)⁻¹`. -/
def cltAuxiliaryMeasure (A : RealRandomVariableArray Ω) (P : Measure Ω) (n : ℕ) : Measure ℝ :=
  (A.varianceWeightedRowMeasure P n).withDensity
    (fun x ↦ ENNReal.ofReal ((1 + x ^ (2 : ℕ))⁻¹))

-- Proof sketch: rewrite the `f_t`-integral against `μₙ` directly using
-- `μₙ = (1 + x^2)⁻¹ νₙ`. For the singular term, first write
-- `1 / (x * (1 + x^2)) = 1 / x - x / (1 + x^2)` and then use centeredness of the array to cancel
-- the `∫ (1 / x) νₙ(dx)` contribution, leaving the bounded correction
-- `-x / (1 + x^2)` against the owner measure `νₙ`.
/-- The textbook two-term expression from Lemma 15.49 is canonically a single integral against the
variance-weighted owner measure `νₙ`. -/
theorem cltAuxiliaryMeasure_expression_eq_integral_varianceWeightedRowMeasure
    (A : RealRandomVariableArray Ω) (P : Measure Ω) [IsProbabilityMeasure P] [A.IsCentered P]
    (n : ℕ) (t : ℝ) :
    (∫ x, cltAuxiliaryFunction t x ∂A.cltAuxiliaryMeasure P n) +
        Complex.I * (t : ℂ) * (∫ x, (1 / (x : ℂ)) ∂A.cltAuxiliaryMeasure P n) =
      ∫ x,
        ((((1 + x ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) * cltAuxiliaryFunction t x +
          -Complex.I * (t : ℂ) * (((x / (1 + x ^ (2 : ℕ)) : ℝ) : ℂ)))
        ∂A.varianceWeightedRowMeasure P n := by
  sorry

-- Proof sketch: use the preceding centered bridge rewrite, where the Lindeberg hypothesis supplies
-- the needed centeredness instance, and combine it with weak convergence of `νₙ` to `δ₀` from
-- Lemma 15.48, applied to the bounded continuous bridge integrand on the right-hand side. Then
-- evaluate the limiting Dirac integral at `0`.
/-- Lemma 15.49: for a normed real random-variable array satisfying the Lindeberg condition, the
textbook expression
`∫ f_t(x) μₙ(dx) + i t ∫ (1 / x) μₙ(dx)` converges to `-t^2 / 2`. -/
theorem tendsto_cltAuxiliaryMeasure_expression
    (A : RealRandomVariableArray Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    [A.IsNormed P] (h_lindeberg : A.SatisfiesLindebergCondition P) (t : ℝ) :
    Tendsto
      (fun n ↦
        (∫ x, cltAuxiliaryFunction t x ∂A.cltAuxiliaryMeasure P n) +
          Complex.I * (t : ℂ) * (∫ x, (1 / (x : ℂ)) ∂A.cltAuxiliaryMeasure P n))
      atTop
      (𝓝 ((-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ))) := by
  sorry

-- Proof sketch: apply weak convergence of `A.varianceWeightedRowLaw P n` to `diracProba 0`
-- from Lemma 15.48 via the canonical bounded continuous test function `cltAuxiliaryFunctionBCF t`
-- from Lemma 15.47, then evaluate the limiting Dirac integral at `0`.
/-- Bridge/view consequence: the canonical variance-weighted row laws `νₙ` integrate the bounded
continuous test function from Lemma 15.47 to the same limit `-t^2 / 2`. -/
theorem tendsto_integral_cltAuxiliaryFunctionBCF_varianceWeightedRowLaw
    (A : RealRandomVariableArray Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    [A.IsNormed P] (h_lindeberg : A.SatisfiesLindebergCondition P) (t : ℝ) :
    Tendsto
      (fun n ↦ ∫ x, cltAuxiliaryFunctionBCF t x ∂(A.varianceWeightedRowLaw P n : Measure ℝ))
      atTop
      (𝓝 ((-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ))) := by
  letI : A.IsCentered P := h_lindeberg.toIsCentered
  have h_tendsto :
      Tendsto (fun n ↦ A.varianceWeightedRowLaw P n) atTop (𝓝 (diracProba (0 : ℝ))) :=
    A.varianceWeightedRowLaw_tendsto_diracProba_zero_of_satisfiesLindebergCondition P h_lindeberg
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ] at h_tendsto
  have h_integral :
      Tendsto
        (fun n ↦ ∫ x, cltAuxiliaryFunctionBCF t x ∂(A.varianceWeightedRowLaw P n : Measure ℝ))
        atTop
        (𝓝
          (∫ x, cltAuxiliaryFunctionBCF t x
            ∂((diracProba (0 : ℝ) : ProbabilityMeasure ℝ) : Measure ℝ))) :=
    h_tendsto (cltAuxiliaryFunctionBCF t)
  have h_dirac :
      (∫ x, cltAuxiliaryFunctionBCF t x
        ∂((diracProba (0 : ℝ) : ProbabilityMeasure ℝ) : Measure ℝ)) =
        ((-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ)) := by
    rw [show (((diracProba (0 : ℝ) : ProbabilityMeasure ℝ) : Measure ℝ)) = Measure.dirac (0 : ℝ)
      by rfl]
    rw [integral_dirac]
    simp [cltAuxiliaryFunction_apply_zero]
  rw [show ((-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ)) =
      (∫ x, cltAuxiliaryFunctionBCF t x
        ∂((diracProba (0 : ℝ) : ProbabilityMeasure ℝ) : Measure ℝ)) by
      simpa using h_dirac.symm]
  exact h_integral

end RealRandomVariableArray
