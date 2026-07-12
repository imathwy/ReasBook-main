import ProbabilityTheory_Klenke_2020.Items.Chap01.Definition_1_59

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Set Filter

open scoped Topology

/-- A real sub-probability measure is a Borel measure on `ℝ` with total mass at most `1`. -/
class IsSubProbabilityMeasure (μ : Measure ℝ) : Prop where
  measure_univ_le_one : μ Set.univ ≤ 1

/-- A real measure is sub-probability exactly when its total mass is at most `1`. -/
theorem isSubProbabilityMeasure_iff (μ : Measure ℝ) :
    IsSubProbabilityMeasure μ ↔ μ Set.univ ≤ 1 := by
  constructor
  · intro hμ
    exact hμ.measure_univ_le_one
  · intro hμ
    exact ⟨hμ⟩

instance (μ : Measure ℝ) [IsSubProbabilityMeasure μ] : IsFiniteMeasure μ :=
  ⟨lt_of_le_of_lt IsSubProbabilityMeasure.measure_univ_le_one ENNReal.one_lt_top⟩

/-- For a finite real measure, the cumulative mass function `x ↦ μ.real (Set.Iic x)` is monotone.
-/
theorem measureDistributionFunction_monotone (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Monotone (fun x : ℝ ↦ μ.real (Set.Iic x)) := by
  intro a b hab
  exact measureReal_mono (Set.Iic_subset_Iic.mpr hab)

/-- The distribution function attached to a finite real measure, viewed as a Stieltjes function.
-/
noncomputable def measureDistributionFunction (μ : Measure ℝ) [IsFiniteMeasure μ] :
    StieltjesFunction ℝ :=
  (measureDistributionFunction_monotone μ).stieltjesFunction

-- Proof sketch: identify the right-limit regularization defining `measureDistributionFunction`
-- with the actual cumulative mass function `x ↦ μ.real (Set.Iic x)` using right-continuity from
-- above for the finite measure of the rays `Set.Iic x`.
/-- The distribution function attached to a finite real measure evaluates to the cumulative mass
`μ (-∞, x]`, encoded as `μ.real (Set.Iic x)`. -/
theorem measureDistributionFunction_apply (μ : Measure ℝ) [IsFiniteMeasure μ] (x : ℝ) :
    measureDistributionFunction μ x = μ.real (Set.Iic x) := by
  sorry

/-- For a real probability measure, the finite-measure distribution function agrees with the
canonical cdf. -/
theorem cdf_eq_measureDistributionFunction (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ProbabilityTheory.cdf μ = measureDistributionFunction μ := by
  ext x
  rw [measureDistributionFunction_apply, ProbabilityTheory.cdf_eq_real]

/-- The distribution function attached to a real probability measure is a distribution function. -/
instance instIsDistributionFunction_measureDistributionFunction (μ : Measure ℝ)
    [IsProbabilityMeasure μ] : IsDistributionFunction (measureDistributionFunction μ) := by
  rw [← cdf_eq_measureDistributionFunction μ]
  infer_instance

/-- The distribution function attached to a real sub-probability measure is defective. -/
instance instIsDefectiveDistributionFunction_measureDistributionFunction (μ : Measure ℝ)
    [IsSubProbabilityMeasure μ] :
    IsDefectiveDistributionFunction (measureDistributionFunction μ) := by
  sorry

/-- A real sub-probability measure gives rise to a defective distribution function. -/
theorem isDefectiveDistributionFunction_measureDistributionFunction
    (μ : Measure ℝ) (hμ : IsSubProbabilityMeasure μ) :
    IsDefectiveDistributionFunction (measureDistributionFunction μ) := by
  letI : IsSubProbabilityMeasure μ := hμ
  infer_instance

/-- Probability measures on `ℝ` are in bijection with distribution functions via the canonical
cdf and Lebesgue--Stieltjes measure. -/
noncomputable def probabilityMeasureEquivDistributionFunction :
    ProbabilityMeasure ℝ ≃ {F : StieltjesFunction ℝ // IsDistributionFunction F} where
  toFun μ := ⟨cdf μ, inferInstance⟩
  invFun F := ⟨F.1.measure,
    F.1.isProbabilityMeasure
      F.2.toIsDefectiveDistributionFunction.tendsto_atBot_zero
      F.2.tendsto_atTop_one⟩
  left_inv μ := by
    apply ProbabilityMeasure.toMeasure_injective
    simpa using measure_cdf (μ : Measure ℝ)
  right_inv F := by
    apply Subtype.ext
    simpa using
      cdf_measure_stieltjesFunction F.1
        F.2.toIsDefectiveDistributionFunction.tendsto_atBot_zero
        F.2.tendsto_atTop_one

/-- Real sub-probability measures are in bijection with defective distribution functions via the
finite-measure cdf and Lebesgue--Stieltjes measure. -/
noncomputable def subProbabilityMeasureEquivDefectiveDistributionFunction :
    {μ : Measure ℝ // IsSubProbabilityMeasure μ} ≃
      {F : StieltjesFunction ℝ // IsDefectiveDistributionFunction F} where
  toFun μ := by
    letI : IsFiniteMeasure μ.1 := ⟨lt_of_le_of_lt μ.2.measure_univ_le_one ENNReal.one_lt_top⟩
    exact ⟨measureDistributionFunction μ.1,
      isDefectiveDistributionFunction_measureDistributionFunction μ.1 μ.2⟩
  invFun F := ⟨F.1.measure, by
    refine ⟨?_⟩
    sorry⟩
  left_inv μ := by
    apply Subtype.ext
    sorry
  right_inv F := by
    apply Subtype.ext
    sorry

-- Proof sketch: for probability measures, use the canonical cdf/Stieltjes correspondence in
-- mathlib together with `cdf_eq_measureDistributionFunction`; for sub-probability measures, the
-- same cumulative-mass construction lands in `IsDefectiveDistributionFunction`, and
-- `StieltjesFunction.measure` reconstructs the original measure.
/-- Theorem 1.60: The assignment `μ ↦ F_μ` is a bijection from probability measures on
`(ℝ, 𝓑(ℝ))` to distribution functions, and from sub-probability measures to defective
distribution functions. -/
theorem measureDistributionFunction_bijective :
    Function.Bijective probabilityMeasureEquivDistributionFunction ∧
      Function.Bijective subProbabilityMeasureEquivDefectiveDistributionFunction := by
  exact ⟨probabilityMeasureEquivDistributionFunction.bijective,
    subProbabilityMeasureEquivDefectiveDistributionFunction.bijective⟩
