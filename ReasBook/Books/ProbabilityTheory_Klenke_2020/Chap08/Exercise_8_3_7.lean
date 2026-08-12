import ProbabilityTheory_Klenke_2020.Chap08.Exercise_8_3_6

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

-- Proof sketch: view each proposal-auxiliary pair `(X n, U n)` as i.i.d. with common law
-- `P.prod volume`. The acceptance event at step `n` has conditional probability
-- `(Q.rnDeriv P (X n ·)).toReal / c`, and `Q ≪ P` together with the bound by `c` identifies the
-- accepted proposal law with `Q`. Summing over the first accepted index yields the law of the
-- selected sample.
/-- Exercise 8.3.7: if `Q ≪ P` and the Radon--Nikodym derivative `dQ/dP` is bounded by `c`, then
the rejection-sampling value with acceptance probability `x ↦ (dQ/dP)(x) / c` has law `Q`. -/
theorem hasLaw_rejectionSamplingValue_of_rnDeriv_le
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P Q : Measure E)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (c : ℝ) (hc : 0 < c) (hQP : Q ≪ P)
    (hbounded : ∀ᵐ x ∂P, (Q.rnDeriv P x).toReal ≤ c)
    (X : ℕ → Ω → E) (U : ℕ → Ω → unitInterval)
    (h_pair_iIndep : iIndepFun (fun n ω ↦ (X n ω, U n ω)) μ)
    (h_pair_law :
      ∀ n, HasLaw (fun ω ↦ (X n ω, U n ω)) (P.prod (volume : Measure unitInterval)) μ) :
    HasLaw (rejectionSamplingValue X U (fun x ↦ (Q.rnDeriv P x).toReal / c)) Q μ := sorry

/-- Exercise 8.3.7 in textbook hypothesis form: if the proposals `X n` are i.i.d. with law `P`,
the auxiliary variables `U n` are i.i.d. uniform on `[0,1]`, and the two sequences are
independent, then the rejection-sampling value with acceptance probability
`x ↦ (dQ/dP)(x) / c` has law `Q`. -/
theorem hasLaw_rejectionSamplingValue_of_rnDeriv_le_of_iIndep_of_indep
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P Q : Measure E)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (c : ℝ) (hc : 0 < c) (hQP : Q ≪ P)
    (hbounded : ∀ᵐ x ∂P, (Q.rnDeriv P x).toReal ≤ c)
    (X : ℕ → Ω → E) (U : ℕ → Ω → unitInterval)
    (hX_iIndep : iIndepFun X μ)
    (hX_law : ∀ n, HasLaw (X n) P μ)
    (hU_iIndep : iIndepFun U μ)
    (hU_law : ∀ n, HasLaw (U n) (volume : Measure unitInterval) μ)
    (h_seq_indep : IndepFun (fun ω n ↦ X n ω) (fun ω n ↦ U n ω) μ) :
    HasLaw (rejectionSamplingValue X U (fun x ↦ (Q.rnDeriv P x).toReal / c)) Q μ := by
  have h_pair_iIndep : iIndepFun (fun n ω ↦ (X n ω, U n ω)) μ :=
    iIndepFun_pair_of_iIndepFun_of_indepFun μ X U
      hX_iIndep hX_law hU_iIndep hU_law h_seq_indep
  have h_pair_law :
      ∀ n, HasLaw (fun ω ↦ (X n ω, U n ω)) (P.prod (volume : Measure unitInterval)) μ := by
    intro n
    have h_indep_n : X n ⟂ᵢ[μ] U n := by
      simpa using h_seq_indep.comp (measurable_pi_apply n) (measurable_pi_apply n)
    exact hasLaw_prod_of_hasLaw_of_indep μ (X n) (U n) (hX_law n) (hU_law n) h_indep_n
  exact hasLaw_rejectionSamplingValue_of_rnDeriv_le μ P Q c hc hQP hbounded X U
    h_pair_iIndep h_pair_law

/-- Textbook-form bridge for Exercise 8.3.7: if `N` is almost surely the first accepted index and
`Y = X N` almost surely, then `Y` has law `Q`. -/
theorem hasLaw_rejectionSamplingValue_of_rnDeriv_le_of_ae_isLeast
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P Q : Measure E)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (c : ℝ) (hc : 0 < c) (hQP : Q ≪ P)
    (hbounded : ∀ᵐ x ∂P, (Q.rnDeriv P x).toReal ≤ c)
    (X : ℕ → Ω → E) (U : ℕ → Ω → unitInterval) (N : Ω → ℕ) (Y : Ω → E)
    (hX_iIndep : iIndepFun X μ)
    (hX_law : ∀ n, HasLaw (X n) P μ)
    (hU_iIndep : iIndepFun U μ)
    (hU_law : ∀ n, HasLaw (U n) (volume : Measure unitInterval) μ)
    (h_seq_indep : IndepFun (fun ω n ↦ X n ω) (fun ω n ↦ U n ω) μ)
    (hN : ∀ᵐ ω ∂μ,
      IsLeast {n : ℕ | (U n ω : ℝ) ≤ (Q.rnDeriv P (X n ω)).toReal / c} (N ω))
    (hY : Y =ᵐ[μ] fun ω ↦ X (N ω) ω) :
    HasLaw Y Q μ := by
  let accept : E → ℝ := fun x ↦ (Q.rnDeriv P x).toReal / c
  refine (hasLaw_rejectionSamplingValue_of_rnDeriv_le_of_iIndep_of_indep μ P Q c hc hQP
    hbounded X U hX_iIndep hX_law hU_iIndep hU_law h_seq_indep).congr ?_
  refine hY.trans ?_
  simpa [accept] using ae_eq_rejectionSamplingValue_of_ae_isLeast μ X U accept N hN
