import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u v

/-- The rejection-sampling index is the infimum of the accepted-index set; when that set is
nonempty, it is the first accepted proposal index. -/
noncomputable def rejectionSamplingIndex
    {Ω : Type u} {E : Type v}
    (X : ℕ → Ω → E) (U : ℕ → Ω → unitInterval) (accept : E → ℝ) : Ω → ℕ :=
  fun ω ↦ sInf {n : ℕ | (U n ω : ℝ) ≤ accept (X n ω)}

/-- The rejection-sampling sample is the proposal evaluated at the rejection-sampling index; when
the accepted-index set is nonempty, this is the first accepted proposal value. -/
noncomputable def rejectionSamplingValue
    {Ω : Type u} {E : Type v}
    (X : ℕ → Ω → E) (U : ℕ → Ω → unitInterval) (accept : E → ℝ) : Ω → E :=
  fun ω ↦ X (rejectionSamplingIndex X U accept ω) ω

/-- If the accepted-index set is nonempty, then the rejection-sampling index is its least
element. -/
theorem isLeast_rejectionSamplingIndex
    {Ω : Type u} {E : Type v}
    (X : ℕ → Ω → E) (U : ℕ → Ω → unitInterval) (accept : E → ℝ) {ω : Ω}
    (hω : {n : ℕ | (U n ω : ℝ) ≤ accept (X n ω)}.Nonempty) :
    IsLeast {n : ℕ | (U n ω : ℝ) ≤ accept (X n ω)} (rejectionSamplingIndex X U accept ω) := by
  constructor
  · simpa [rejectionSamplingIndex] using Nat.sInf_mem hω
  · intro n hn
    simpa [rejectionSamplingIndex] using (Nat.sInf_le hn)

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]

/-- The acceptance probability used by rejection sampling for the proposal law `p` and the target
law `q`, with rejection constant `c`. -/
noncomputable def rejectionAcceptanceProb (p q : PMF E) (c : ℝ) (e : E) : ℝ :=
  if p e = 0 then 0 else (q e).toReal / (c * (p e).toReal)

-- Proof sketch: split on whether `p e = 0`. In the zero-mass case the definition is `0`. In the
-- nonzero case, rewrite `rejectionAcceptanceProb` and divide the domination inequality by the
-- positive number `c * (p e).toReal`.
/-- Under the domination bound `q ≤ c p`, every rejection-sampling acceptance probability is at
most `1`. -/
theorem rejectionAcceptanceProb_le_one
    (p q : PMF E) {c : ℝ} (hc : 0 < c)
    (hdom : ∀ e, (q e).toReal ≤ c * (p e).toReal) (e : E) :
    rejectionAcceptanceProb p q c e ≤ 1 := sorry

-- Proof sketch: for each `e`, compute the probability that the first accepted proposal equals
-- `e` by summing over the first acceptance time. The pairwise i.i.d. hypothesis gives a geometric
-- factor from the previous rejections and identifies the acceptance probability at time `n` with
-- `q e / c`; summing the geometric series yields exactly `q e`. Equality of singleton masses then
-- gives `HasLaw Y q.toMeasure μ`.
/-- Canonical paired formulation of Exercise 8.3.6: if the proposal-auxiliary pairs `(X n, U n)`
form an independent sequence with common law `p × uniform[0,1]`, then the rejection-sampling
value associated to `rejectionAcceptanceProb p q c` has law `q`. -/
theorem hasLaw_of_rejection_sampling_of_pair_iIndep
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p q : PMF E) (c : ℝ)
    (X : ℕ → Ω → E) (U : ℕ → Ω → unitInterval)
    (hc : 0 < c)
    (hdom : ∀ e, (q e).toReal ≤ c * (p e).toReal)
    (h_pair_iIndep : iIndepFun (fun n ω ↦ (X n ω, U n ω)) μ)
    (h_pair_law : ∀ n, HasLaw (fun ω ↦ (X n ω, U n ω))
      (p.toMeasure.prod volume) μ) :
    HasLaw (rejectionSamplingValue X U (rejectionAcceptanceProb p q c)) q.toMeasure μ := sorry

/-- Independent random variables with laws `ν` and `η` have joint law `ν.prod η`. -/
theorem hasLaw_prod_of_hasLaw_of_indep
    {F G : Type*} [MeasurableSpace F] [MeasurableSpace G]
    (μ : Measure Ω) [IsFiniteMeasure μ] {ν : Measure F} {η : Measure G}
    (X : Ω → F) (Y : Ω → G)
    (hX_law : HasLaw X ν μ) (hY_law : HasLaw Y η μ)
    (hXY : X ⟂ᵢ[μ] Y) :
    HasLaw (fun ω ↦ (X ω, Y ω)) (ν.prod η) μ := by
  refine
    { aemeasurable := hX_law.aemeasurable.prodMk hY_law.aemeasurable
      map_eq := ?_ }
  rw [(indepFun_iff_map_prod_eq_prod_map_map hX_law.aemeasurable hY_law.aemeasurable).mp hXY,
    hX_law.map_eq, hY_law.map_eq]

omit [MeasurableSingletonClass E] [Countable E] in
/-- If `X` and `U` are i.i.d. families and the sequence-valued random elements are independent,
then the paired family `n ↦ (X n, U n)` is independent. -/
theorem iIndepFun_pair_of_iIndepFun_of_indepFun
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ν : Measure E}
    (X : ℕ → Ω → E) (U : ℕ → Ω → unitInterval)
    (hX_iIndep : iIndepFun X μ)
    (hX_law : ∀ n, HasLaw (X n) ν μ)
    (hU_iIndep : iIndepFun U μ)
    (hU_law : ∀ n, HasLaw (U n) volume μ)
    (h_seq_indep : IndepFun (fun ω n ↦ X n ω) (fun ω n ↦ U n ω) μ) :
    iIndepFun (fun n ω ↦ (X n ω, U n ω)) μ := by
  rw [iIndepFun_iff_finset]
  intro s
  have hX_restrict' : iIndepFun (fun i : s ↦ X i) μ :=
    hX_iIndep.precomp Subtype.val_injective
  have hX_restrict : iIndepFun (s.restrict X) μ := by
    simpa [Finset.restrict] using hX_restrict'
  have hU_restrict' : iIndepFun (fun i : s ↦ U i) μ :=
    hU_iIndep.precomp Subtype.val_injective
  have hU_restrict : iIndepFun (s.restrict U) μ := by
    simpa [Finset.restrict] using hU_restrict'
  rw [iIndepFun_iff_map_fun_eq_pi_map]
  · change μ.map (fun ω (i : s) ↦ (X i ω, U i ω)) =
      Measure.pi (fun i : s ↦ μ.map (fun ω ↦ (X i ω, U i ω)))
    let φ : (ℕ → E) → (s → E) := fun f i ↦ f i
    let ψ : (ℕ → unitInterval) → (s → unitInterval) := fun f i ↦ f i
    have h_indep_restrict :
        IndepFun (fun ω (i : s) ↦ X i ω) (fun ω (i : s) ↦ U i ω) μ := by
      have hφ : Measurable φ := by
        fun_prop
      have hψ : Measurable ψ := by
        fun_prop
      simpa [φ, ψ] using h_seq_indep.comp hφ hψ
    have h_map_eq :
        μ.map (fun ω ↦ (fun i : s ↦ X i ω, fun i : s ↦ U i ω)) =
          (Measure.pi fun i : s ↦ μ.map (X i)).prod
            (Measure.pi fun i : s ↦ μ.map (U i)) := by
      rw [(indepFun_iff_map_prod_eq_prod_map_map
        (aemeasurable_pi_lambda _ fun i : s ↦ (hX_law i).aemeasurable)
        (aemeasurable_pi_lambda _ fun i : s ↦ (hU_law i).aemeasurable)).mp h_indep_restrict,
        (iIndepFun_iff_map_fun_eq_pi_map fun i : s ↦ (hX_law i).aemeasurable).mp hX_restrict,
        (iIndepFun_iff_map_fun_eq_pi_map fun i : s ↦ (hU_law i).aemeasurable).mp hU_restrict]
    have h_pair_map_eq (i : s) :
        μ.map (fun ω ↦ (X i ω, U i ω)) = (μ.map (X i)).prod (μ.map (U i)) := by
      have h_indep_i : X i ⟂ᵢ[μ] U i := by
        simpa using h_seq_indep.comp (measurable_pi_apply (i : ℕ)) (measurable_pi_apply (i : ℕ))
      rw [(indepFun_iff_map_prod_eq_prod_map_map
        (hX_law i).aemeasurable (hU_law i).aemeasurable).mp h_indep_i]
    let e := MeasurableEquiv.arrowProdEquivProdArrow E unitInterval s
    have h_pair_vec_aemeasurable : AEMeasurable (fun ω (i : s) ↦ (X i ω, U i ω)) μ :=
      aemeasurable_pi_lambda _ fun i : s ↦
        ((hX_law i).aemeasurable).prodMk ((hU_law i).aemeasurable)
    rw [← e.map_measurableEquiv_injective.eq_iff]
    rw [AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable h_pair_vec_aemeasurable]
    change μ.map (fun ω ↦ (fun i : s ↦ X i ω, fun i : s ↦ U i ω)) =
      Measure.map e (Measure.pi (fun i : s ↦ μ.map (fun ω ↦ (X i ω, U i ω))))
    refine h_map_eq.trans ?_
    symm
    calc
      Measure.map e (Measure.pi fun i : s ↦ μ.map (fun ω ↦ (X i ω, U i ω)))
          = Measure.map e (Measure.pi fun i : s ↦ (μ.map (X i)).prod (μ.map (U i))) := by
              simp [h_pair_map_eq]
      _ = (Measure.pi fun i : s ↦ μ.map (X i)).prod (Measure.pi fun i : s ↦ μ.map (U i)) :=
            (measurePreserving_arrowProdEquivProdArrow E unitInterval s
              (fun i : s ↦ μ.map (X i)) (fun i : s ↦ μ.map (U i))).map_eq
  · intro i
    simpa [Finset.restrict] using
      (((hX_law i).aemeasurable).prodMk ((hU_law i).aemeasurable) :
        AEMeasurable (fun ω ↦ (X i ω, U i ω)) μ)

/-- Exercise 8.3.6: if the proposals `X n` are i.i.d. with law `p`, the auxiliary variables `U n`
are i.i.d. uniform on `[0,1]`, and the two sequences are independent, then the associated
rejection-sampling value has law `q`. -/
theorem hasLaw_of_rejection_sampling
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p q : PMF E) (c : ℝ)
    (X : ℕ → Ω → E) (U : ℕ → Ω → unitInterval)
    (hc : 0 < c)
    (hdom : ∀ e, (q e).toReal ≤ c * (p e).toReal)
    (hX_iIndep : iIndepFun X μ)
    (hX_law : ∀ n, HasLaw (X n) p.toMeasure μ)
    (hU_iIndep : iIndepFun U μ)
    (hU_law : ∀ n, HasLaw (U n) volume μ)
    (h_seq_indep : IndepFun (fun ω n ↦ X n ω) (fun ω n ↦ U n ω) μ) :
    HasLaw (rejectionSamplingValue X U (rejectionAcceptanceProb p q c)) q.toMeasure μ := by
  have h_pair_iIndep : iIndepFun (fun n ω ↦ (X n ω, U n ω)) μ :=
    iIndepFun_pair_of_iIndepFun_of_indepFun μ (ν := p.toMeasure) X U
      hX_iIndep hX_law hU_iIndep hU_law h_seq_indep
  have h_pair_law : ∀ n, HasLaw (fun ω ↦ (X n ω, U n ω)) (p.toMeasure.prod volume) μ := by
    intro n
    have h_indep_n : X n ⟂ᵢ[μ] U n := by
      simpa using h_seq_indep.comp (measurable_pi_apply n) (measurable_pi_apply n)
    exact hasLaw_prod_of_hasLaw_of_indep μ (X n) (U n) (hX_law n) (hU_law n) h_indep_n
  exact hasLaw_of_rejection_sampling_of_pair_iIndep μ p q c X U hc hdom h_pair_iIndep h_pair_law

/-- If `N` is almost surely the first accepted proposal index, then the associated proposal value
agrees almost surely with the canonical rejection-sampling value. -/
theorem ae_eq_rejectionSamplingValue_of_ae_isLeast
    {Ω : Type u} {E : Type v} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → E) (U : ℕ → Ω → unitInterval) (accept : E → ℝ) (N : Ω → ℕ)
    (hN : ∀ᵐ ω ∂μ,
      IsLeast {n : ℕ | (U n ω : ℝ) ≤ accept (X n ω)} (N ω)) :
    (fun ω ↦ X (N ω) ω) =ᵐ[μ] rejectionSamplingValue X U accept := by
  filter_upwards [hN] with ω hω
  dsimp [rejectionSamplingValue, rejectionSamplingIndex]
  rw [hω.isGLB.csInf_eq hω.nonempty]

/-- Textbook-form bridge for Exercise 8.3.6: if `N` is almost surely the first accepted index and
`Y = X N` almost surely, then `Y` has law `q`. -/
theorem hasLaw_of_rejection_sampling_of_ae_isLeast
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p q : PMF E) (c : ℝ)
    (X : ℕ → Ω → E) (U : ℕ → Ω → unitInterval) (N : Ω → ℕ) (Y : Ω → E)
    (hc : 0 < c)
    (hdom : ∀ e, (q e).toReal ≤ c * (p e).toReal)
    (hX_iIndep : iIndepFun X μ)
    (hX_law : ∀ n, HasLaw (X n) p.toMeasure μ)
    (hU_iIndep : iIndepFun U μ)
    (hU_law : ∀ n, HasLaw (U n) volume μ)
    (h_seq_indep : IndepFun (fun ω n ↦ X n ω) (fun ω n ↦ U n ω) μ)
    (hN : ∀ᵐ ω ∂μ,
      IsLeast {n : ℕ | (U n ω : ℝ) ≤ rejectionAcceptanceProb p q c (X n ω)} (N ω))
    (hY : Y =ᵐ[μ] fun ω ↦ X (N ω) ω) :
    HasLaw Y q.toMeasure μ := by
  refine (hasLaw_of_rejection_sampling μ p q c X U hc hdom
    hX_iIndep hX_law hU_iIndep hU_law h_seq_indep).congr ?_
  exact hY.trans (ae_eq_rejectionSamplingValue_of_ae_isLeast μ X U
    (rejectionAcceptanceProb p q c) N hN)
