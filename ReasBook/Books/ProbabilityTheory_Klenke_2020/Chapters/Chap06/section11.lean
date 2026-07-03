

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_6_11 (from Items/Chap06) -/
open Filter MeasureTheory
open scoped ENNReal Topology

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [NormedAddCommGroup E]

-- Proof sketch: fix a finite-measure set `A` and apply the canonical finite-measure
-- `L¹`-to-in-measure implication to the restricted measure `μ.restrict A`; this is the local
-- textbook notion packaged by `TendstoInMeasureOnFiniteMeasureSets`.
/-- Mean (`L¹`) convergence implies local convergence in `μ`-measure on finite-measure sets. -/
theorem tendstoInMeasureOnFiniteMeasureSets_of_tendstoInMean
    (μ : Measure Ω) {fSeq : ℕ → Ω → E} {f : Ω → E}
    (h_mean : TendstoInMean μ fSeq f) :
    TendstoInMeasureOnFiniteMeasureSets μ fSeq f := by
  have h_measSeq : ∀ n, AEStronglyMeasurable (fSeq n) μ :=
    fun n ↦ (h_mean.memLpSeq n).aestronglyMeasurable
  have h_meas : AEStronglyMeasurable f μ := h_mean.memLp.aestronglyMeasurable
  have h_tendsto_eLpNorm :
      Tendsto (fun n ↦ eLpNorm (fSeq n - f) 1 μ) atTop (𝓝 0) := by
    exact h_mean.tendsto_eLpNorm
  intro A hA_fin
  haveI : IsFiniteMeasure (μ.restrict A) :=
    isFiniteMeasure_restrict.2 (ne_of_lt hA_fin)
  have h_mean_restrict :
      Tendsto (fun n ↦ eLpNorm (fSeq n - f) 1 (μ.restrict A)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_tendsto_eLpNorm
      (fun n ↦ zero_le _) ?_
    intro n
    exact eLpNorm_restrict_le (fSeq n - f) 1 μ A
  exact tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
    (fun n ↦ (h_measSeq n).restrict) h_meas.restrict h_mean_restrict

-- Proof sketch: split on the disjunction and apply the canonical theorem for each branch:
-- the previous theorem for mean convergence, and
-- `tendstoInMeasureOnFiniteMeasureSets_of_tendsto_ae`
-- for almost-everywhere convergence.
/-- Remark 6.11: mean (`L¹`) convergence and almost-everywhere convergence are each sufficient
for local convergence in `μ`-measure on finite-measure sets. -/
theorem tendstoInMeasureOnFiniteMeasureSets_of_tendstoInMean_or_tendstoAlmostEverywhere
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) {fSeq : ℕ → Ω → E} {f : Ω → E}
    (h_meas : ∀ n, AEStronglyMeasurable (fSeq n) μ)
    (h : TendstoInMean μ fSeq f ∨
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ fSeq n ω) atTop (𝓝 (f ω))) :
    TendstoInMeasureOnFiniteMeasureSets μ fSeq f := by
  exact h.elim
    (tendstoInMeasureOnFiniteMeasureSets_of_tendstoInMean μ)
    (fun h_ae ↦ tendstoInMeasureOnFiniteMeasureSets_of_tendsto_ae μ h_meas h_ae)

/-- Remark 6.11 (counterexample): the typewriter sequence converges in mean, hence also in local
`μ`-measure, but it does not converge almost everywhere. Thus neither mean convergence nor local
convergence in measure implies almost-everywhere convergence in general. -/
theorem typewriterSequence_tendstoInMeasureOnFiniteMeasureSets_not_tendstoAlmostEverywhere :
    TendstoInMeasureOnFiniteMeasureSets typewriterMeasure typewriterSequence 0 ∧
      ¬ ∀ᵐ ω ∂typewriterMeasure, Tendsto (fun n ↦ typewriterSequence n ω) atTop (𝓝 (0 : ℝ)) := by
  sorry

/- Exercise 6.1.2 (1): the typewriter sequence is the chapter's source-facing counterexample
showing that mean convergence does not imply almost-everywhere convergence. -/
recall typewriter_sequence_converges_inL1_not_ae

/-- Remark 6.11 (counterexample): the escaping interval indicators converge almost everywhere,
hence also in local Lebesgue measure, but they do not converge in mean. Thus neither
almost-everywhere convergence nor local convergence in measure implies mean convergence in
general. -/
theorem escapingIndicatorSequence_tendstoInMeasureOnFiniteMeasureSets_not_tendstoInMean :
    TendstoInMeasureOnFiniteMeasureSets volume escapingIndicatorSequence 0 ∧
      ¬ TendstoInMean volume escapingIndicatorSequence 0 := by
  sorry

/- Exercise 6.1.2 (2): the escaping interval indicators are the chapter's source-facing
counterexample showing that almost-everywhere convergence does not imply mean convergence. -/
recall escaping_indicator_sequence_tendsto_ae_not_inL1
