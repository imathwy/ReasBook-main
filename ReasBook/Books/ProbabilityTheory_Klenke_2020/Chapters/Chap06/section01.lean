import Mathlib
import Mathlib.MeasureTheory.Measure.Dirac

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_6_1_1 (from Items/Chap06) -/
open Filter MeasureTheory
open scoped Topology

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [PseudoMetricSpace E]

-- Proof sketch: restrict the convergence-in-measure statement to the singleton `{ω}`. The
-- restricted measure is `μ {ω} • Measure.dirac ω`, so if `μ {ω} ≠ 0`, then every deviation event
-- containing `ω` has restricted measure exactly `μ {ω}`. Since the restricted deviation measures
-- tend to `0`, eventually `ω` cannot lie in any `ε`-deviation set.
private theorem tendsto_at_of_tendstoInMeasure_of_singleton_ne_zero
    (μ : Measure Ω) [IsFiniteMeasure μ] {fSeq : ℕ → Ω → E} {f : Ω → E} {ω : Ω}
    (h_tendsto : TendstoInMeasure μ fSeq atTop f)
    (hω : μ {ω} ≠ 0) :
    Tendsto (fun n ↦ fSeq n ω) atTop (𝓝 (f ω)) := by
  have h_restrict : TendstoInMeasure (μ.restrict {ω}) fSeq atTop f := by
    rw [tendstoInMeasure_iff_dist] at h_tendsto ⊢
    intro ε hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h_tendsto ε hε)
      (fun _ ↦ zero_le _) ?_
    intro n
    exact Measure.restrict_apply_le {ω} {x | ε ≤ dist (fSeq n x) (f x)}
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := (ENNReal.tendsto_atTop_zero.1 ((tendstoInMeasure_iff_dist.1 h_restrict) ε hε))
    (μ {ω} / 2) (ENNReal.half_pos hω)
  refine ⟨N, fun n hn ↦ ?_⟩
  by_contra hdist
  have hmem : ω ∈ {x | ε ≤ dist (fSeq n x) (f x)} := by
    simpa [Set.mem_setOf_eq, not_lt] using hdist
  have hdirac :
      (Measure.dirac ω) {x | ε ≤ dist (fSeq n x) (f x)} = 1 :=
    Measure.dirac_apply_of_mem hmem
  have h_le : μ {ω} ≤ μ {ω} / 2 := by
    simpa [Measure.restrict_singleton, hdirac, smul_eq_mul] using hN n hn
  exact not_le_of_gt (ENNReal.half_lt_self hω (measure_ne_top μ {ω})) h_le

-- Proof sketch: use `ae_iff_of_countable` to reduce almost-everywhere convergence on the
-- countable space `Ω` to pointwise convergence at those `ω` with `P {ω} ≠ 0`, then apply the
-- preceding singleton-mass lemma.
/-- Exercise 6.1.1: On a countable probability space, convergence in probability implies
almost-everywhere convergence. -/
theorem tendsto_ae_of_tendstoInMeasure_of_countable
    [Countable Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {fSeq : ℕ → Ω → E} {f : Ω → E}
    (h_tendsto : TendstoInMeasure P fSeq atTop f) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ fSeq n ω) atTop (𝓝 (f ω)) := by
  rw [ae_iff_of_countable]
  intro ω hω
  exact tendsto_at_of_tendstoInMeasure_of_singleton_ne_zero P h_tendsto hω

/-! ### Lemma_6_1 (from Items/Chap06) -/
/- Lemma 6.1: If `f, g : Ω → E` are measurable maps into a metric space equipped with its Borel
`σ`-algebra, then the nonnegative distance map `ω ↦ nndist (f ω) (g ω)` is measurable. This is
the canonical mathlib statement `Measurable.nndist`. -/
recall Measurable.nndist

/-! ### Exercise_6_1_2 (from Items/Chap06) -/
open Filter MeasureTheory
open scoped Topology

noncomputable section

/-- The Lebesgue measure restricted to `(0, 1]`, used for the typewriter example. -/
def typewriterMeasure : Measure ℝ :=
  volume.restrict (Set.Ioc (0 : ℝ) 1)

/-- The dyadic interval supporting the `n`-th term of the typewriter sequence. -/
private def typewriterSupport (n : ℕ) : Set ℝ :=
  let m := Nat.log2 (n + 1)
  let k := n + 1 - 2 ^ m
  Set.Ioc ((k : ℝ) / (2 : ℝ) ^ m) (((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ m)

/-- The typewriter sequence on `(0, 1]`, viewed as indicator functions of dyadic intervals. -/
def typewriterSequence (n : ℕ) : ℝ → ℝ :=
  (typewriterSupport n).indicator (fun _ ↦ (1 : ℝ))

-- Proof sketch: the support of `typewriterSequence n` is a bounded measurable interval inside
-- `(0, 1]`, so its indicator is measurable and has finite integral against `typewriterMeasure`.
/-- Each term of the typewriter sequence is integrable on `(0, 1]`. -/
private theorem typewriterSequence_integrable (n : ℕ) :
    Integrable (typewriterSequence n) typewriterMeasure := sorry

-- Proof sketch: compute the `L¹` norm of `typewriterSequence n` as the length of its dyadic
-- support, which tends to `0`, while every point of `(0, 1]` lies in exactly one dyadic interval
-- at each generation, so the pointwise values oscillate between `0` and `1` and fail to converge.
/-- The typewriter sequence converges to `0` in mean (`L¹`) on `(0, 1]`. -/
private theorem typewriterSequence_tendstoInMean :
    TendstoInMean typewriterMeasure typewriterSequence 0 := sorry

/-- The typewriter sequence does not converge to `0` almost everywhere on `(0, 1]`. -/
private theorem typewriterSequence_not_tendstoAlmostEverywhere :
    ¬ ∀ᵐ ω ∂typewriterMeasure, Tendsto (fun n ↦ typewriterSequence n ω) atTop (𝓝 (0 : ℝ)) := sorry

/-- Exercise 6.1.2 (1): the typewriter sequence converges to `0` in mean (`L¹`) but does not
converge to `0` almost everywhere. -/
theorem typewriter_sequence_converges_inL1_not_ae :
    TendstoInMean typewriterMeasure typewriterSequence 0 ∧
      ¬ ∀ᵐ ω ∂typewriterMeasure, Tendsto (fun n ↦ typewriterSequence n ω) atTop (𝓝 (0 : ℝ)) :=
  ⟨typewriterSequence_tendstoInMean, typewriterSequence_not_tendstoAlmostEverywhere⟩

/-- The indicator functions of the unit intervals translated to the right along the real line. -/
def escapingIndicatorSequence (n : ℕ) : ℝ → ℝ :=
  (Set.Icc (n : ℝ) (n + 1)).indicator (fun _ ↦ (1 : ℝ))

-- Proof sketch: each translated unit interval is measurable and has finite Lebesgue measure, so
-- its indicator function is Lebesgue integrable.
/-- Each translated interval indicator is integrable with respect to Lebesgue measure. -/
private theorem escapingIndicatorSequence_integrable (n : ℕ) :
    Integrable (escapingIndicatorSequence n) (volume : Measure ℝ) := sorry

-- Proof sketch: for each fixed `x : ℝ`, the intervals `[n, n + 1]` eventually lie to the right of
-- `x`, so the sequence is eventually `0` at `x`; however every term has `L¹` norm equal to `1`,
-- so the sequence cannot converge to `0` in `L¹`.
/-- The translated unit-interval indicators converge to `0` almost everywhere. -/
private theorem escapingIndicatorSequence_tendstoAlmostEverywhere :
    ∀ᵐ ω ∂volume, Tendsto (fun n ↦ escapingIndicatorSequence n ω) atTop (𝓝 (0 : ℝ)) := sorry

/-- The translated unit-interval indicators do not converge to `0` in mean (`L¹`). -/
private theorem escapingIndicatorSequence_not_tendstoInMean :
    ¬ TendstoInMean volume escapingIndicatorSequence 0 := sorry

/-- Exercise 6.1.2 (2): the translated unit-interval indicators converge to `0` almost
everywhere but do not converge to `0` in mean (`L¹`). -/
theorem escaping_indicator_sequence_tendsto_ae_not_inL1 :
    (∀ᵐ ω ∂volume, Tendsto (fun n ↦ escapingIndicatorSequence n ω) atTop (𝓝 (0 : ℝ))) ∧
      ¬ TendstoInMean volume escapingIndicatorSequence 0 :=
  ⟨escapingIndicatorSequence_tendstoAlmostEverywhere,
    escapingIndicatorSequence_not_tendstoInMean⟩

end

/-! ### Exercise_6_1_3 (from Items/Chap06) -/
open Filter MeasureTheory
open scoped Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- Exercise 6.1.3: a source-facing complement-set reformulation of
`MeasureTheory.tendstoUniformlyOn_of_ae_tendsto'` for real-valued measurable functions on a finite
measure space. It produces a measurable set on which the convergence is uniform and whose
complement has arbitrarily small measure. -/
-- Proof sketch: apply mathlib's finite-measure Egorov theorem to the sequence `fSeq` and limit
-- `f`, using measurable-to-strongly-measurable for real-valued functions. Run the theorem with
-- tolerance `ε / 2`, then replace the exceptional set `t` by `A := tᶜ` so that
-- `μ (Aᶜ) = μ t < ε`.
theorem exists_measurableSet_tendstoUniformlyOn_of_ae_tendsto
    {fSeq : ℕ → Ω → ℝ} {f : Ω → ℝ}
    (hf : ∀ n, Measurable (fSeq n)) (hg : Measurable f)
    (h_tendsto : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ fSeq n ω) atTop (𝓝 (f ω)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Set Ω, MeasurableSet A ∧
      μ Aᶜ < ENNReal.ofReal ε ∧ TendstoUniformlyOn fSeq f atTop A := by
  obtain ⟨t, ht_meas, ht_small, ht_uniform⟩ :=
    tendstoUniformlyOn_of_ae_tendsto'
      (fun n ↦ (hf n).stronglyMeasurable) hg.stronglyMeasurable h_tendsto (half_pos hε)
  refine ⟨tᶜ, ht_meas.compl, ?_, by simpa using ht_uniform⟩
  simpa using
    (lt_of_le_of_lt ht_small <| (ENNReal.ofReal_lt_ofReal_iff hε).2 (half_lt_self hε))

/-! ### Exercise_6_1_4 (from Items/Chap06) -/
open Filter MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

-- Proof sketch: the variances of the partial sums are the finite sums of the summable variance
-- series because the terms are independent and centered, so the partial sums form a Cauchy family
-- in `L²`. Use completeness of `L²` to obtain a square-integrable limit and then apply the
-- almost-sure convergence criterion from summable square-integrable tails.
/-- Exercise 6.1.4: If `X₁, X₂, …` is an independent sequence of centered square-integrable real
random variables with summable variances, then the partial sums converge almost surely to a
square-integrable random variable. In Lean's `0`-based indexing, the conclusion concerns the
canonical partial sums `partialSum X n = X₀ + ⋯ + Xₙ₋₁`. -/
theorem exists_memLp_two_ae_tendsto_partial_sums_of_iIndepFun_summable_variance
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_indep : iIndepFun X P)
    (hX_memLp : ∀ n, MemLp (X n) 2 P)
    (hX_centered : ∀ n, P[X n] = 0)
    (h_var_summable : Summable fun n ↦ Var[X n; P]) :
    ∃ Y : Ω → ℝ, MemLp Y 2 P ∧
      ∀ᵐ ω ∂P, Tendsto (fun n ↦ partialSum X n ω) atTop (𝓝 (Y ω)) := sorry
