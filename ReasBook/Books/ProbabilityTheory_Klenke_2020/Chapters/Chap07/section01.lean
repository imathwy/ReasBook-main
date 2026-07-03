import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_1 (from Items/Chap07) -/
open MeasureTheory
open scoped ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {p : ℝ≥0∞}

/- Definition 7.1: The textbook space `L^p(Ω, 𝒜, μ)` of almost-everywhere equivalence classes of
real-valued `ℒ^p` functions modulo null functions is formalized by the canonical type
`Lp ℝ p μ`. -/
recall Lp

/- The quotient-class representative map `f ↦ \bar f` is the canonical construction
`MemLp.toLp`, sending a real-valued `ℒ^p` function to its class in `Lp ℝ p μ`. -/
recall MemLp.toLp

/- The norm of an `L^p` class is the `ℒ^p` seminorm of any representative, formalized by
`Lp.norm_toLp`. -/
recall Lp.norm_toLp

/- The integral descends to almost-everywhere equivalence classes whenever a representative is
integrable, because almost-everywhere equal representatives have the same integral by
`integral_congr_ae`. -/
recall integral_congr_ae

/-! ### Exercise_7_1_1 (from Items/Chap07) -/
open Filter MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

-- Proof sketch: reuse the Chapter 6 `L²` convergence theorem, then replace its almost-sure limit
-- by the canonical measurable representative of the underlying `MemLp` function.
/-- Exercise 7.1.1 (1): (i) If `X₁, X₂, …` is an independent sequence of centered square-integrable
real random variables and `∑ Var[X_i] < ∞`, then the partial sums converge almost surely to a
measurable real-valued limit. In Lean's `0`-based indexing, the partial sums are `partialSum X n
= X₀ + ⋯ + Xₙ₋₁`. -/
theorem hasAETendstoPartialSums_of_iIndepFun_summable_variance
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_indep : iIndepFun X P)
    (hX_memLp : ∀ n, MemLp (X n) 2 P)
    (hX_centered : ∀ n, P[X n] = 0)
    (h_var_summable : Summable fun n ↦ Var[X n; P]) :
    ∃ Y : Ω → ℝ, Measurable Y ∧
      ∀ᵐ ω ∂P, Tendsto (fun n ↦ partialSum X n ω) atTop (𝓝 (Y ω)) := by
  obtain ⟨Y, hY_memLp, hY_lim⟩ :=
    exists_memLp_two_ae_tendsto_partial_sums_of_iIndepFun_summable_variance
      P X hX_indep hX_memLp hX_centered h_var_summable
  let hY_meas := hY_memLp.aestronglyMeasurable
  refine ⟨hY_meas.mk Y, hY_meas.measurable_mk, ?_⟩
  filter_upwards [hY_lim, hY_meas.ae_eq_mk] with ω hω hY_eq
  simpa [hY_eq] using hω

-- Proof sketch: take a product probability measure on `ℝ^ℕ` whose `n`th coordinate is usually
-- `0` but equals `± (n + 1)` with probability of order `(n + 1)⁻²`. Then the coordinates are
-- independent, centered, and square integrable with nonsummable variances, while Borel--Cantelli
-- gives only finitely many nonzero coordinates almost surely, so the partial sums converge almost
-- surely.
/-- Exercise 7.1.1 (2): (ii) The converse in part (i) does not hold: there exists a probability
measure on `ℝ^ℕ` whose coordinate process is independent, centered, and square integrable, whose
partial sums converge almost surely, but whose variance series is not summable. -/
theorem exists_counterexample_to_converse_of_summable_variance
    :
    ∃ P : ProbabilityMeasure (ℕ → ℝ),
      iIndepFun coordinateProcess P ∧
        (∀ n, MemLp (coordinateProcess n) 2 P) ∧
        (∀ n, P[coordinateProcess n] = 0) ∧
        (∃ Y : (ℕ → ℝ) → ℝ, Measurable Y ∧
          ∀ᵐ ω ∂P.toMeasure,
            Tendsto (fun n ↦ partialSum coordinateProcess n ω) atTop (𝓝 (Y ω))) ∧
        ¬ Summable (fun n ↦ Var[coordinateProcess n; P]) := sorry

/-! ### Exercise_7_1_2 (from Items/Chap07) -/
open Filter
open scoped ENNReal Topology

namespace MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Exercise 7.1.2 (1): canonical `MemLp` form of clause (i). If `f` belongs to `L^p(μ)` for some
positive finite exponent, then its finite-exponent seminorms converge to the `L^∞` seminorm as
`p → ∞`. -/
-- Proof sketch: compare the seminorms for different exponents using the standard `eLpNorm`
-- comparison inequalities, use the finite-exponent hypothesis to control all large exponents, and
-- identify the limiting upper and lower bounds with `eLpNorm f ∞ μ`.
theorem tendsto_eLpNorm_atTop_of_exists_memLp {f : Ω → ℝ}
    (hfin : ∃ p : NNReal, 0 < p ∧ MemLp f p μ) :
    Tendsto (fun p : NNReal ↦ eLpNorm f p μ) atTop (𝓝 (eLpNorm f ∞ μ)) := sorry

/-- Exercise 7.1.2 (1): source-facing bridge from measurable finite-exponent data to the
canonical `MemLp` statement. -/
theorem tendsto_eLpNorm_atTop_of_finite_exponent {f : Ω → ℝ} (hf_meas : Measurable f)
    (hfin : ∃ p : NNReal, 0 < p ∧ eLpNorm f p μ < ∞) :
    Tendsto (fun p : NNReal ↦ eLpNorm f p μ) atTop (𝓝 (eLpNorm f ∞ μ)) :=
  tendsto_eLpNorm_atTop_of_exists_memLp <| by
    rcases hfin with ⟨p, hp, hpfin⟩
    exact ⟨p, hp, ⟨hf_meas.aestronglyMeasurable, hpfin⟩⟩

/-- Exercise 7.1.2 (2): Clause (ii). On `ℝ` with Lebesgue measure, the measurable constant
function `1` shows that the finite-exponent integrability assumption in clause (i) is necessary. -/
-- Proof sketch: for the constant function `1` on `ℝ`, every finite `L^p` seminorm is infinite
-- because `volume univ = ∞`, while the `L^∞` seminorm is `1`; hence the finite-exponent seminorms
-- cannot converge to the `L^∞` seminorm as `p → ∞`.
theorem not_tendsto_eLpNorm_const_one_atTop :
    ¬ Tendsto (fun p : NNReal ↦ eLpNorm (fun _ : ℝ ↦ (1 : ℝ)) p volume) atTop
      (𝓝 (eLpNorm (fun _ : ℝ ↦ (1 : ℝ)) ∞ volume)) := by
  intro h
  have hconst :
      (fun p : NNReal ↦ eLpNorm (fun _ : ℝ ↦ (1 : ℝ)) p volume) =ᶠ[atTop]
        fun _ ↦ (∞ : ℝ≥0∞) := by
    filter_upwards [eventually_gt_atTop (0 : NNReal)] with p hp
    rw [eLpNorm_const' (1 : ℝ) (by exact_mod_cast hp.ne') (by simp)]
    simp [hp, one_div]
  have h' : Tendsto (fun _ : NNReal ↦ (∞ : ℝ≥0∞)) atTop
      (𝓝 (eLpNorm (fun _ : ℝ ↦ (1 : ℝ)) ∞ volume)) :=
    (tendsto_congr' hconst).mp h
  have hEq : (∞ : ℝ≥0∞) = eLpNorm (fun _ : ℝ ↦ (1 : ℝ)) ∞ volume :=
    tendsto_const_nhds_iff.mp h'
  rw [eLpNorm_exponent_top, eLpNormEssSup_const _] at hEq
  · norm_num at hEq
  · intro hvolume
    simpa [hvolume] using (Real.volume_univ : volume (Set.univ : Set ℝ) = ∞)

end MeasureTheory

/-! ### Exercise_7_1_3 (from Items/Chap07) -/
open Filter
open MeasureTheory
open scoped ENNReal Topology

/-- The `n`-th Cesàro average of the nonnegative integer translates of `f`. -/
noncomputable def integerTranslateCesaro (f : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  fun x ↦
    ((n + 1 : ℝ)⁻¹) * Finset.sum (Finset.range (n + 1)) (fun k ↦ f (x + k))

/-- Integer translation preserves `ℒ^p(λ)` because Lebesgue measure is translation invariant. -/
private theorem integerTranslate_memLp {p : ℝ≥0∞} {f : ℝ → ℝ} (hf : MemLp f p volume) (k : ℕ) :
    MemLp (fun x ↦ f (x + k)) p volume := by
  simpa [Function.comp, add_comm] using
    hf.comp_measurePreserving (measurePreserving_vadd (k : ℝ) volume)

/-- If `f ∈ ℒ^p(λ)`, then each Cesàro average of its integer translates again belongs to
`ℒ^p(λ)`. -/
private theorem integerTranslateCesaro_memLp {p : ℝ≥0∞} {f : ℝ → ℝ} (hf : MemLp f p volume)
    (n : ℕ) :
    MemLp (integerTranslateCesaro f n) p volume := by
  have hsum : MemLp (fun x ↦ Finset.sum (Finset.range (n + 1)) (fun k ↦ f (x + k))) p volume := by
    classical
    refine Finset.induction_on (Finset.range (n + 1)) ?_ ?_
    · simp
    · intro k s hk hs
      simpa [Finset.sum_insert hk] using (integerTranslate_memLp hf k).add hs
  simpa [integerTranslateCesaro, smul_eq_mul] using hsum.const_smul ((n + 1 : ℝ)⁻¹)

private instance fact_one_le_coe_ennreal_of_fact_one_lt (p : NNReal) [Fact (1 < p)] :
    Fact (1 ≤ (p : ℝ≥0∞)) :=
  ⟨by
    exact_mod_cast (Fact.out : (1 : NNReal) < p).le⟩

/-- Exercise 7.1.3: canonical `Lp`-valued form. For a finite exponent `p > 1`, if
`f ∈ ℒ^p(λ)` on `ℝ`, then the Cesàro averages of the integer translates `x ↦ f (x + k)`
converge to `0` in `Lp ℝ p volume`. -/
-- Proof sketch: view integer translation as a measure-preserving action on
-- `Lp ℝ p volume`, so each translate is an isometric copy of `f`. Prove the
-- claim first for compactly supported continuous functions, where the translates separate and the
-- averages vanish, then extend to general `MemLp` functions by density of nice functions in `L^p`.
theorem integer_translate_cesaro_tendsto_zero_inLp {p : NNReal} [Fact (1 < p)] {f : ℝ → ℝ}
    (hf : MemLp f (p : ℝ≥0∞) volume) :
    Tendsto
      (fun n ↦ (integerTranslateCesaro_memLp hf n).toLp (integerTranslateCesaro f n))
      atTop (𝓝 (0 : Lp ℝ (p : ℝ≥0∞) volume)) := sorry

/-- The textbook `eLpNorm` formulation of Exercise 7.1.3 follows from the canonical `Lp`-valued
convergence statement via `MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm''`. -/
theorem integer_translate_cesaro_tendsto_zero_in_eLpNorm {p : ℝ} (hp : 1 < p) {f : ℝ → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    Tendsto (fun n ↦ eLpNorm (integerTranslateCesaro f n) (ENNReal.ofReal p) volume) atTop
      (𝓝 0) := by
  have hp0 : 0 ≤ p := le_trans zero_le_one hp.le
  let p' : NNReal := ⟨p, hp0⟩
  have hp' : (p' : ℝ≥0∞) = ENNReal.ofReal p := by
    simpa using (ENNReal.ofReal_eq_coe_nnreal hp0).symm
  haveI : Fact (1 < p') := ⟨by exact_mod_cast hp⟩
  have hf' : MemLp f (p' : ℝ≥0∞) volume := by
    simpa [hp'] using hf
  have hCesaroMemLp : ∀ n, MemLp (integerTranslateCesaro f n) (p' : ℝ≥0∞) volume :=
    integerTranslateCesaro_memLp hf'
  simpa [hp'] using
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n ↦ integerTranslateCesaro f n) hCesaroMemLp 0
      MemLp.zero).mp (integer_translate_cesaro_tendsto_zero_inLp hf')
