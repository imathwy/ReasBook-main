import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap05.Definition_5_25

-- Declarations for this item will be appended below by the statement pipeline.

open InformationTheory MeasureTheory
open scoped BigOperators

noncomputable section

universe u
variable {E : Type u}

/-- The extended-real cross-entropy of `p` against a nonnegative mass function `q` in base `b`. -/
def crossEntropyInBase (b : LogBase) (p : PMF E) (q : E → ENNReal) : EReal :=
  -∑' e : E, ((p e : EReal) * (((Real.log (b : ℝ) : EReal)⁻¹) * ENNReal.log (q e)))

/-- The extended-real base-`b` cross-entropy is given by its defining logarithmic series. -/
@[simp] theorem crossEntropyInBase_def (b : LogBase) (p : PMF E)
    (q : E → ENNReal) :
    crossEntropyInBase b p q =
      -∑' e : E, ((p e : EReal) * (((Real.log (b : ℝ) : EReal)⁻¹) * ENNReal.log (q e))) :=
  rfl

/-- Helper for Lemma 5.26: when the comparison mass function agrees with `p`, the cross-entropy
coincides with the entropy. -/
private theorem crossEntropyInBase_eq_entropyInBase_of_eq (b : LogBase) (p : PMF E) :
    crossEntropyInBase b p p = entropyInBase b p := by
  -- Both quantities are the same defining series when `q = p`.
  simp [crossEntropyInBase, entropyInBase]

/-- Helper for Lemma 5.26: equality holds in the cross-entropy inequality for the diagonal choice
`q = p`. -/
private theorem entropyInBase_eq_crossEntropyInBase_of_eq (b : LogBase) (p : PMF E) :
    entropyInBase b p = crossEntropyInBase b p p := by
  -- This is the symmetric restatement of the diagonal compatibility lemma above.
  exact (crossEntropyInBase_eq_entropyInBase_of_eq b p).symm

/-- Helper for Lemma 5.26: if `q` vanishes at a point where `p` has positive mass, then the
cross-entropy diverges to `⊤`. -/
private theorem crossEntropyInBase_eq_top_of_exists_zero_on_support
    (b : LogBase) (hb : 1 < (b : ℝ)) (p : PMF E)
    (q : E → ENNReal) (hzero : ∃ e, e ∈ p.support ∧ q e = 0) :
    crossEntropyInBase b p q = (⊤ : EReal) := by
  rcases hzero with ⟨e, he, hqe⟩
  let f : E → EReal := fun x ↦
    ((p x : EReal) * (((Real.log (b : ℝ) : EReal)⁻¹) * ENNReal.log (q x)))
  have hsum_bot : HasSum f (⊥ : EReal) := by
    rw [HasSum]
    change Filter.Tendsto (fun s : Finset E ↦ ∑ x ∈ s, f x) Filter.atTop
      (nhds (⊥ : EReal))
    rw [EReal.tendsto_nhds_bot_iff_real]
    intro a
    have hmem :
        {s : Finset E | e ∈ s} ∈ (Filter.atTop : Filter (Finset E)) := by
      exact Filter.mem_atTop_sets.mpr ⟨{e}, by
        intro s hs
        simpa using hs⟩
    refine Filter.mem_of_superset hmem ?_
    intro s hs
    have hfe : f e = (⊥ : EReal) := by
      -- The singled-out support term is `⊥`: the logarithm contributes `⊥` and `p e` is positive.
      dsimp [f]
      have hp : (0 : EReal) < (p e : EReal) := by
        exact_mod_cast (PMF.apply_pos_iff p e).2 he
      have hlog :
          (((Real.log (b : ℝ) : EReal)⁻¹) * ENNReal.log (q e)) = (⊥ : EReal) := by
        have hpos : (0 : EReal) < ((Real.log (b : ℝ) : EReal)⁻¹) := by
          rw [← EReal.coe_inv]
          exact_mod_cast (inv_pos.mpr (Real.log_pos hb))
        simpa [hqe] using EReal.mul_bot_of_pos hpos
      simpa [hlog] using EReal.mul_bot_of_pos hp
    have hsbot : ∑ x ∈ s, f x = (⊥ : EReal) := by
      -- Every finite partial sum containing that term is already `⊥`.
      refine (WithBot.sum_eq_bot_iff).2 ?_
      exact ⟨e, by simpa using hs, hfe⟩
    change (∑ x ∈ s, f x) < (a : EReal)
    rw [hsbot]
    exact EReal.bot_lt_coe a
  -- The defining series therefore sums to `⊥`, and negating it gives `⊤`.
  have htsum : ∑' x : E, f x = (⊥ : EReal) := hsum_bot.tsum_eq
  rw [crossEntropyInBase_def]
  change -∑' x : E, f x = (⊤ : EReal)
  simp [htsum]

/-- Helper for Lemma 5.26: a sub-probability mass value is automatically finite. -/
private theorem q_apply_ne_top_of_tsum_le_one (q : E → ENNReal)
    (hq : (∑' e : E, q e) ≤ 1) (e : E) :
    q e ≠ ⊤ := by
  -- Each coordinate is bounded by the total mass, hence by `1`.
  have hq_le_one : q e ≤ 1 := (ENNReal.le_tsum e).trans hq
  exact ne_of_lt (lt_of_le_of_lt hq_le_one ENNReal.one_lt_top)

/-- Helper for Lemma 5.26: on the positive-support branch, each logarithmic gap term rewrites to
the KL remainder plus the linear correction `p_e - q_e`. -/
private theorem cross_entropy_gap_term_identity (p : PMF E) (q : E → ENNReal)
    (hq : (∑' e : E, q e) ≤ 1) (hnozero : ∀ e ∈ p.support, q e ≠ 0) (e : E) :
    (p e).toReal * (Real.log (p e).toReal - Real.log (q e).toReal) =
      (q e).toReal * klFun (((p e : ENNReal) / q e).toReal) +
        (p e).toReal - (q e).toReal := by
  by_cases hp : p e = 0
  · -- Off the support of `p`, the identity collapses to the `klFun 0 = 1` case.
    simp [hp, klFun_zero]
  · -- On the support, positivity of both masses lets us rewrite through `log (p_e / q_e)`.
    have hq' : q e ≠ 0 := hnozero e ((PMF.mem_support_iff p e).2 hp)
    have hq_top : q e ≠ ⊤ := q_apply_ne_top_of_tsum_le_one q hq e
    have hp_toReal : 0 < (p e).toReal := ENNReal.toReal_pos hp (p.apply_ne_top e)
    have hq_toReal : 0 < (q e).toReal := ENNReal.toReal_pos hq' hq_top
    rw [klFun_apply]
    rw [ENNReal.toReal_div, Real.log_div hp_toReal.ne' hq_toReal.ne']
    field_simp [hq_toReal.ne']
    ring

/-- Helper for Lemma 5.26: on the positive-support branch, each pointwise logarithmic gap is at
least the corresponding mass difference. -/
private theorem log_ratio_mul_ge_mass_difference (p : PMF E) (q : E → ENNReal)
    (hq : (∑' e : E, q e) ≤ 1) (hnozero : ∀ e ∈ p.support, q e ≠ 0) (e : E) :
    (p e).toReal * (Real.log (p e).toReal - Real.log (q e).toReal) ≥
      (p e).toReal - (q e).toReal := by
  -- Rewrite the gap as a nonnegative KL remainder plus the linear correction.
  have hid := cross_entropy_gap_term_identity p q hq hnozero e
  have hkl_nonneg : 0 ≤ (q e).toReal * klFun (((p e : ENNReal) / q e).toReal) := by
    have hq_nonneg : 0 ≤ (q e).toReal := ENNReal.toReal_nonneg
    have hkl_nonneg : 0 ≤ klFun (((p e : ENNReal) / q e).toReal) :=
      klFun_nonneg ENNReal.toReal_nonneg
    exact mul_nonneg hq_nonneg hkl_nonneg
  linarith

/-- Helper for Lemma 5.26: if `q` differs from `p` at a positive-mass point, then the pointwise
logarithmic gap is strictly larger than the mass difference. -/
private theorem log_ratio_mul_gt_mass_difference_of_ne (p : PMF E) (q : E → ENNReal)
    (hq : (∑' e : E, q e) ≤ 1) (hnozero : ∀ e ∈ p.support, q e ≠ 0) {e : E}
    (he : e ∈ p.support) (hneq : q e ≠ p e) :
    (p e).toReal * (Real.log (p e).toReal - Real.log (q e).toReal) >
      (p e).toReal - (q e).toReal := by
  -- The strict gap comes from strict positivity of `klFun` away from ratio `1`.
  have hid := cross_entropy_gap_term_identity p q hq hnozero e
  have hq0 : q e ≠ 0 := hnozero e he
  have hq_top : q e ≠ ⊤ := q_apply_ne_top_of_tsum_le_one q hq e
  have hq_real_pos : 0 < (q e).toReal := ENNReal.toReal_pos hq0 hq_top
  have hratio_ne_one : (((p e : ENNReal) / q e).toReal) ≠ 1 := by
    intro hratio
    have hdiv : (p e : ENNReal) / q e = 1 := (ENNReal.toReal_eq_one_iff _).mp hratio
    have hmul := congrArg (fun x : ENNReal ↦ q e * x) hdiv
    have hmul' : (p e : ENNReal) * (q e * (q e)⁻¹) = q e * 1 := by
      simpa only [ENNReal.div_eq_inv_mul, mul_assoc, mul_left_comm, mul_comm, one_mul] using hmul
    rw [ENNReal.mul_inv_cancel hq0 hq_top, mul_one, mul_one] at hmul'
    exact hneq hmul'.symm
  have hkl_nonneg : 0 ≤ klFun (((p e : ENNReal) / q e).toReal) :=
    klFun_nonneg ENNReal.toReal_nonneg
  have hkl_ne_zero : klFun (((p e : ENNReal) / q e).toReal) ≠ 0 := by
    intro hzero
    have hratio_eq_one :=
      (klFun_eq_zero_iff ENNReal.toReal_nonneg).mp hzero
    exact hratio_ne_one hratio_eq_one
  have hkl_pos : 0 < klFun (((p e : ENNReal) / q e).toReal) :=
    lt_of_le_of_ne hkl_nonneg (Ne.symm hkl_ne_zero)
  have hgap_pos :
      0 < (q e).toReal * klFun (((p e : ENNReal) / q e).toReal) :=
    mul_pos hq_real_pos hkl_pos
  linarith

/-- Helper for Lemma 5.26: summing the pointwise textbook inequality over a finite set gives the
finite truncation lower bound used in the support-sum argument. -/
private theorem cross_entropy_partial_sum_bound (p : PMF E) (q : E → ENNReal)
    (hq : (∑' e : E, q e) ≤ 1) (hnozero : ∀ e ∈ p.support, q e ≠ 0) (s : Finset E) :
    Finset.sum s (fun e ↦ (p e).toReal * (Real.log (p e).toReal - Real.log (q e).toReal)) ≥
      Finset.sum s (fun e ↦ ((p e).toReal - (q e).toReal)) := by
  -- Sum the pointwise lower bound over the chosen truncation.
  exact Finset.sum_le_sum fun e he ↦ log_ratio_mul_ge_mass_difference p q hq hnozero e

/-- Helper for Lemma 5.26: if a finite truncation contains a support point where `q` differs from
`p`, then the truncation inequality is strict. -/
private theorem cross_entropy_partial_sum_strict (p : PMF E) (q : E → ENNReal)
    (hq : (∑' e : E, q e) ≤ 1) (hnozero : ∀ e ∈ p.support, q e ≠ 0) (s : Finset E)
    {e : E} (he_mem : e ∈ s) (he_support : e ∈ p.support) (hneq : q e ≠ p e) :
    Finset.sum s (fun x ↦ (p x).toReal * (Real.log (p x).toReal - Real.log (q x).toReal)) >
      Finset.sum s (fun x ↦ ((p x).toReal - (q x).toReal)) := by
  classical
  -- Split off the witness index and use the strict pointwise gap there.
  let f : E → ℝ := fun x ↦
    (p x).toReal * (Real.log (p x).toReal - Real.log (q x).toReal)
  let g : E → ℝ := fun x ↦ (p x).toReal - (q x).toReal
  have hstrict :
      f e > g e :=
    log_ratio_mul_gt_mass_difference_of_ne p q hq hnozero he_support hneq
  have hweak :
      Finset.sum (s.erase e) g ≤ Finset.sum (s.erase e) f :=
    cross_entropy_partial_sum_bound p q hq hnozero (s.erase e)
  have hsum_strict :
      Finset.sum (s.erase e) g + g e < Finset.sum (s.erase e) f + f e :=
    add_lt_add_of_le_of_lt hweak hstrict
  have hs_g : Finset.sum (s.erase e) g + g e = Finset.sum s g :=
    Finset.sum_erase_add s g he_mem
  have hs_f : Finset.sum (s.erase e) f + f e = Finset.sum s f :=
    Finset.sum_erase_add s f he_mem
  have hs_g' :
      Finset.sum s (fun x ↦ (p x).toReal - (q x).toReal) =
        Finset.sum (s.erase e) g + g e := by
    simpa [g] using hs_g.symm
  have hs_f' :
      Finset.sum s (fun x ↦ (p x).toReal * (Real.log (p x).toReal - Real.log (q x).toReal)) =
        Finset.sum (s.erase e) f + f e := by
    simpa [f] using hs_f.symm
  rw [hs_g', hs_f']
  exact hsum_strict

/-- Helper for Lemma 5.26: the comparison measure `Measure.count.withDensity q` agrees with
`p.toMeasure` exactly when `q` agrees pointwise with `p`. -/
private theorem comparison_measure_eq_pmf_iff (p : PMF E) (q : E → ENNReal) :
    letI : MeasurableSpace E := ⊤
    letI : MeasurableSingletonClass E := ⟨fun _ ↦ trivial⟩
    let ν : Measure E := Measure.count.withDensity q
    ν = p.toMeasure ↔ q = (p : E → ENNReal) := by
  letI : MeasurableSpace E := ⊤
  letI : MeasurableSingletonClass E := ⟨fun _ ↦ trivial⟩
  let ν : Measure E := Measure.count.withDensity q
  constructor
  · intro hν
    -- Compare the two measures on singletons to recover the pointwise masses.
    ext e
    have hsingle := congrArg (fun μ : Measure E ↦ μ {e}) hν
    simpa [ν, withDensity_apply, lintegral_count, PMF.toMeasure_apply_singleton] using hsingle
  · intro hpq
    -- Once the densities agree pointwise, both weighted counting measures have the same values on
    -- every measurable set.
    ext s hs
    have hcount :
        (Measure.count.withDensity (fun e ↦ (p e : ENNReal))) s = p.toMeasure s := by
      rw [withDensity_apply _ hs, ← lintegral_indicator hs, lintegral_count]
      simpa using (p.toMeasure_apply hs).symm
    simpa [ν, hpq] using hcount

/-- Helper for Lemma 5.26: on the positive-support branch, `p.toMeasure` is the weighted
comparison measure with density `p / q`. -/
private theorem pmf_toMeasure_eq_withDensity_comparison (p : PMF E) (q : E → ENNReal)
    (hq : (∑' e : E, q e) ≤ 1) (hnozero : ∀ e ∈ p.support, q e ≠ 0) :
    letI : MeasurableSpace E := ⊤
    letI : MeasurableSingletonClass E := ⟨fun _ ↦ trivial⟩
    let ν : Measure E := Measure.count.withDensity q
    p.toMeasure = ν.withDensity (fun e ↦ (p e : ENNReal) / q e) := by
  letI : MeasurableSpace E := ⊤
  letI : MeasurableSingletonClass E := ⟨fun _ ↦ trivial⟩
  let ν : Measure E := Measure.count.withDensity q
  calc
    p.toMeasure = Measure.count.withDensity (fun e ↦ (p e : ENNReal)) := by
      -- Rewrite `p.toMeasure` itself as a weighted counting measure.
      refine Measure.ext fun s hs ↦ ?_
      rw [p.toMeasure_apply hs, withDensity_apply _ hs]
      rw [← lintegral_indicator hs (fun e ↦ (p e : ENNReal)), lintegral_count]
    _ = (Measure.count.withDensity q).withDensity (fun e ↦ (p e : ENNReal) / q e) := by
      -- Route correction: compose the counting measure with the density `q` first, then identify
      -- the remaining Radon-Nikodym factor pointwise as `p / q`.
      rw [← withDensity_mul (Measure.count : Measure E)]
      · refine withDensity_congr_ae ?_
        refine Filter.Eventually.of_forall ?_
        intro e
        by_cases hp : p e = 0
        · simp [hp]
        · have hq0 : q e ≠ 0 := hnozero e ((PMF.mem_support_iff p e).2 hp)
          have hq_top : q e ≠ ⊤ := q_apply_ne_top_of_tsum_le_one q hq e
          have hmul : q e * (p e / q e) = p e := by
            calc
              q e * (p e / q e) = q e * (q e)⁻¹ * p e := by
                rw [ENNReal.div_eq_inv_mul, mul_assoc]
              _ = p e := by
                rw [ENNReal.mul_inv_cancel hq0 hq_top, one_mul]
          simpa [Pi.mul_apply] using hmul.symm
      · fun_prop
      · fun_prop
    _ = ν.withDensity (fun e ↦ (p e : ENNReal) / q e) := by
      rfl

/-- Helper for Lemma 5.26: the discrete KL divergence against the comparison measure is exactly the
sum of the ambient gap terms. -/
private theorem cross_entropy_gap_eq_klDiv (p : PMF E) (q : E → ENNReal)
    (hq : (∑' e : E, q e) ≤ 1) (hnozero : ∀ e ∈ p.support, q e ≠ 0) :
    letI : MeasurableSpace E := ⊤
    letI : MeasurableSingletonClass E := ⟨fun _ ↦ trivial⟩
    let ν : Measure E := Measure.count.withDensity q
    klDiv p.toMeasure ν =
      ∑' e : E, ENNReal.ofReal ((q e).toReal * klFun (((p e : ENNReal) / q e).toReal)) := by
  letI : MeasurableSpace E := ⊤
  letI : MeasurableSingletonClass E := ⟨fun _ ↦ trivial⟩
  let ν : Measure E := Measure.count.withDensity q
  letI : IsFiniteMeasure ν := by
    -- The sub-probability bound makes the comparison measure finite.
    refine ⟨?_⟩
    change (Measure.count.withDensity q) Set.univ < (⊤ : ENNReal)
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_count]
    exact lt_of_le_of_lt hq ENNReal.one_lt_top
  have hpν : p.toMeasure ≪ ν := by
    rw [pmf_toMeasure_eq_withDensity_comparison p q hq hnozero]
    exact withDensity_absolutelyContinuous _ _
  change klDiv p.toMeasure ν =
      ∑' e : E, ENNReal.ofReal ((q e).toReal * klFun (((p e : ENNReal) / q e).toReal))
  rw [klDiv_eq_lintegral_klFun_of_ac hpν]
  have hrn : p.toMeasure.rnDeriv ν =ᵐ[ν] fun e ↦ (p e : ENNReal) / q e := by
    rw [pmf_toMeasure_eq_withDensity_comparison p q hq hnozero]
    exact Measure.rnDeriv_withDensity ν (by fun_prop)
  have hfun :
      (fun x ↦ ENNReal.ofReal (klFun (p.toMeasure.rnDeriv ν x).toReal)) =ᵐ[ν]
        fun e ↦ ENNReal.ofReal (klFun (((p e : ENNReal) / q e).toReal)) := by
    -- Replace the Radon-Nikodym derivative by the explicit density `p / q`.
    filter_upwards [hrn] with x hx
    simp [hx]
  rw [lintegral_congr_ae hfun]
  rw [lintegral_withDensity_eq_lintegral_mul Measure.count]
  · rw [lintegral_count]
    congr with e
    have hq_top : q e ≠ ⊤ := q_apply_ne_top_of_tsum_le_one q hq e
    have hq_toReal_nonneg : 0 ≤ (q e).toReal := ENNReal.toReal_nonneg
    calc
      q e * ENNReal.ofReal (klFun (((p e : ENNReal) / q e).toReal)) =
          ENNReal.ofReal (q e).toReal *
            ENNReal.ofReal (klFun (((p e : ENNReal) / q e).toReal)) := by
        rw [ENNReal.ofReal_toReal hq_top]
      _ = ENNReal.ofReal ((q e).toReal * klFun (((p e : ENNReal) / q e).toReal)) := by
        rw [← ENNReal.ofReal_mul hq_toReal_nonneg]
  · fun_prop
  · fun_prop

/-- Helper for Lemma 5.26: on the positive-support branch, the cross-entropy splits as the entropy
plus the KL divergence against the comparison measure and the mass deficit of `q`. -/
private theorem cross_entropy_gap_full_decomposition (b : LogBase) (p : PMF E)
    (q : E → ENNReal) (hq : (∑' e : E, q e) ≤ 1)
    (hnozero : ∀ e ∈ p.support, q e ≠ 0) :
    letI : MeasurableSpace E := ⊤
    letI : MeasurableSingletonClass E := ⟨fun _ ↦ trivial⟩
    let ν : Measure E := Measure.count.withDensity q
    crossEntropyInBase b p q =
      entropyInBase b p +
        (((Real.log (b : ℝ) : EReal)⁻¹) *
          (((klDiv p.toMeasure ν) + (1 - ν Set.univ)) : ENNReal)) := by
  -- Route correction: the stalled ambient-`tsum` identity is replaced by the KL-form target.
  -- TODO: the pointwise identity, the finite-truncation lower bound, and the support adapter are
  -- now proved above. The remaining blocker is the series-level packaging step: pass from the
  -- verified finite-set inequality to the full `EReal` identity, using `cross_entropy_gap_eq_klDiv`
  -- together with the direct evaluation of `(Measure.count.withDensity q) Set.univ`.
  sorry

/-- Helper for Lemma 5.26: on the finite-entropy positive-support branch, equality forces the
comparison mass function to agree pointwise with `p`. -/
private theorem cross_entropy_remainder_eq_zero_iff (b : LogBase) (hb : 1 < (b : ℝ))
    (p : PMF E) (q : E → ENNReal) (hq : (∑' e : E, q e) ≤ 1)
    (hnozero : ∀ e ∈ p.support, q e ≠ 0) (htop : entropyInBase b p ≠ (⊤ : EReal)) :
    entropyInBase b p = crossEntropyInBase b p q ↔ q = (p : E → ENNReal) := by
  letI : MeasurableSpace E := ⊤
  letI : MeasurableSingletonClass E := ⟨fun _ ↦ trivial⟩
  let ν : Measure E := Measure.count.withDensity q
  letI : IsFiniteMeasure ν := by
    -- The sub-probability bound makes the comparison measure finite.
    refine ⟨?_⟩
    change (Measure.count.withDensity q) Set.univ < (⊤ : ENNReal)
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_count]
    exact lt_of_le_of_lt hq ENNReal.one_lt_top
  constructor
  · intro hEq
    have hcoeff_pos : (0 : EReal) < ((Real.log (b : ℝ) : EReal)⁻¹) := by
      rw [← EReal.coe_inv]
      exact_mod_cast inv_pos.mpr (Real.log_pos hb)
    have hcoeff_ne_zero : ((Real.log (b : ℝ) : EReal)⁻¹) ≠ 0 := ne_of_gt hcoeff_pos
    have hcoeff_nonneg : (0 : EReal) ≤ ((Real.log (b : ℝ) : EReal)⁻¹) :=
      hcoeff_pos.le
    have hentropy_ne_bot : entropyInBase b p ≠ (⊥ : EReal) := by
      have hsum_nonpos :
          (∑' e : E, ((p e : EReal) * (((Real.log (b : ℝ) : EReal)⁻¹) * ENNReal.log (p e)))) ≤
            (0 : EReal) := by
        refine tsum_nonpos ?_
        intro e
        have hp_nonneg : (0 : EReal) ≤ (p e : EReal) := by
          exact_mod_cast (show (0 : ENNReal) ≤ p e by simp)
        have hlog_nonpos : ENNReal.log (p e) ≤ 0 := by
          rw [ENNReal.log_le_zero_iff]
          exact p.coe_le_one e
        have hscaled_nonpos :
            (((Real.log (b : ℝ) : EReal)⁻¹) * ENNReal.log (p e)) ≤ 0 := by
          exact mul_nonpos_of_nonneg_of_nonpos hcoeff_nonneg hlog_nonpos
        exact mul_nonpos_of_nonneg_of_nonpos hp_nonneg hscaled_nonpos
      have hsum_ne_top :
          ∑' e : E, ((p e : EReal) * (((Real.log (b : ℝ) : EReal)⁻¹) * ENNReal.log (p e))) ≠
            (⊤ : EReal) := by
        have hzero_lt_top : (0 : EReal) < ⊤ := by simp
        exact ne_of_lt (lt_of_le_of_lt hsum_nonpos hzero_lt_top)
      rw [entropyInBase_def]
      intro hbot
      exact hsum_ne_top ((EReal.neg_eq_bot_iff).mp hbot)
    -- Rewrite equality so that the nonnegative KL remainder is the only possible obstruction.
    rw [cross_entropy_gap_full_decomposition b p q hq hnozero] at hEq
    let rem : ENNReal := klDiv p.toMeasure ν + (1 - ν Set.univ)
    have hrem_nonneg : (0 : EReal) ≤ (rem : EReal) := by
      exact_mod_cast (bot_le : (0 : ENNReal) ≤ rem)
    have hmul_nonneg :
        (0 : EReal) ≤ ((Real.log (b : ℝ) : EReal)⁻¹) * (rem : EReal) := by
      exact mul_nonneg hcoeff_nonneg hrem_nonneg
    have hEq' :
        ((entropyInBase b p).toReal : EReal) =
          ((entropyInBase b p).toReal : EReal) +
            (((Real.log (b : ℝ) : EReal)⁻¹) * (rem : EReal)) := by
      -- Replace the finite entropy value by its real coercion before cancelling it.
      have hcoe : entropyInBase b p = ((entropyInBase b p).toReal : EReal) := by
        symm
        exact EReal.coe_toReal htop hentropy_ne_bot
      have hEq'' := hEq
      rw [hcoe] at hEq''
      simpa [rem, ν] using hEq''
    have hmul_le_zero :
        ((Real.log (b : ℝ) : EReal)⁻¹) * (rem : EReal) ≤ 0 := by
      have hle :
          ((entropyInBase b p).toReal : EReal) +
              (((Real.log (b : ℝ) : EReal)⁻¹) * (rem : EReal)) ≤
            ((entropyInBase b p).toReal : EReal) + 0 := by
        simpa [hEq', add_comm, add_left_comm, add_assoc] using le_of_eq hEq'.symm
      exact EReal.addLECancellable_coe (entropyInBase b p).toReal hle
    have hmul_zero :
        ((Real.log (b : ℝ) : EReal)⁻¹) * (rem : EReal) = 0 := by
      exact le_antisymm hmul_le_zero hmul_nonneg
    have hrem_zero_e : (rem : EReal) = 0 := by
      exact (eq_zero_or_eq_zero_of_mul_eq_zero hmul_zero).resolve_left hcoeff_ne_zero
    have hrem_zero : rem = 0 := by
      simpa using hrem_zero_e
    have hkl_zero : klDiv p.toMeasure ν = 0 := by
      exact (add_eq_zero_iff_of_nonneg bot_le bot_le).mp hrem_zero |>.1
    -- Converse Gibbs inequality identifies the comparison measure with `p.toMeasure`.
    have hν_eq : ν = p.toMeasure := by
      have hzero_iff : klDiv p.toMeasure ν = 0 ↔ p.toMeasure = ν := klDiv_eq_zero_iff
      exact (hzero_iff.mp hkl_zero).symm
    exact (comparison_measure_eq_pmf_iff p q).mp hν_eq
  · intro hpq
    -- Once `q` agrees with `p`, the defining logarithmic series coincide termwise.
    cases hpq
    exact entropyInBase_eq_crossEntropyInBase_of_eq b p

-- Proof sketch: rewrite the difference between the two sides as the base-change factor
-- `(Real.log (b : ℝ))⁻¹` times the Kullback-Leibler divergence term
-- `∑ p(e) * log (p(e) / q(e))`, use the standard inequality `log x ≤ x - 1`, and identify the
-- equality case from strictness unless the entropy side is already `⊤`.
/-- Lemma 5.26, inequality part: the base-`b` entropy of `p` is bounded above by the base-`b`
cross-entropy against any sub-probability mass function `q`. -/
theorem entropyInBase_le_crossEntropyInBase (b : LogBase) (hb : 1 < (b : ℝ)) (p : PMF E)
    (q : E → ENNReal) (hq : (∑' e : E, q e) ≤ 1) :
    entropyInBase b p ≤ crossEntropyInBase b p q := by
  classical
  -- Route correction: the viable proof has to split first on whether `q` vanishes on `p.support`,
  -- then compare the positive-support branch through a KL-type nonnegative remainder.
  by_cases hzero : ∃ e, e ∈ p.support ∧ q e = 0
  · -- On the singular branch, the cross-entropy is already `⊤`.
    rw [crossEntropyInBase_eq_top_of_exists_zero_on_support b hb p q hzero]
    exact le_top
  · -- The positive-support branch is controlled by the nonnegative full-index KL remainder.
    have hnozero : ∀ e ∈ p.support, q e ≠ 0 := by
      intro e he hqe
      exact hzero ⟨e, he, hqe⟩
    letI : MeasurableSpace E := ⊤
    letI : MeasurableSingletonClass E := ⟨fun _ ↦ trivial⟩
    rw [cross_entropy_gap_full_decomposition b p q hq hnozero]
    have hcoeff_nonneg : (0 : EReal) ≤ ((Real.log (b : ℝ) : EReal)⁻¹) := by
      rw [← EReal.coe_inv]
      exact_mod_cast inv_nonneg.mpr (le_of_lt (Real.log_pos hb))
    have hrem_nonneg :
        (0 : EReal) ≤
          (((klDiv p.toMeasure (Measure.count.withDensity q)) +
              (1 - (Measure.count.withDensity q) Set.univ)) : ENNReal) := by
      exact_mod_cast (bot_le :
        (0 : ENNReal) ≤
          klDiv p.toMeasure (Measure.count.withDensity q) +
            (1 - (Measure.count.withDensity q) Set.univ))
    have hmul_nonneg :
        (0 : EReal) ≤
          ((Real.log (b : ℝ) : EReal)⁻¹ *
            (((klDiv p.toMeasure (Measure.count.withDensity q)) +
                (1 - (Measure.count.withDensity q) Set.univ)) : ENNReal)) := by
      exact mul_nonneg hcoeff_nonneg hrem_nonneg
    -- Adding a nonnegative remainder to the entropy yields the desired comparison.
    exact le_add_of_nonneg_right hmul_nonneg

/-- Lemma 5.26, equality part: for a sub-probability mass function `q`, equality between entropy
and cross-entropy occurs exactly when the entropy is infinite or `q` agrees pointwise with `p`. -/
theorem entropyInBase_eq_crossEntropyInBase_iff (b : LogBase) (hb : 1 < (b : ℝ)) (p : PMF E)
    (q : E → ENNReal) (hq : (∑' e : E, q e) ≤ 1) :
    entropyInBase b p = crossEntropyInBase b p q ↔
      entropyInBase b p = (⊤ : EReal) ∨ q = (p : E → ENNReal) := by
  constructor
  · intro hEq
    by_cases htop : entropyInBase b p = (⊤ : EReal)
    · -- If the entropy is already infinite, this is one of the stated equality cases.
      exact Or.inl htop
    · -- On the finite-entropy branch, equality can only happen when the KL remainder vanishes.
      have hcross_ne_top : crossEntropyInBase b p q ≠ (⊤ : EReal) := by
        rw [← hEq]
        exact htop
      have hnozero : ∀ e ∈ p.support, q e ≠ 0 := by
        intro e he hqe
        exact hcross_ne_top (crossEntropyInBase_eq_top_of_exists_zero_on_support b hb p q
          ⟨e, he, hqe⟩)
      exact Or.inr ((cross_entropy_remainder_eq_zero_iff b hb p q hq hnozero htop).1 hEq)
  · intro h
    rcases h with htop | hpq
    · -- The inequality already forces the cross-entropy to be `⊤` once the entropy is `⊤`.
      have hle : entropyInBase b p ≤ crossEntropyInBase b p q :=
        entropyInBase_le_crossEntropyInBase b hb p q hq
      have hcross_top : crossEntropyInBase b p q = (⊤ : EReal) := by
        have htop_le : (⊤ : EReal) ≤ crossEntropyInBase b p q := by
          rw [← htop]
          exact hle
        exact le_antisymm le_top htop_le
      rw [htop, hcross_top]
    · -- The diagonal case has already been reduced to the defining-series identity.
      cases hpq
      exact entropyInBase_eq_crossEntropyInBase_of_eq b p
