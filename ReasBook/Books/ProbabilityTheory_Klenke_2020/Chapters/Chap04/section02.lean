import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_4_2_1 (from Items/Chap04) -/
open MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

-- Proof sketch: consider the superlevel sets `A_t = {ω | t ≤ |f ω|}`. For `t > 0`,
-- `Integrable.measure_norm_ge_lt_top` gives `μ A_t < ∞`. Choose `t` so that the tail `L¹`-mass of
-- `|f|` on `A_tᶜ = {ω | |f ω| < t}` is less than `ε`, then control the complementary set integral
-- using `norm_integral_le_integral_norm` and rewrite the difference with `integral_add_compl`.
/-- Exercise 4.2.1: every integrable real-valued function admits a measurable set of finite
measure whose complementary `L¹`-mass is less than `ε`. -/
theorem exists_set_finite_measure_integral_abs_compl_lt_of_integrable
    {f : Ω → ℝ} (hf : Integrable f μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Set Ω, MeasurableSet A ∧ μ A < ⊤ ∧
      ∫ x in Aᶜ, |f x| ∂μ < ε := sorry

/-- Textbook reformulation of Exercise 4.2.1. -/
theorem exists_set_finite_measure_integral_sub_lt_of_integrable
    {f : Ω → ℝ} (hf : Integrable f μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Set Ω, MeasurableSet A ∧ μ A < ⊤ ∧
      |(∫ x in A, f x ∂μ) - ∫ x, f x ∂μ| < ε := by
  obtain ⟨A, hA, hμA, htail⟩ := exists_set_finite_measure_integral_abs_compl_lt_of_integrable hf hε
  refine ⟨A, hA, hμA, ?_⟩
  have hsub : (∫ x in A, f x ∂μ) - ∫ x, f x ∂μ = -(∫ x in Aᶜ, f x ∂μ) := by
    have hadd := integral_add_compl hA hf
    linarith
  have hnorm : |∫ x in Aᶜ, f x ∂μ| ≤ ∫ x in Aᶜ, |f x| ∂μ := by
    rw [← Real.norm_eq_abs]
    let ν : Measure Ω := μ.restrict Aᶜ
    change ‖∫ x, f x ∂ν‖ ≤ ∫ x, ‖f x‖ ∂ν
    simpa [ν] using norm_integral_le_integral_norm (fun x ↦ f x)
  calc
    |(∫ x in A, f x ∂μ) - ∫ x, f x ∂μ|
        = |∫ x in Aᶜ, f x ∂μ| := by rw [hsub, abs_neg]
    _ ≤ ∫ x in Aᶜ, |f x| ∂μ := hnorm
    _ < ε := htail

/-! ### Definition_4_2 (from Items/Chap04) -/
universe u

open MeasureTheory
open scoped BigOperators

variable {Ω : Type u} [MeasurableSpace Ω]

/- Definition 4.2: The textbook map `I : E⁺ → [0, ∞]` is the canonical integral of a nonnegative
simple function, namely `MeasureTheory.SimpleFunc.lintegral`. -/
recall MeasureTheory.SimpleFunc.lintegral

-- Proof sketch: use additivity of `SimpleFunc.lintegral` over a finite sum of restricted constant
-- simple functions, then evaluate each summand with `SimpleFunc.restrict_const_lintegral`.
/-- Canonical finite-sum form of Definition 4.2: a finite sum of restricted constant simple
functions integrates to the corresponding weighted sum of the measures of its measurable pieces. -/
theorem simpleFunc_lintegral_finset_sum_restrict_const
    (μ : Measure Ω) {ι : Type*} (s : Finset ι) (A : ι → Set Ω) (α : ι → ENNReal)
    (hA : ∀ i, MeasurableSet (A i)) :
    (∑ i ∈ s, (SimpleFunc.const Ω (α i)).restrict (A i)).lintegral μ =
      ∑ i ∈ s, α i * μ (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert i s hi hs =>
      simp [hi, hs, hA i, SimpleFunc.add_lintegral, SimpleFunc.restrict_const_lintegral]

/-- `Fin n`-indexed textbook form of Definition 4.2, obtained from
`simpleFunc_lintegral_finset_sum_restrict_const` by taking `s = Finset.univ`. -/
theorem simpleFunc_lintegral_eq_sum_of_indicator
    (μ : Measure Ω) {n : ℕ} (A : Fin n → Set Ω) (α : Fin n → ENNReal)
    (hA : ∀ i, MeasurableSet (A i)) :
    (∑ i, (SimpleFunc.const Ω (α i)).restrict (A i)).lintegral μ = ∑ i, α i * μ (A i) := by
  simpa using simpleFunc_lintegral_finset_sum_restrict_const μ Finset.univ A α hA

/-! ### Exercise_4_2_2 (from Items/Chap04) -/
open Filter MeasureTheory
open scoped Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

-- Proof sketch: apply Fatou's lemma to the nonnegative functions `f - min (f_n) f` and
-- `f_n - min (f_n) f` to identify the limit of the integrals of `min (f_n) f`, deduce that `f`
-- is integrable from the assumed convergence of `∫ f_n`, and then rewrite `‖f_n - f‖` using the
-- decomposition through `min (f_n) f`.
/-- Exercise 4.2.2: if nonnegative integrable functions `f_n` converge almost everywhere to a
function `f` and the integrals `∫ f_n dμ` converge to `I`, then `f` is integrable and the
`L¹`-distance to `f` has limit `I - ∫ f dμ`. -/
theorem scheffe_of_nonnegative_ae_tendsto
    {fSeq : ℕ → Ω → ℝ} {f : Ω → ℝ} {I : ℝ}
    (hfSeq_int : ∀ n, Integrable (fSeq n) μ)
    (hfSeq_nonneg : ∀ n, 0 ≤ᵐ[μ] fSeq n)
    (h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n ↦ fSeq n x) atTop (𝓝 (f x)))
    (h_integral_tendsto : Tendsto (fun n ↦ ∫ x, fSeq n x ∂μ) atTop (𝓝 I)) :
    Integrable f μ ∧
      Tendsto (fun n ↦ ∫ x, ‖fSeq n x - f x‖ ∂μ) atTop
        (𝓝 (I - ∫ x, f x ∂μ)) := sorry

/-! ### Exercise_4_2_3 (from Items/Chap04) -/
open MeasureTheory Set

universe u

variable {E : Type u} [NormedAddCommGroup E]

-- Proof sketch: apply Tonelli/Fubini to the nonnegative function `(n, t) ↦ ‖f ((n + 1) * t)‖` on
-- `ℕ × [0, ∞)`, use the change of variables `x = (n + 1) t` to bound the iterated integral by a
-- convergent multiple of `∫_[0,∞) ‖f x‖ dx`, and conclude that the sampled series is absolutely
-- summable for almost every `t`.
theorem ae_summable_norm_at_nat_multiples_of_integrableOn_Ici (f : ℝ → E)
    (hf : IntegrableOn f (Ici 0)) :
    ∀ᵐ t ∂(volume.restrict (Ici 0)), Summable (fun n ↦ ‖f ((n + 1) * t)‖) := sorry

/-- Exercise 4.2.3: if `f` is Lebesgue integrable on `[0, ∞)`, then for Lebesgue-almost every
`t ∈ [0, ∞)` the sampled series `∑ n = 1 to ∞, f (n t)` converges absolutely. In Lean's `0`-based
indexing, this is the summability of `n ↦ |f ((n + 1) * t)|`. -/
theorem ae_summable_abs_at_nat_multiples_of_integrableOn_Ici (f : ℝ → ℝ)
    (hf : IntegrableOn f (Ici 0)) :
    ∀ᵐ t ∂(volume.restrict (Ici 0)), Summable (fun n ↦ |f ((n + 1) * t)|) := by
  simpa [Real.norm_eq_abs] using ae_summable_norm_at_nat_multiples_of_integrableOn_Ici f hf

/-! ### Exercise_4_2_4 (from Items/Chap04) -/
open MeasureTheory Set
open scoped Topology

-- Proof sketch: use the regularity of Lebesgue measure to choose an open set `U ⊇ A` with
-- `volume (U \ A) < ε / 2` and a compact set `C ⊆ A` with `volume (A \ C) < ε / 2`. Let
-- `D := Uᶜ`, so `D` is closed and contained in `Aᶜ`. Apply
-- `exists_continuous_one_zero_of_isCompact` to the disjoint compact/closed pair `C` and `D` to
-- obtain a continuous cutoff `φ` with values in `[0, 1]` and `1_C ≤ φ ≤ 1_{ℝ \ D}`. The
-- pointwise sandwich bounds reduce the `L¹` error to the two regularity errors.
/-- Exercise 4.2.4: every Borel set `A ⊆ ℝ` of finite Lebesgue measure admits a compact subset
`C ⊆ A`, a closed set `D ⊆ Aᶜ`, and a continuous cutoff `φ` with values in `[0, 1]` such that
`1_C ≤ φ ≤ 1_{ℝ \ D}` and the `L¹` distance between `1_A` and `φ` is less than `ε`. -/
theorem exists_compact_closed_continuous_indicator_l1_sub_lt
    {A : Set ℝ} (hA : MeasurableSet A) (hA_fin : volume A < ⊤)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (C D : Set ℝ) (φ : C(ℝ, ℝ)),
      IsCompact C ∧
        C ⊆ A ∧
        IsClosed D ∧
        D ⊆ Aᶜ ∧
        EqOn φ 1 C ∧
        EqOn φ 0 D ∧
        (∀ x, φ x ∈ Set.Icc (0 : ℝ) 1) ∧
        (∫ x, |A.indicator (fun _ ↦ (1 : ℝ)) x - φ x| ∂volume) < ε := by
  have hε_half : 0 < ε / 2 := by linarith
  have hε_half_ne : ENNReal.ofReal (ε / 2) ≠ 0 := by
    simpa [ENNReal.ofReal_ne_zero_iff] using hε_half
  obtain ⟨C, hCA, hC_compact, hC_lt⟩ :=
    hA.exists_isCompact_diff_lt hA_fin.ne hε_half_ne
  obtain ⟨U, hAU, hU_open, hU_fin, hU_lt⟩ :=
    hA.exists_isOpen_diff_lt hA_fin.ne hε_half_ne
  obtain ⟨φ, hφC, hφD, hφ_compactSupport, hφ_range⟩ :=
    exists_continuous_one_zero_of_isCompact hC_compact hU_open.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr (hCA.trans hAU))
  have hA_indicator_int : Integrable (A.indicator (fun _ ↦ (1 : ℝ))) volume := by
    rw [integrable_indicator_iff hA]
    exact integrableOn_const hA_fin.ne
  have hφ_int : Integrable φ volume :=
    φ.continuous.integrable_of_hasCompactSupport hφ_compactSupport
  have hAC_meas : MeasurableSet (A \ C) :=
    hA.diff hC_compact.isClosed.measurableSet
  have hUA_meas : MeasurableSet (U \ A) :=
    hU_open.measurableSet.diff hA
  have hAC_fin : volume (A \ C) ≠ ⊤ :=
    (measure_mono diff_subset).trans_lt hA_fin |>.ne
  have hUA_fin : volume (U \ A) ≠ ⊤ :=
    (measure_mono diff_subset).trans_lt hU_fin |>.ne
  have hAC_int : Integrable ((A \ C).indicator (fun _ ↦ (1 : ℝ))) volume := by
    rw [integrable_indicator_iff hAC_meas]
    exact integrableOn_const hAC_fin
  have hUA_int : Integrable ((U \ A).indicator (fun _ ↦ (1 : ℝ))) volume := by
    rw [integrable_indicator_iff hUA_meas]
    exact integrableOn_const hUA_fin
  have h_bound :
      ∀ x,
        |A.indicator (fun _ ↦ (1 : ℝ)) x - φ x| ≤
          (A \ C).indicator (fun _ ↦ (1 : ℝ)) x + (U \ A).indicator (fun _ ↦ (1 : ℝ)) x := by
    intro x
    by_cases hxA : x ∈ A
    · by_cases hxC : x ∈ C
      · simp [hxA, hxC, hφC hxC]
      · have hφx_le : φ x ≤ 1 := (hφ_range x).2
        have hφx_nonneg : 0 ≤ φ x := (hφ_range x).1
        have habs : |1 - φ x| ≤ 1 := by
          rw [abs_of_nonneg (sub_nonneg.mpr hφx_le)]
          linarith
        simpa [hxA, hxC] using habs
    · by_cases hxU : x ∈ U
      · have hφx_nonneg : 0 ≤ φ x := (hφ_range x).1
        have habs : |0 - φ x| ≤ 1 := by
          rw [zero_sub, abs_neg, abs_of_nonneg hφx_nonneg]
          exact (hφ_range x).2
        simpa [hxA, hxU] using habs
      · have hφx : φ x = 0 := hφD hxU
        simp [hxA, hxU, hφx]
  have h_rhs_int :
      Integrable
        (fun x ↦
          (A \ C).indicator (fun _ ↦ (1 : ℝ)) x +
            (U \ A).indicator (fun _ ↦ (1 : ℝ)) x) volume :=
    hAC_int.add hUA_int
  have hC_real_lt : volume.real (A \ C) < ε / 2 :=
    ENNReal.toReal_lt_of_lt_ofReal hC_lt
  have hU_real_lt : volume.real (U \ A) < ε / 2 :=
    ENNReal.toReal_lt_of_lt_ofReal hU_lt
  refine ⟨C, Uᶜ, φ, hC_compact, hCA, hU_open.isClosed_compl, compl_subset_compl.mpr hAU, hφC,
    hφD, hφ_range, ?_⟩
  calc
    ∫ x, |A.indicator (fun _ ↦ (1 : ℝ)) x - φ x| ∂volume
        ≤ ∫ x,
            ((A \ C).indicator (fun _ ↦ (1 : ℝ)) x +
              (U \ A).indicator (fun _ ↦ (1 : ℝ)) x) ∂volume :=
      integral_mono (hA_indicator_int.sub hφ_int).norm h_rhs_int h_bound
    _ = volume.real (A \ C) + volume.real (U \ A) := by
      rw [integral_add hAC_int hUA_int]
      congr 1
      · simpa using
          (integral_indicator_one hAC_meas :
            ∫ x, (A \ C).indicator (fun _ ↦ (1 : ℝ)) x ∂volume = volume.real (A \ C))
      · simpa using
          (integral_indicator_one hUA_meas :
            ∫ x, (U \ A).indicator (fun _ ↦ (1 : ℝ)) x ∂volume = volume.real (U \ A))
    _ < ε := by linarith

/-! ### Exercise_4_2_5 (from Items/Chap04) -/
open scoped ENNReal
open MeasureTheory

/-- Exercise 4.2.5: every real-valued `L^p` function on `ℝ` with respect to Lebesgue measure can
be approximated arbitrarily well in `eLpNorm` by a continuous real-valued function. -/
-- Proof sketch: apply the canonical smooth compact-support approximation theorem
-- `MemLp.exist_eLpNorm_sub_le` with tolerance `ε / 2`, then forget smoothness to continuity and
-- upgrade `≤ ENNReal.ofReal (ε / 2)` to the strict inequality required here.
theorem exists_continuous_eLpNorm_sub_lt_of_memLp
    {p : ℝ} (hp : 1 ≤ p) {f : ℝ → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) volume) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℝ → ℝ,
      Continuous h ∧ eLpNorm (f - h) (ENNReal.ofReal p) volume < ENNReal.ofReal ε := by
  have hε₂ : 0 < ε / 2 := by positivity
  have hp' : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  obtain ⟨h, _hh_compact, hh_smooth, hh_le⟩ :=
    hf.exist_eLpNorm_sub_le ENNReal.ofReal_ne_top hp' hε₂
  have hhalf_lt : ε / 2 < ε := by linarith
  have hε₂_lt : ENNReal.ofReal (ε / 2) < ENNReal.ofReal ε := by
    simpa using (ENNReal.ofReal_lt_ofReal_iff hε).2 hhalf_lt
  exact ⟨h, hh_smooth.continuous, lt_of_le_of_lt hh_le hε₂_lt⟩

/-! ### Exercise_4_2_6 (from Items/Chap04) -/
open MeasureTheory
open scoped BigOperators ENNReal

/-- A real-valued step function on `ℝ` is constant on the finitely many intervals cut out by a
strictly increasing finite family of breakpoints, namely on `(-∞, t₀]`, on each
`(tᵢ, tᵢ₊₁]`, and on `(tₙ, ∞)`. -/
def IsStepFunction (h : ℝ → ℝ) : Prop :=
  ∃ n : ℕ, ∃ t : Fin (n + 1) → ℝ, StrictMono t ∧
    ∃ a b : ℝ, ∃ α : Fin n → ℝ,
      h = fun x ↦
        (Set.Iic (t 0)).indicator (fun _ ↦ a) x +
          ∑ k, (Set.Ioc (t (Fin.castSucc k)) (t k.succ)).indicator (fun _ ↦ α k) x +
            (Set.Ioi (t (Fin.last n))).indicator (fun _ ↦ b) x

-- Proof sketch: unfold the representation of a step function, note that `Set.Iic a`,
-- `Set.Ioc a b`, and `Set.Ioi a` are measurable in `ℝ`, each indicator summand is measurable, and
-- finite sums preserve measurability.
/-- Every real-valued step function is measurable. -/
theorem IsStepFunction.measurable {h : ℝ → ℝ} (hh : IsStepFunction h) :
    Measurable h := sorry

namespace IsStepFunction

/-- A real-valued step function on `ℝ` has finite range. -/
theorem finite_range {h : ℝ → ℝ} (hh : IsStepFunction h) :
    (Set.range h).Finite := sorry

end IsStepFunction

/-- Exercise 4.2.6: every real-valued `L^p` function on `ℝ` with respect to Lebesgue measure can
be approximated arbitrarily well in `eLpNorm` by a real-valued step function. -/
-- Proof sketch: first approximate `f` in `eLpNorm` by a simple function using
-- `MemLp.exists_simpleFunc_eLpNorm_sub_lt`; then approximate the measurable fibers of that simple
-- function by a finite interval partition of `ℝ`, and finally transfer the approximation argument
-- from Exercise 4.2.5.
theorem exists_stepFunction_eLpNorm_sub_lt_of_memLp
    {p : ℝ} (hp : 1 ≤ p) {f : ℝ → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) volume) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℝ → ℝ,
      IsStepFunction h ∧
        eLpNorm (f - h) (ENNReal.ofReal p) volume < ENNReal.ofReal ε := sorry
