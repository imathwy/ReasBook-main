/-
  Copyright (c) 2026 Zichen Wang. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Zichen Wang, Wanli Ma, Min Cui, Zaiwen Wen
-/

import Mathlib

section Chap08
section Section03

/-- Definition 8.8: let `Ω ⊆ ℝ^n` be measurable. A measurable function `f` is absolutely
integrable on `Ω` iff the Lebesgue integral over `Ω` of `|f|` is finite. -/
def IsAbsolutelyIntegrableOn {n : ℕ} (Ω : Set (Fin n → ℝ))
    (f : Ω → EReal) : Prop :=
  MeasurableSet Ω ∧
    Measurable f ∧
      (∫⁻ x, (f x).abs ∂(MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume)) < ⊤

/-- Definition 8.9: for a real-valued function `f`, define its positive and negative parts
by `f⁺ x = max (f x) 0` and `f⁻ x = -min (f x) 0`. -/
def positiveNegativeParts {α : Type*} (f : α → ℝ) : (α → ℝ) × (α → ℝ) :=
  (fun x => max (f x) 0, fun x => -min (f x) 0)

/-- Helper for Proposition 8.9: the positive part `max (f x) 0` is nonnegative. -/
lemma helperForProposition_8_9_posPart_nonneg
    {α : Type*} (f : α → ℝ) (x : α) :
    0 ≤ max (f x) 0 := by
  exact le_max_right (f x) 0

/-- Helper for Proposition 8.9: the negative part `-min (f x) 0` is nonnegative. -/
lemma helperForProposition_8_9_negPart_nonneg
    {α : Type*} (f : α → ℝ) (x : α) :
    0 ≤ -min (f x) 0 := by
  have hmin : min (f x) 0 ≤ 0 := min_le_right (f x) 0
  exact neg_nonneg.mpr hmin

/-- Helper for Proposition 8.9: pointwise decomposition `f = f⁺ - f⁻` using `max/min`. -/
lemma helperForProposition_8_9_self_eq_posPart_sub_negPart_pointwise
    {α : Type*} (f : α → ℝ) (x : α) :
    f x = max (f x) 0 - (-min (f x) 0) := by
  have hmaxmin : max (f x) 0 + min (f x) 0 = f x := by
    calc
      max (f x) 0 + min (f x) 0 = f x + 0 := by
        exact max_add_min (f x) 0
      _ = f x := by
        simp
  calc
    f x = max (f x) 0 + min (f x) 0 := by
      exact hmaxmin.symm
    _ = max (f x) 0 - (-min (f x) 0) := by
      simp [sub_eq_add_neg]

/-- Helper for Proposition 8.9: pointwise decomposition `|f| = f⁺ + f⁻` using `max/min`. -/
lemma helperForProposition_8_9_abs_eq_posPart_add_negPart_pointwise
    {α : Type*} (f : α → ℝ) (x : α) :
    |f x| = max (f x) 0 + -min (f x) 0 := by
  calc
    |f x| = max (f x) 0 - min (f x) 0 := by
      simpa using (max_sub_min_eq_abs (f x) 0).symm
    _ = max (f x) 0 + -min (f x) 0 := by
      simp [sub_eq_add_neg]

/-- Proposition 8.9: for a real-valued function `f`, defining
`f⁺ x := max (f x) 0` and `f⁻ x := -min (f x) 0`, one has
`f⁺ ≥ 0`, `f⁻ ≥ 0`, `f = f⁺ - f⁻`, and `|f| = f⁺ + f⁻` pointwise. -/
theorem proposition_8_9
    {α : Type*} (f : α → ℝ) :
    (∀ x : α, 0 ≤ max (f x) 0) ∧
      (∀ x : α, 0 ≤ -min (f x) 0) ∧
      (∀ x : α, f x = max (f x) 0 - (-min (f x) 0)) ∧
      (∀ x : α, |f x| = max (f x) 0 + -min (f x) 0) := by
  constructor
  · intro x
    simpa using helperForProposition_8_9_posPart_nonneg f x
  constructor
  · intro x
    simpa using helperForProposition_8_9_negPart_nonneg f x
  constructor
  · intro x
    simpa using helperForProposition_8_9_self_eq_posPart_sub_negPart_pointwise f x
  · intro x
    simpa using helperForProposition_8_9_abs_eq_posPart_add_negPart_pointwise f x

/-- The positive part of an extended-real-valued function, `f⁺ = max (f, 0)`. -/
noncomputable def erealPositivePart {Ω : Type*} (f : Ω → EReal) : Ω → EReal :=
  fun x => max (f x) 0

/-- The negative part of an extended-real-valued function, `f⁻ = max (-f, 0)`. -/
noncomputable def erealNegativePart {Ω : Type*} (f : Ω → EReal) : Ω → EReal :=
  fun x => max (-f x) 0

/-- Predicate asserting that an extended-real-valued function has finite absolute
Lebesgue integral. -/
def HasFiniteAbsIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (f : Ω → EReal) : Prop :=
  (∫⁻ x, EReal.abs (f x) ∂ μ) < ⊤

/-- Definition 8.10 (Lebesgue integral): for a measurable `f : Ω → EReal` with
`∫ |f| dμ < ∞`, define `f⁺ := max (f, 0)`, `f⁻ := max (-f, 0)`, and set
`∫ f dμ := ∫ f⁺ dμ - ∫ f⁻ dμ`. -/
noncomputable def lebesgueIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (f : Ω → EReal) (hf_measurable : Measurable f) (hf_abs : HasFiniteAbsIntegral μ f) : EReal :=
  (fun (_ : Measurable f) (_ : HasFiniteAbsIntegral μ f) =>
    ((∫⁻ x, (erealPositivePart f x).toENNReal ∂ μ) : EReal) -
      ((∫⁻ x, (erealNegativePart f x).toENNReal ∂ μ) : EReal)) hf_measurable hf_abs

/-- Proposition 8.10.1: if `f,g : Ω → ℝ` are absolutely integrable, then for every
`c : ℝ`, `cf` is absolutely integrable and `∫ cf dμ = c ∫ f dμ`. -/
theorem proposition_8_10_1
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (f g : Ω → ℝ) (hf : MeasureTheory.Integrable f μ) (_hg : MeasureTheory.Integrable g μ)
    (c : ℝ) :
    MeasureTheory.Integrable (fun x => c * f x) μ ∧
      (∫ x, c * f x ∂ μ) = c * ∫ x, f x ∂ μ := by
  constructor
  · simpa using hf.const_mul c
  · simpa using MeasureTheory.integral_const_mul c f

/-- Proposition 8.10.2: if `f,g : Ω → ℝ` are absolutely integrable
(equivalently, integrable), then `f + g` is absolutely integrable and
`∫ (f + g) dμ = ∫ f dμ + ∫ g dμ`. -/
theorem proposition_8_10_2
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (f g : Ω → ℝ) (hf : MeasureTheory.Integrable f μ) (hg : MeasureTheory.Integrable g μ) :
    MeasureTheory.Integrable (fun x => f x + g x) μ ∧
      (∫ x, (f x + g x) ∂ μ) = (∫ x, f x ∂ μ) + (∫ x, g x ∂ μ) := by
  constructor
  · simpa using hf.add hg
  · simpa using MeasureTheory.integral_add hf hg

/-- Proposition 8.10.3: let `(Ω, 𝒜, μ)` be a measure space and let
`f, g : Ω → ℝ` be absolutely integrable (`∫ |f| dμ < ∞` and `∫ |g| dμ < ∞`).
If `f x ≤ g x` for all `x ∈ Ω`, then `∫ f dμ ≤ ∫ g dμ`. -/
theorem proposition_8_10_3
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (f g : Ω → ℝ) (hf : MeasureTheory.Integrable f μ) (hg : MeasureTheory.Integrable g μ)
    (hfg : ∀ x : Ω, f x ≤ g x) :
    (∫ x, f x ∂ μ) ≤ (∫ x, g x ∂ μ) := by
  simpa using MeasureTheory.integral_mono hf hg hfg

/-- Proposition 8.10.4: let `(Ω, 𝒜, μ)` be a measure space and let
`f, g : Ω → ℝ` be absolutely integrable (`∫ |f| dμ < ∞` and `∫ |g| dμ < ∞`).
If `f(x) = g(x)` for `μ`-almost every `x ∈ Ω`, then `∫ f dμ = ∫ g dμ`. -/
theorem proposition_8_10_4
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (f g : Ω → ℝ) (hf : MeasureTheory.Integrable f μ) (hg : MeasureTheory.Integrable g μ)
    (hfg : f =ᵐ[μ] g) :
    (∫ x, f x ∂ μ) = (∫ x, g x ∂ μ) := by
  let _ := hf
  let _ := hg
  simpa using MeasureTheory.integral_congr_ae hfg

/-- Helper for Theorem 8.5: measurability of a pointwise limit in `EReal`. -/
lemma helperForTheorem_8_5_measurableLimitFromPointwiseTendsto
    {Ω : Type*} [MeasurableSpace Ω]
    (fSeq : ℕ → Ω → EReal) (f : Ω → EReal)
    (h_measurable : ∀ n : ℕ, Measurable (fSeq n))
    (h_tendsto : ∀ x : Ω, Filter.Tendsto (fun n : ℕ => fSeq n x) Filter.atTop (nhds (f x))) :
    Measurable f := by
  refine measurable_of_tendsto_metrizable h_measurable ?_
  rw [tendsto_pi_nhds]
  intro x
  exact h_tendsto x

/-- Helper for Theorem 8.5: the positive-part ENNReal map is bounded by absolute value. -/
lemma helperForTheorem_8_5_posPartToENNReal_le_abs
    (z : EReal) :
    (max z 0).toENNReal ≤ EReal.abs z := by
  cases z with
  | bot => simp
  | top => simp
  | coe a =>
      by_cases ha : a ≤ 0
      · have haE : (a : EReal) ≤ 0 := by
          exact_mod_cast ha
        have hmax : max (a : EReal) 0 = 0 := max_eq_right haE
        simp [EReal.abs_def, hmax]
      · have hnonneg : 0 ≤ a := le_of_not_ge ha
        simp [EReal.abs_def, hnonneg, abs_of_nonneg hnonneg]

/-- Helper for Theorem 8.5: the negative-part ENNReal map is bounded by absolute value. -/
lemma helperForTheorem_8_5_negPartToENNReal_le_abs
    (z : EReal) :
    (max (-z) 0).toENNReal ≤ EReal.abs z := by
  simpa [EReal.abs_neg] using helperForTheorem_8_5_posPartToENNReal_le_abs (-z)

/-- Helper for Theorem 8.5: decomposition of absolute value into positive and negative ENNReal
parts. -/
lemma helperForTheorem_8_5_abs_eq_posPartAddNegPart
    (z : EReal) :
    EReal.abs z = (max z 0).toENNReal + (max (-z) 0).toENNReal := by
  cases z with
  | bot => simp
  | top => simp
  | coe a =>
      by_cases ha : 0 ≤ a
      · simp [EReal.abs_def, ha, abs_of_nonneg ha]
      · have hle : a ≤ 0 := le_of_not_ge ha
        simp [EReal.abs_def, hle, abs_of_nonpos hle]

/-- Helper for Theorem 8.5: absolute value is bounded by positive and negative ENNReal parts. -/
lemma helperForTheorem_8_5_abs_le_posPartAddNegPart
    (z : EReal) :
    EReal.abs z ≤ (max z 0).toENNReal + (max (-z) 0).toENNReal := by
  exact le_of_eq (helperForTheorem_8_5_abs_eq_posPartAddNegPart z)

/-- Helper for Theorem 8.5: domination by an integrable bound yields finite absolute integral. -/
lemma helperForTheorem_8_5_hasFiniteAbsIntegral_of_domination
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (g : Ω → EReal) (F : Ω → ENNReal)
    (hF_integrable : (∫⁻ x, F x ∂μ) < ⊤)
    (h_dom : ∀ x : Ω, EReal.abs (g x) ≤ (F x : EReal)) :
    HasFiniteAbsIntegral μ g := by
  have h_dom' : ∀ x : Ω, EReal.abs (g x) ≤ F x := by
    intro x
    exact_mod_cast h_dom x
  exact lt_of_le_of_lt (MeasureTheory.lintegral_mono h_dom') hF_integrable

/-- Theorem 8.5 (Lebesgue dominated convergence theorem): let `Ω ⊆ ℝ^n` be measurable,
let `fₙ : Ω → EReal` be measurable with pointwise limit `f`, and suppose there is a
measurable `F : Ω → [0, ∞]` with finite integral such that `|fₙ x| ≤ F x` for all `x`
and all `n`. Then `f` is measurable, `∫ |f| < ∞`, and `∫ f` is the limit of `∫ fₙ`. -/
theorem lebesgue_dominated_convergence_on_subtype
    {n : ℕ} (Ω : Set (Fin n → ℝ)) (hΩ : MeasurableSet Ω)
    (fSeq : ℕ → Ω → EReal) (f : Ω → EReal)
    (h_measurable : ∀ n : ℕ, Measurable (fSeq n))
    (h_tendsto : ∀ x : Ω, Filter.Tendsto (fun n : ℕ => fSeq n x) Filter.atTop (nhds (f x)))
    (F : Ω → ENNReal) (hF_measurable : Measurable F)
    (hF_integrable :
      (∫⁻ x, F x ∂ (MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume)) < ⊤)
    (h_dom : ∀ n : ℕ, ∀ x : Ω, EReal.abs (fSeq n x) ≤ (F x : EReal)) :
    ∃ (hf_measurable : Measurable f)
      (hf_abs :
        HasFiniteAbsIntegral (MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume) f)
      (hfSeq_abs : ∀ n : ℕ,
        HasFiniteAbsIntegral (MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume) (fSeq n)),
      Filter.Tendsto
        (fun n : ℕ =>
          lebesgueIntegral (MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume)
            (fSeq n) (h_measurable n) (hfSeq_abs n))
        Filter.atTop
        (nhds (lebesgueIntegral (MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume)
          f hf_measurable hf_abs)) := by
  let _ := hΩ
  let _ := hF_measurable
  let μ : MeasureTheory.Measure Ω := MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume
  let posPart : (Ω → EReal) → Ω → ENNReal := fun g x => (max (g x) 0).toENNReal
  let negPart : (Ω → EReal) → Ω → ENNReal := fun g x => (max (-g x) 0).toENNReal
  have hf_measurable : Measurable f :=
    helperForTheorem_8_5_measurableLimitFromPointwiseTendsto fSeq f h_measurable h_tendsto
  have hfSeq_abs : ∀ n : ℕ, HasFiniteAbsIntegral μ (fSeq n) := by
    intro n
    refine helperForTheorem_8_5_hasFiniteAbsIntegral_of_domination μ (fSeq n) F hF_integrable ?_
    intro x
    exact h_dom n x
  have h_pos_measurable : ∀ n : ℕ, Measurable (posPart (fSeq n)) := by
    intro n
    change Measurable (fun x => (max (fSeq n x) 0).toENNReal)
    exact ((h_measurable n).max measurable_const).ereal_toENNReal
  have h_neg_measurable : ∀ n : ℕ, Measurable (negPart (fSeq n)) := by
    intro n
    change Measurable (fun x => (max (-fSeq n x) 0).toENNReal)
    exact (((h_measurable n).neg).max measurable_const).ereal_toENNReal
  have h_pos_bound_pointwise : ∀ n : ℕ, ∀ x : Ω, posPart (fSeq n) x ≤ F x := by
    intro n x
    change (max (fSeq n x) 0).toENNReal ≤ F x
    have hdomCast : EReal.abs (fSeq n x) ≤ F x := by
      exact_mod_cast h_dom n x
    exact (helperForTheorem_8_5_posPartToENNReal_le_abs (fSeq n x)).trans hdomCast
  have h_neg_bound_pointwise : ∀ n : ℕ, ∀ x : Ω, negPart (fSeq n) x ≤ F x := by
    intro n x
    change (max (-fSeq n x) 0).toENNReal ≤ F x
    have hdomCast : EReal.abs (fSeq n x) ≤ F x := by
      exact_mod_cast h_dom n x
    exact (helperForTheorem_8_5_negPartToENNReal_le_abs (fSeq n x)).trans hdomCast
  have h_pos_bound : ∀ n : ℕ, posPart (fSeq n) ≤ᵐ[μ] F := by
    intro n
    exact Filter.Eventually.of_forall (h_pos_bound_pointwise n)
  have h_neg_bound : ∀ n : ℕ, negPart (fSeq n) ≤ᵐ[μ] F := by
    intro n
    exact Filter.Eventually.of_forall (h_neg_bound_pointwise n)
  have h_pos_cont : Continuous (fun z : EReal => (max z 0).toENNReal) :=
    (continuous_id.max continuous_const).ereal_toENNReal
  have h_neg_cont : Continuous (fun z : EReal => (max (-z) 0).toENNReal) := by
    simpa using (continuous_neg.max continuous_const).ereal_toENNReal
  have h_pos_tendsto_pointwise :
      ∀ x : Ω, Filter.Tendsto (fun n : ℕ => posPart (fSeq n) x) Filter.atTop
        (nhds (posPart f x)) := by
    intro x
    change Filter.Tendsto (fun n : ℕ => (max (fSeq n x) 0).toENNReal) Filter.atTop
      (nhds ((max (f x) 0).toENNReal))
    exact (h_pos_cont.tendsto (f x)).comp (h_tendsto x)
  have h_neg_tendsto_pointwise :
      ∀ x : Ω, Filter.Tendsto (fun n : ℕ => negPart (fSeq n) x) Filter.atTop
        (nhds (negPart f x)) := by
    intro x
    change Filter.Tendsto (fun n : ℕ => (max (-fSeq n x) 0).toENNReal) Filter.atTop
      (nhds ((max (-f x) 0).toENNReal))
    exact (h_neg_cont.tendsto (f x)).comp (h_tendsto x)
  have h_pos_tendsto_lintegral :
      Filter.Tendsto (fun n : ℕ => ∫⁻ x, posPart (fSeq n) x ∂μ) Filter.atTop
        (nhds (∫⁻ x, posPart f x ∂μ)) := by
    refine MeasureTheory.tendsto_lintegral_of_dominated_convergence F h_pos_measurable h_pos_bound
      (ne_of_lt hF_integrable) ?_
    exact Filter.Eventually.of_forall h_pos_tendsto_pointwise
  have h_neg_tendsto_lintegral :
      Filter.Tendsto (fun n : ℕ => ∫⁻ x, negPart (fSeq n) x ∂μ) Filter.atTop
        (nhds (∫⁻ x, negPart f x ∂μ)) := by
    refine MeasureTheory.tendsto_lintegral_of_dominated_convergence F h_neg_measurable h_neg_bound
      (ne_of_lt hF_integrable) ?_
    exact Filter.Eventually.of_forall h_neg_tendsto_pointwise
  have h_pos_integral_bound_seq :
      ∀ n : ℕ, (∫⁻ x, posPart (fSeq n) x ∂μ) ≤ (∫⁻ x, F x ∂μ) := by
    intro n
    exact MeasureTheory.lintegral_mono (h_pos_bound_pointwise n)
  have h_neg_integral_bound_seq :
      ∀ n : ℕ, (∫⁻ x, negPart (fSeq n) x ∂μ) ≤ (∫⁻ x, F x ∂μ) := by
    intro n
    exact MeasureTheory.lintegral_mono (h_neg_bound_pointwise n)
  have h_pos_integral_bound : (∫⁻ x, posPart f x ∂μ) ≤ (∫⁻ x, F x ∂μ) := by
    exact le_of_tendsto h_pos_tendsto_lintegral (Filter.Eventually.of_forall h_pos_integral_bound_seq)
  have h_neg_integral_bound : (∫⁻ x, negPart f x ∂μ) ≤ (∫⁻ x, F x ∂μ) := by
    exact le_of_tendsto h_neg_tendsto_lintegral (Filter.Eventually.of_forall h_neg_integral_bound_seq)
  have h_pos_lt_top : (∫⁻ x, posPart f x ∂μ) < ⊤ :=
    lt_of_le_of_lt h_pos_integral_bound hF_integrable
  have h_neg_lt_top : (∫⁻ x, negPart f x ∂μ) < ⊤ :=
    lt_of_le_of_lt h_neg_integral_bound hF_integrable
  have h_neg_measurable_f : Measurable (negPart f) := by
    change Measurable (fun x => (max (-f x) 0).toENNReal)
    exact ((hf_measurable.neg).max measurable_const).ereal_toENNReal
  have h_abs_pointwise : ∀ x : Ω, EReal.abs (f x) ≤ posPart f x + negPart f x := by
    intro x
    change EReal.abs (f x) ≤ (max (f x) 0).toENNReal + (max (-f x) 0).toENNReal
    exact helperForTheorem_8_5_abs_le_posPartAddNegPart (f x)
  have h_abs_lintegral_le :
      (∫⁻ x, EReal.abs (f x) ∂μ) ≤ (∫⁻ x, posPart f x + negPart f x ∂μ) :=
    MeasureTheory.lintegral_mono h_abs_pointwise
  have h_pos_neg_lintegral :
      (∫⁻ x, posPart f x + negPart f x ∂μ) =
        (∫⁻ x, posPart f x ∂μ) + (∫⁻ x, negPart f x ∂μ) := by
    exact MeasureTheory.lintegral_add_right (posPart f) h_neg_measurable_f
  have h_sum_lt_top :
      (∫⁻ x, posPart f x ∂μ) + (∫⁻ x, negPart f x ∂μ) < ⊤ := by
    exact (ENNReal.add_lt_top).2 ⟨h_pos_lt_top, h_neg_lt_top⟩
  have hf_abs : HasFiniteAbsIntegral μ f := by
    refine lt_of_le_of_lt ?_ h_sum_lt_top
    calc
      (∫⁻ x, EReal.abs (f x) ∂μ) ≤ (∫⁻ x, posPart f x + negPart f x ∂μ) :=
        h_abs_lintegral_le
      _ = (∫⁻ x, posPart f x ∂μ) + (∫⁻ x, negPart f x ∂μ) :=
        h_pos_neg_lintegral
  have h_pos_tendsto_ereal :
      Filter.Tendsto (fun n : ℕ => ((∫⁻ x, posPart (fSeq n) x ∂μ) : EReal)) Filter.atTop
        (nhds (((∫⁻ x, posPart f x ∂μ) : ENNReal) : EReal)) := by
    exact (continuous_coe_ennreal_ereal.tendsto _).comp h_pos_tendsto_lintegral
  have h_neg_tendsto_ereal :
      Filter.Tendsto (fun n : ℕ => ((∫⁻ x, negPart (fSeq n) x ∂μ) : EReal)) Filter.atTop
        (nhds (((∫⁻ x, negPart f x ∂μ) : ENNReal) : EReal)) := by
    exact (continuous_coe_ennreal_ereal.tendsto _).comp h_neg_tendsto_lintegral
  refine ⟨hf_measurable, hf_abs, hfSeq_abs, ?_⟩
  have h_pos_ne_top_ereal : (((∫⁻ x, posPart f x ∂μ) : ENNReal) : EReal) ≠ ⊤ := by
    intro h
    exact h_pos_lt_top.ne (EReal.coe_ennreal_eq_top_iff.mp h)
  have h_pos_ne_bot_ereal : (((∫⁻ x, posPart f x ∂μ) : ENNReal) : EReal) ≠ ⊥ :=
    EReal.coe_ennreal_ne_bot _
  have h_integral_tendsto_ereal :
      Filter.Tendsto
        (fun n : ℕ =>
          (((∫⁻ x, posPart (fSeq n) x ∂μ) : ENNReal) : EReal) -
            (((∫⁻ x, negPart (fSeq n) x ∂μ) : ENNReal) : EReal))
        Filter.atTop
        (nhds
          ((((∫⁻ x, posPart f x ∂μ) : ENNReal) : EReal) -
            (((∫⁻ x, negPart f x ∂μ) : ENNReal) : EReal))) := by
    have hcontAdd :
        ContinuousAt (fun p : EReal × EReal => p.1 + p.2)
          ((((∫⁻ x, posPart f x ∂μ) : ENNReal) : EReal),
            -((((∫⁻ x, negPart f x ∂μ) : ENNReal) : EReal))) := by
      exact EReal.continuousAt_add (Or.inl h_pos_ne_top_ereal) (Or.inl h_pos_ne_bot_ereal)
    have h_add_tendsto :
        Filter.Tendsto
          (fun n : ℕ =>
            (((∫⁻ x, posPart (fSeq n) x ∂μ) : ENNReal) : EReal) +
              -((((∫⁻ x, negPart (fSeq n) x ∂μ) : ENNReal) : EReal)))
          Filter.atTop
          (nhds
            ((((∫⁻ x, posPart f x ∂μ) : ENNReal) : EReal) +
              -((((∫⁻ x, negPart f x ∂μ) : ENNReal) : EReal)))) := by
      exact hcontAdd.tendsto.comp (h_pos_tendsto_ereal.prodMk_nhds h_neg_tendsto_ereal.neg)
    simpa [sub_eq_add_neg] using h_add_tendsto
  simpa [lebesgueIntegral, erealPositivePart, erealNegativePart, μ, posPart, negPart] using
    h_integral_tendsto_ereal

/-- Definition 8.11 (Upper and lower Lebesgue integrals): let `Ω ⊆ ℝ^n` be measurable and
`f : Ω → ℝ`. The upper integral is the infimum of integrals of absolutely integrable
majorants of `f`, and the lower integral is the supremum of integrals of absolutely
integrable minorants of `f`. -/
noncomputable def upperLowerLebesgueIntegralsOn {n : ℕ}
    (Ω : Set (Fin n → ℝ)) (hΩ : MeasurableSet Ω) (f : Ω → ℝ) : EReal × EReal :=
  let _ : MeasurableSet Ω := hΩ
  let μ : MeasureTheory.Measure Ω := MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume
  (sInf {I : EReal | ∃ g : Ω → ℝ, MeasureTheory.Integrable g μ ∧
      (∀ x : Ω, f x ≤ g x) ∧ I = (∫ x, g x ∂ μ : ℝ)},
    sSup {I : EReal | ∃ g : Ω → ℝ, MeasureTheory.Integrable g μ ∧
      (∀ x : Ω, g x ≤ f x) ∧ I = (∫ x, g x ∂ μ : ℝ)})

/-- Helper for Lemma 8.9: upper-candidate membership for `-f` is equivalent to lower-candidate
membership for `f` after negating the candidate value. -/
lemma helperForLemma_8_9_negUpperCandidate_iff_lowerCandidate
    {n : ℕ} (Ω : Set (Fin n → ℝ)) (f : Ω → ℝ) (I : EReal) :
    (I ∈ {J : EReal | ∃ g : Ω → ℝ,
      MeasureTheory.Integrable g (MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume) ∧
      (∀ x : Ω, (-f x) ≤ g x) ∧
      J = (∫ x, g x ∂ (MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume) : ℝ)}) ↔
    (-I ∈ {J : EReal | ∃ g : Ω → ℝ,
      MeasureTheory.Integrable g (MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume) ∧
      (∀ x : Ω, g x ≤ f x) ∧
      J = (∫ x, g x ∂ (MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume) : ℝ)}) := by
  constructor
  · rintro ⟨g, hgInt, hMajor, hI⟩
    refine ⟨(fun x => -g x), hgInt.neg, ?_, ?_⟩
    · intro x
      simpa using (neg_le_neg (hMajor x))
    · calc
        -I = -((∫ x, g x ∂ (MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume) : ℝ) : EReal) := by
          simpa [hI]
        _ = ((∫ x, (-g x) ∂ (MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume) : ℝ) : EReal) := by
          simp [MeasureTheory.integral_neg]
  · rintro ⟨g, hgInt, hMinor, hNegI⟩
    refine ⟨(fun x => -g x), hgInt.neg, ?_, ?_⟩
    · intro x
      exact neg_le_neg (hMinor x)
    · calc
        I = -(-I) := by simp
        _ = -((∫ x, g x ∂ (MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume) : ℝ) : EReal) := by
          simpa [hNegI]
        _ = ((∫ x, (-g x) ∂ (MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume) : ℝ) : EReal) := by
          simp [MeasureTheory.integral_neg]

/-- Helper for Lemma 8.9: lower-candidate membership for `-f` is equivalent to upper-candidate
membership for `f` after negating the candidate value. -/
lemma helperForLemma_8_9_negLowerCandidate_iff_upperCandidate
    {n : ℕ} (Ω : Set (Fin n → ℝ)) (f : Ω → ℝ) (I : EReal) :
    (I ∈ {J : EReal | ∃ g : Ω → ℝ,
      MeasureTheory.Integrable g (MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume) ∧
      (∀ x : Ω, g x ≤ (-f x)) ∧
      J = (∫ x, g x ∂ (MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume) : ℝ)}) ↔
    (-I ∈ {J : EReal | ∃ g : Ω → ℝ,
      MeasureTheory.Integrable g (MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume) ∧
      (∀ x : Ω, f x ≤ g x) ∧
      J = (∫ x, g x ∂ (MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume) : ℝ)}) := by
  constructor
  · rintro ⟨g, hgInt, hMinor, hI⟩
    refine ⟨(fun x => -g x), hgInt.neg, ?_, ?_⟩
    · intro x
      simpa using (neg_le_neg (hMinor x))
    · calc
        -I = -((∫ x, g x ∂ (MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume) : ℝ) : EReal) := by
          simpa [hI]
        _ = ((∫ x, (-g x) ∂ (MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume) : ℝ) : EReal) := by
          simp [MeasureTheory.integral_neg]
  · rintro ⟨g, hgInt, hMajor, hNegI⟩
    refine ⟨(fun x => -g x), hgInt.neg, ?_, ?_⟩
    · intro x
      exact neg_le_neg (hMajor x)
    · calc
        I = -(-I) := by simp
        _ = -((∫ x, g x ∂ (MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume) : ℝ) : EReal) := by
          simpa [hNegI]
        _ = ((∫ x, (-g x) ∂ (MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume) : ℝ) : EReal) := by
          simp [MeasureTheory.integral_neg]

/-- Helper for Lemma 8.9: the upper/lower components for `-f` are the negations of the lower/upper
components for `f`. -/
lemma helperForLemma_8_9_upperLower_neg_components
    {n : ℕ} (Ω : Set (Fin n → ℝ)) (hΩ : MeasurableSet Ω) (f : Ω → ℝ) :
    (upperLowerLebesgueIntegralsOn Ω hΩ (fun x => -f x)).1 =
        -(upperLowerLebesgueIntegralsOn Ω hΩ f).2 ∧
      (upperLowerLebesgueIntegralsOn Ω hΩ (fun x => -f x)).2 =
        -(upperLowerLebesgueIntegralsOn Ω hΩ f).1 := by
  let μ : MeasureTheory.Measure Ω := MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume
  let upperSet : Set EReal := {I : EReal | ∃ g : Ω → ℝ, MeasureTheory.Integrable g μ ∧
    (∀ x : Ω, f x ≤ g x) ∧ I = (∫ x, g x ∂ μ : ℝ)}
  let lowerSet : Set EReal := {I : EReal | ∃ g : Ω → ℝ, MeasureTheory.Integrable g μ ∧
    (∀ x : Ω, g x ≤ f x) ∧ I = (∫ x, g x ∂ μ : ℝ)}
  let negUpperSet : Set EReal := {I : EReal | ∃ g : Ω → ℝ, MeasureTheory.Integrable g μ ∧
    (∀ x : Ω, (-f x) ≤ g x) ∧ I = (∫ x, g x ∂ μ : ℝ)}
  let negLowerSet : Set EReal := {I : EReal | ∃ g : Ω → ℝ, MeasureTheory.Integrable g μ ∧
    (∀ x : Ω, g x ≤ (-f x)) ∧ I = (∫ x, g x ∂ μ : ℝ)}
  have hNegUpperSet : negUpperSet = -lowerSet := by
    ext I
    constructor
    · intro hI
      have hTransport : I ∈ negUpperSet ↔ -I ∈ lowerSet := by
        simpa [negUpperSet, lowerSet, μ] using
          (helperForLemma_8_9_negUpperCandidate_iff_lowerCandidate Ω f I)
      exact (Set.mem_neg).2 ((hTransport.mp hI))
    · intro hI
      have hTransport : I ∈ negUpperSet ↔ -I ∈ lowerSet := by
        simpa [negUpperSet, lowerSet, μ] using
          (helperForLemma_8_9_negUpperCandidate_iff_lowerCandidate Ω f I)
      exact hTransport.mpr ((Set.mem_neg).1 hI)
  have hNegLowerSet : negLowerSet = -upperSet := by
    ext I
    constructor
    · intro hI
      have hTransport : I ∈ negLowerSet ↔ -I ∈ upperSet := by
        simpa [negLowerSet, upperSet, μ] using
          (helperForLemma_8_9_negLowerCandidate_iff_upperCandidate Ω f I)
      exact (Set.mem_neg).2 ((hTransport.mp hI))
    · intro hI
      have hTransport : I ∈ negLowerSet ↔ -I ∈ upperSet := by
        simpa [negLowerSet, upperSet, μ] using
          (helperForLemma_8_9_negLowerCandidate_iff_upperCandidate Ω f I)
      exact hTransport.mpr ((Set.mem_neg).1 hI)
  have hSInfNeg : ∀ s : Set EReal, sInf (-s) = -sSup s := by
    intro s
    apply le_antisymm
    · have hUpper : sSup s ≤ -sInf (-s) := by
        refine sSup_le ?_
        intro b hb
        have hsInf : sInf (-s) ≤ -b := sInf_le ((Set.neg_mem_neg).2 hb)
        exact (EReal.le_neg).2 hsInf
      exact (EReal.le_neg).2 hUpper
    · refine le_sInf ?_
      intro b hb
      have hSup : -b ≤ sSup s := le_sSup ((Set.mem_neg).1 hb)
      exact (EReal.neg_le).2 hSup
  have hSSupNeg : ∀ s : Set EReal, sSup (-s) = -sInf s := by
    intro s
    apply le_antisymm
    · refine sSup_le ?_
      intro b hb
      have hsInf : sInf s ≤ -b := sInf_le ((Set.mem_neg).1 hb)
      exact (EReal.le_neg).2 hsInf
    · have hLower : -sSup (-s) ≤ sInf s := by
        refine le_sInf ?_
        intro b hb
        have hSup : -b ≤ sSup (-s) := le_sSup ((Set.neg_mem_neg).2 hb)
        exact (EReal.neg_le).2 hSup
      exact (EReal.neg_le).2 hLower
  constructor
  · calc
      (upperLowerLebesgueIntegralsOn Ω hΩ (fun x => -f x)).1 = sInf negUpperSet := by
        simp [upperLowerLebesgueIntegralsOn, negUpperSet, μ]
      _ = sInf (-lowerSet) := by simpa [hNegUpperSet]
      _ = -sSup lowerSet := hSInfNeg lowerSet
      _ = -(upperLowerLebesgueIntegralsOn Ω hΩ f).2 := by
        simp [upperLowerLebesgueIntegralsOn, lowerSet, μ]
  · calc
      (upperLowerLebesgueIntegralsOn Ω hΩ (fun x => -f x)).2 = sSup negLowerSet := by
        simp [upperLowerLebesgueIntegralsOn, negLowerSet, μ]
      _ = sSup (-upperSet) := by simpa [hNegLowerSet]
      _ = -sInf upperSet := hSSupNeg upperSet
      _ = -(upperLowerLebesgueIntegralsOn Ω hΩ f).1 := by
        simp [upperLowerLebesgueIntegralsOn, upperSet, μ]

/-- Helper for Lemma 8.9: from equal upper/lower component values at `A`, conclude the same
equalities for `f` and the corresponding sign-flipped values for `-f`. -/
lemma helperForLemma_8_9_finalize_from_component_equalities
    {n : ℕ} (Ω : Set (Fin n → ℝ)) (hΩ : MeasurableSet Ω) (f : Ω → ℝ) (A : ℝ)
    (hUpper : (upperLowerLebesgueIntegralsOn Ω hΩ f).1 = (A : EReal))
    (hLower : (upperLowerLebesgueIntegralsOn Ω hΩ f).2 = (A : EReal)) :
    (upperLowerLebesgueIntegralsOn Ω hΩ f).1 = (A : EReal) ∧
      (upperLowerLebesgueIntegralsOn Ω hΩ f).2 = (A : EReal) ∧
      (upperLowerLebesgueIntegralsOn Ω hΩ (fun x => -f x)).1 = (-A : EReal) ∧
      (upperLowerLebesgueIntegralsOn Ω hΩ (fun x => -f x)).2 = (-A : EReal) := by
  have hNeg :=
    helperForLemma_8_9_upperLower_neg_components Ω hΩ f
  rcases hNeg with ⟨hNegUpper, hNegLower⟩
  refine ⟨hUpper, hLower, ?_, ?_⟩
  · calc
      (upperLowerLebesgueIntegralsOn Ω hΩ (fun x => -f x)).1 =
          -(upperLowerLebesgueIntegralsOn Ω hΩ f).2 := hNegUpper
      _ = (-A : EReal) := by simpa [hLower]
  · calc
      (upperLowerLebesgueIntegralsOn Ω hΩ (fun x => -f x)).2 =
          -(upperLowerLebesgueIntegralsOn Ω hΩ f).1 := hNegLower
      _ = (-A : EReal) := by simpa [hUpper]

/-- Lemma 8.9: let `Ω ⊆ ℝ^n` be measurable and `f : Ω → ℝ`. If the upper and lower
Lebesgue-integral components of `f` are both equal to a finite value `A : ℝ`, then `f` is
integrable (hence absolutely integrable) on the subtype measure, the integral of `f` is `A`,
the upper/lower components for `f` are `A`, and the upper/lower components for `-f` are `-A`.
In particular, the usual integral agrees with both upper and lower components. -/
theorem lemma_8_9
    {n : ℕ} (Ω : Set (Fin n → ℝ)) (hΩ : MeasurableSet Ω) (f : Ω → ℝ) (A : ℝ)
    (hUpper : (upperLowerLebesgueIntegralsOn Ω hΩ f).1 = (A : EReal))
    (hLower : (upperLowerLebesgueIntegralsOn Ω hΩ f).2 = (A : EReal)) :
    (upperLowerLebesgueIntegralsOn Ω hΩ f).1 = (upperLowerLebesgueIntegralsOn Ω hΩ f).2 ∧
      MeasureTheory.Integrable f
        (MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume) ∧
      MeasureTheory.Integrable (fun x => |f x|)
        (MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume) ∧
      (∫ x, f x ∂ (MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume)) = A ∧
      (let Ωneg : Set (Fin n → ℝ) := (fun x => -x) ⁻¹' Ω
       let fneg : Ωneg → ℝ := fun x => f ⟨-x.1, x.2⟩
       (∫ x, fneg x ∂ (MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume)) = A) ∧
      (upperLowerLebesgueIntegralsOn Ω hΩ f).1 = (A : EReal) ∧
      (upperLowerLebesgueIntegralsOn Ω hΩ f).2 = (A : EReal) ∧
      (upperLowerLebesgueIntegralsOn Ω hΩ (fun x => -f x)).1 = (-A : EReal) ∧
      (upperLowerLebesgueIntegralsOn Ω hΩ (fun x => -f x)).2 = (-A : EReal) := by
  classical
  let μ : MeasureTheory.Measure Ω := MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume
  let upperSet : Set EReal := {I : EReal | ∃ g : Ω → ℝ, MeasureTheory.Integrable g μ ∧
    (∀ x : Ω, f x ≤ g x) ∧ I = (∫ x, g x ∂ μ : ℝ)}
  let lowerSet : Set EReal := {I : EReal | ∃ g : Ω → ℝ, MeasureTheory.Integrable g μ ∧
    (∀ x : Ω, g x ≤ f x) ∧ I = (∫ x, g x ∂ μ : ℝ)}
  have hUpperSet : sInf upperSet = (A : EReal) := by
    simpa [upperLowerLebesgueIntegralsOn, μ, upperSet, lowerSet] using hUpper
  have hLowerSet : sSup lowerSet = (A : EReal) := by
    simpa [upperLowerLebesgueIntegralsOn, μ, upperSet, lowerSet] using hLower
  have hUpperApprox :
      ∀ ε : ℝ, 0 < ε → ∃ h : Ω → ℝ, MeasureTheory.Integrable h μ ∧
        (∀ x : Ω, f x ≤ h x) ∧
          (((∫ x, h x ∂ μ : ℝ) : EReal) < ((A + ε : ℝ) : EReal)) := by
    intro ε hε
    by_contra hnot
    have hNoElt : ¬ ∃ b ∈ upperSet, b < ((A + ε : ℝ) : EReal) := by
      intro hExists
      rcases hExists with ⟨b, hb, hbLt⟩
      rcases hb with ⟨h, hhInt, hhLe, hEq⟩
      exact hnot ⟨h, hhInt, hhLe, by simpa [hEq] using hbLt⟩
    have hall : ∀ b ∈ upperSet, ((A + ε : ℝ) : EReal) ≤ b := by
      intro b hb
      by_contra hle
      exact hNoElt ⟨b, hb, lt_of_not_ge hle⟩
    have hle : ((A + ε : ℝ) : EReal) ≤ sInf upperSet := le_sInf hall
    have hleA : ((A + ε : ℝ) : EReal) ≤ (A : EReal) := by
      simpa [hUpperSet] using hle
    have hreal : A + ε ≤ A := by
      exact_mod_cast hleA
    linarith
  have hLowerApprox :
      ∀ ε : ℝ, 0 < ε → ∃ g : Ω → ℝ, MeasureTheory.Integrable g μ ∧
        (∀ x : Ω, g x ≤ f x) ∧
          (((A - ε : ℝ) : EReal) < ((∫ x, g x ∂ μ : ℝ) : EReal)) := by
    intro ε hε
    by_contra hnot
    have hNoElt : ¬ ∃ b ∈ lowerSet, ((A - ε : ℝ) : EReal) < b := by
      intro hExists
      rcases hExists with ⟨b, hb, hbLt⟩
      rcases hb with ⟨g, hgInt, hgLe, hEq⟩
      exact hnot ⟨g, hgInt, hgLe, by simpa [hEq] using hbLt⟩
    have hall : ∀ b ∈ lowerSet, b ≤ ((A - ε : ℝ) : EReal) := by
      intro b hb
      by_contra hle
      exact hNoElt ⟨b, hb, lt_of_not_ge hle⟩
    have hle : sSup lowerSet ≤ ((A - ε : ℝ) : EReal) := sSup_le hall
    have hleA : (A : EReal) ≤ ((A - ε : ℝ) : EReal) := by
      simpa [hLowerSet] using hle
    have hreal : A ≤ A - ε := by
      exact_mod_cast hleA
    linarith
  let ratRange : Set EReal := Set.range (fun q : ℚ => ((q : ℝ) : EReal))
  have hRatCountable : ratRange.Countable := by
    dsimp [ratRange]
    simpa [Set.image_univ] using
      ((Set.to_countable (Set.univ : Set ℚ)).image (fun q : ℚ => ((q : ℝ) : EReal)))
  have hRatDense : Dense ratRange := by
    dsimp [ratRange]
    simpa [DenseRange] using (EReal.denseRange_ratCast : DenseRange (fun q : ℚ => ((q : ℝ) : EReal)))
  have hfAEMeasurable : AEMeasurable f μ := by
    have hfE : AEMeasurable (fun x : Ω => (f x : EReal)) μ := by
      refine
        MeasureTheory.aemeasurable_of_exist_almost_disjoint_supersets μ ratRange hRatCountable
          hRatDense (fun x : Ω => (f x : EReal)) ?_
      intro p hp q hq hpq
      rcases hp with ⟨pRat, rfl⟩
      rcases hq with ⟨qRat, rfl⟩
      have hpqReal : (pRat : ℝ) < qRat := by
        simpa using (EReal.coe_lt_coe_iff.mp hpq)
      have hpqPos : 0 < (qRat : ℝ) - pRat := sub_pos.mpr hpqReal
      have hPairs :
          ∀ n : ℕ, ∃ g h : Ω → ℝ, MeasureTheory.Integrable g μ ∧ MeasureTheory.Integrable h μ ∧
            (∀ x : Ω, g x ≤ f x) ∧ (∀ x : Ω, f x ≤ h x) ∧
              ((∫ x, h x ∂ μ) - ∫ x, g x ∂ μ < ((qRat : ℝ) - pRat) / (n + 1 : ℝ)) := by
        intro n
        let ε : ℝ := ((qRat : ℝ) - pRat) / (2 * (n + 1 : ℝ))
        have hεPos : 0 < ε := by
          dsimp [ε]
          positivity
        rcases hLowerApprox ε hεPos with ⟨g, hgInt, hgLe, hgBound⟩
        rcases hUpperApprox ε hεPos with ⟨h, hhInt, hhLe, hhBound⟩
        have hgReal : A - ε < ∫ x, g x ∂ μ := by
          exact_mod_cast hgBound
        have hhReal : ∫ x, h x ∂ μ < A + ε := by
          exact_mod_cast hhBound
        have hGap : (∫ x, h x ∂ μ) - ∫ x, g x ∂ μ < ((qRat : ℝ) - pRat) / (n + 1 : ℝ) := by
          have hGapAux : (∫ x, h x ∂ μ) - ∫ x, g x ∂ μ < (A + ε) - (A - ε) := by
            exact sub_lt_sub hhReal hgReal
          have hTwoEps : (A + ε) - (A - ε) = ((qRat : ℝ) - pRat) / (n + 1 : ℝ) := by
            have hn : (n + 1 : ℝ) ≠ 0 := by positivity
            dsimp [ε]
            field_simp [hn]
            ring
          exact hTwoEps ▸ hGapAux
        exact ⟨g, h, hgInt, hhInt, hgLe, hhLe, hGap⟩
      choose g h hgInt hhInt hgLe hhLe hGap using hPairs
      let rawU : ℕ → Set Ω := fun n => {x : Ω | g n x < pRat}
      let rawV : ℕ → Set Ω := fun n => {x : Ω | (qRat : ℝ) < h n x}
      have hRawUNull : ∀ n : ℕ, MeasureTheory.NullMeasurableSet (rawU n) μ := by
        intro n
        dsimp [rawU]
        exact (hgInt n).aemeasurable.nullMeasurable measurableSet_Iio
      have hRawVNull : ∀ n : ℕ, MeasureTheory.NullMeasurableSet (rawV n) μ := by
        intro n
        dsimp [rawV]
        exact (hhInt n).aemeasurable.nullMeasurable measurableSet_Ioi
      choose u huSub huMeas huAE using
        fun n => (hRawUNull n).exists_measurable_superset_ae_eq
      choose v hvSub hvMeas hvAE using
        fun n => (hRawVNull n).exists_measurable_superset_ae_eq
      let U : Set Ω := ⋂ n : ℕ, u n
      let V : Set Ω := ⋂ n : ℕ, v n
      have hUMeas : MeasurableSet U := by
        dsimp [U]
        exact MeasurableSet.iInter huMeas
      have hVMeas : MeasurableSet V := by
        dsimp [V]
        exact MeasurableSet.iInter hvMeas
      have hSubsetU : {x : Ω | (f x : EReal) < (((pRat : ℝ) : EReal))} ⊆ U := by
        intro x hx
        have hxAll : ∀ k : ℕ, x ∈ u k := by
          intro k
          refine huSub k ?_
          dsimp [rawU]
          exact lt_of_le_of_lt (hgLe k x) (by exact_mod_cast hx)
        exact (Set.mem_iInter.2 hxAll)
      have hSubsetV : {x : Ω | (((qRat : ℝ) : EReal)) < (f x : EReal)} ⊆ V := by
        intro x hx
        have hxAll : ∀ k : ℕ, x ∈ v k := by
          intro k
          refine hvSub k ?_
          dsimp [rawV]
          exact lt_of_lt_of_le (by exact_mod_cast hx) (hhLe k x)
        exact (Set.mem_iInter.2 hxAll)
      have hRawInterBound : ∀ n : ℕ, μ (rawU n ∩ rawV n) ≤ ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
        intro n
        let Tn : Set Ω := {x : Ω |
          ENNReal.ofReal ((qRat : ℝ) - pRat) ≤ ENNReal.ofReal (h n x - g n x)}
        have hRawSub : rawU n ∩ rawV n ⊆ Tn := by
          intro x hx
          dsimp [rawU, rawV, Tn] at hx ⊢
          have hxLeft : g n x < (pRat : ℝ) := hx.1
          have hxRight : (qRat : ℝ) < h n x := hx.2
          have hdiff : (qRat : ℝ) - pRat < h n x - g n x := by
            linarith
          exact ENNReal.ofReal_le_ofReal (le_of_lt hdiff)
        have hNonneg : 0 ≤ᵐ[μ] fun x : Ω => h n x - g n x := by
          refine Filter.Eventually.of_forall ?_
          intro x
          exact sub_nonneg.mpr (le_trans (hgLe n x) (hhLe n x))
        have hDiffInt : MeasureTheory.Integrable (fun x : Ω => h n x - g n x) μ :=
          (hhInt n).sub (hgInt n)
        have hFMeas : AEMeasurable (fun x : Ω => ENNReal.ofReal (h n x - g n x)) μ :=
          hDiffInt.aemeasurable.ennreal_ofReal
        have hMarkov :
            μ Tn ≤
              (∫⁻ x : Ω, ENNReal.ofReal (h n x - g n x) ∂ μ) /
                ENNReal.ofReal ((qRat : ℝ) - pRat) := by
          refine MeasureTheory.meas_ge_le_lintegral_div hFMeas ?_ ?_
          · exact (ne_of_gt (ENNReal.ofReal_pos.mpr hpqPos))
          · simp
        have hLIntEq :
            ∫⁻ x : Ω, ENNReal.ofReal (h n x - g n x) ∂ μ =
              ENNReal.ofReal (∫ x : Ω, (h n x - g n x) ∂ μ) := by
          symm
          exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hDiffInt hNonneg
        have hLIntLe :
            ∫⁻ x : Ω, ENNReal.ofReal (h n x - g n x) ∂ μ ≤
              ENNReal.ofReal (((qRat : ℝ) - pRat) / (n + 1 : ℝ)) := by
          have hIntSub :
              (∫ x : Ω, (h n x - g n x) ∂ μ) = (∫ x, h n x ∂ μ) - ∫ x, g n x ∂ μ := by
            simpa using MeasureTheory.integral_sub (hhInt n) (hgInt n)
          rw [hLIntEq]
          rw [hIntSub]
          exact ENNReal.ofReal_le_ofReal (le_of_lt (hGap n))
        have hRatio :
            ENNReal.ofReal (((qRat : ℝ) - pRat) / (n + 1 : ℝ)) /
                ENNReal.ofReal ((qRat : ℝ) - pRat) =
              ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
          calc
            ENNReal.ofReal (((qRat : ℝ) - pRat) / (n + 1 : ℝ)) /
                ENNReal.ofReal ((qRat : ℝ) - pRat) =
                ENNReal.ofReal ((((qRat : ℝ) - pRat) / (n + 1 : ℝ)) / ((qRat : ℝ) - pRat)) := by
                  symm
                  exact ENNReal.ofReal_div_of_pos hpqPos
            _ = ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
                  congr 1
                  field_simp [hpqPos.ne']
        calc
          μ (rawU n ∩ rawV n) ≤ μ Tn := MeasureTheory.measure_mono hRawSub
          _ ≤
              (∫⁻ x : Ω, ENNReal.ofReal (h n x - g n x) ∂ μ) /
                ENNReal.ofReal ((qRat : ℝ) - pRat) := hMarkov
          _ ≤ ENNReal.ofReal (((qRat : ℝ) - pRat) / (n + 1 : ℝ)) /
                ENNReal.ofReal ((qRat : ℝ) - pRat) := by
                gcongr
          _ = ENNReal.ofReal (1 / (n + 1 : ℝ)) := hRatio
      have hUVBound : ∀ n : ℕ, μ (U ∩ V) ≤ ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
        intro n
        have hSub : U ∩ V ⊆ u n ∩ v n := by
          intro x hx
          have hxU : x ∈ U := hx.1
          have hxV : x ∈ V := hx.2
          have hxUn : x ∈ u n := by
            exact (Set.mem_iInter.1 (by simpa [U] using hxU)) n
          have hxVn : x ∈ v n := by
            exact (Set.mem_iInter.1 (by simpa [V] using hxV)) n
          exact ⟨hxUn, hxVn⟩
        calc
          μ (U ∩ V) ≤ μ (u n ∩ v n) := MeasureTheory.measure_mono hSub
          _ = μ (rawU n ∩ rawV n) := by
                exact MeasureTheory.measure_congr ((huAE n).inter (hvAE n))
          _ ≤ ENNReal.ofReal (1 / (n + 1 : ℝ)) := hRawInterBound n
      have hInvTendsto :
          Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (n + 1 : ℝ))) Filter.atTop (nhds 0) := by
        simpa using
          (ENNReal.continuous_ofReal.tendsto 0).comp
            (tendsto_one_div_add_atTop_nhds_zero_nat :
              Filter.Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) Filter.atTop (nhds 0))
      have hUVleZero : μ (U ∩ V) ≤ 0 := by
        have hConst :
            Filter.Tendsto (fun _ : ℕ => μ (U ∩ V)) Filter.atTop (nhds (μ (U ∩ V))) :=
          tendsto_const_nhds
        exact le_of_tendsto_of_tendsto hConst hInvTendsto (Filter.Eventually.of_forall hUVBound)
      have hUVZero : μ (U ∩ V) = 0 := le_antisymm hUVleZero bot_le
      exact ⟨U, V, hUMeas, hVMeas, hSubsetU, hSubsetV, hUVZero⟩
    have hfToReal : AEMeasurable (fun x : Ω => ((f x : EReal).toReal)) μ :=
      hfE.ereal_toReal
    simpa using hfToReal
  have hOnePos : (0 : ℝ) < 1 := by norm_num
  rcases hLowerApprox 1 hOnePos with ⟨g0, hg0Int, hg0Le, hg0Bound⟩
  rcases hUpperApprox 1 hOnePos with ⟨h0, hh0Int, hh0Le, hh0Bound⟩
  have hfInt : MeasureTheory.Integrable f μ :=
    MeasureTheory.integrable_of_le_of_le hfAEMeasurable.aestronglyMeasurable
      (Filter.Eventually.of_forall hg0Le) (Filter.Eventually.of_forall hh0Le) hg0Int hh0Int
  have hIntLeUpper : (((∫ x, f x ∂ μ) : ℝ) : EReal) ≤ sInf upperSet := by
    refine le_sInf ?_
    intro I hI
    rcases hI with ⟨h, hhInt, hhLe, hIeq⟩
    have hReal : (∫ x, f x ∂ μ) ≤ ∫ x, h x ∂ μ :=
      MeasureTheory.integral_mono hfInt hhInt hhLe
    have hEReal : (((∫ x, f x ∂ μ) : ℝ) : EReal) ≤ (((∫ x, h x ∂ μ) : ℝ) : EReal) := by
      exact_mod_cast hReal
    simpa [hIeq] using hEReal
  have hLowerLeInt : sSup lowerSet ≤ (((∫ x, f x ∂ μ) : ℝ) : EReal) := by
    refine sSup_le ?_
    intro I hI
    rcases hI with ⟨g, hgInt, hgLe', hIeq⟩
    have hReal : (∫ x, g x ∂ μ) ≤ ∫ x, f x ∂ μ :=
      MeasureTheory.integral_mono hgInt hfInt hgLe'
    have hEReal : (((∫ x, g x ∂ μ) : ℝ) : EReal) ≤ (((∫ x, f x ∂ μ) : ℝ) : EReal) := by
      exact_mod_cast hReal
    simpa [hIeq] using hEReal
  have hIntEReal : (((∫ x, f x ∂ μ) : ℝ) : EReal) = (A : EReal) := by
    refine le_antisymm ?_ ?_
    · exact (hIntLeUpper.trans_eq hUpperSet)
    · exact (hLowerSet.symm ▸ hLowerLeInt)
  have hIntA : (∫ x, f x ∂ μ) = A := by
    exact_mod_cast hIntEReal
  have hEqUL :
      (upperLowerLebesgueIntegralsOn Ω hΩ f).1 =
        (upperLowerLebesgueIntegralsOn Ω hΩ f).2 := by
    calc
      (upperLowerLebesgueIntegralsOn Ω hΩ f).1 = (A : EReal) := hUpper
      _ = (upperLowerLebesgueIntegralsOn Ω hΩ f).2 := hLower.symm
  have hAbsInt :
      MeasureTheory.Integrable (fun x => |f x|) μ := by
    simpa [Real.norm_eq_abs] using hfInt.norm
  have hFinal :=
    helperForLemma_8_9_finalize_from_component_equalities Ω hΩ f A hUpper hLower
  rcases hFinal with ⟨hUpperA, hLowerA, hNegUpperA, hNegLowerA⟩
  have hNegIntegralA :
      (let Ωneg : Set (Fin n → ℝ) := (fun x => -x) ⁻¹' Ω
       let fneg : Ωneg → ℝ := fun x => f ⟨-x.1, x.2⟩
       (∫ x, fneg x ∂ (MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume)) = A) := by
    let Ωneg : Set (Fin n → ℝ) := (fun x => -x) ⁻¹' Ω
    let F : (Fin n → ℝ) → ℝ := fun x => if hx : x ∈ Ω then f ⟨x, hx⟩ else 0
    have hΩneg : MeasurableSet Ωneg := by
      simpa [Ωneg] using hΩ.preimage measurable_neg
    have hMapNeg :
        (MeasureTheory.volume.restrict Ωneg).map Neg.neg =
          MeasureTheory.volume.restrict Ω := by
      calc
        (MeasureTheory.volume.restrict Ωneg).map Neg.neg =
            ((MeasureTheory.Measure.map Neg.neg
              (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))).restrict Ω) := by
              simpa [Ωneg] using
                (measurableEmbedding_neg.restrict_map
                  (μ := (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)))
                  (s := Ω)).symm
        _ = MeasureTheory.volume.restrict Ω := by
              simpa [MeasureTheory.Measure.map_neg_eq_self
                (μ := (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ)))]
    have hLeftRepr :
        (∫ x : Ωneg, f ⟨-x.1, x.2⟩ ∂
            (MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume)) =
          ∫ x in Ωneg, F (-x) ∂ MeasureTheory.volume := by
      calc
        (∫ x : Ωneg, f ⟨-x.1, x.2⟩ ∂
            (MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume)) =
            ∫ x : Ωneg, F (-x.1) ∂
              (MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume) := by
              refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
              intro x
              cases x with
              | mk x hx =>
                  have hxΩ : -x ∈ Ω := by
                    simpa [Ωneg] using hx
                  change f ⟨-x, hxΩ⟩ = F (-x)
                  simp [F, hxΩ]
        _ = ∫ x in Ωneg, F (-x) ∂ MeasureTheory.volume := by
              simpa using
                (MeasureTheory.integral_subtype_comap
                  (μ := MeasureTheory.volume) hΩneg (fun x : Fin n → ℝ => F (-x)))
    have hRightRepr :
        (∫ x : Ω, f x ∂ (MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume)) =
          ∫ x in Ω, F x ∂ MeasureTheory.volume := by
      calc
        (∫ x : Ω, f x ∂ (MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume)) =
            ∫ x : Ω, F x.1 ∂ (MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume) := by
              refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
              intro x
              cases x with
              | mk x hx =>
                  change f ⟨x, hx⟩ = F x
                  simp [F, hx]
        _ = ∫ x in Ω, F x ∂ MeasureTheory.volume := by
              simpa using
                (MeasureTheory.integral_subtype_comap (μ := MeasureTheory.volume) hΩ F)
    have hSetIntegral :
        ∫ x in Ωneg, F (-x) ∂ MeasureTheory.volume = ∫ x in Ω, F x ∂ MeasureTheory.volume := by
      calc
        ∫ x in Ωneg, F (-x) ∂ MeasureTheory.volume =
            ∫ x, F (-x) ∂ (MeasureTheory.volume.restrict Ωneg) := rfl
        _ = ∫ y, F y ∂ (MeasureTheory.Measure.map Neg.neg (MeasureTheory.volume.restrict Ωneg)) := by
              exact (measurableEmbedding_neg.integral_map
                (μ := MeasureTheory.volume.restrict Ωneg) F).symm
        _ = ∫ y, F y ∂ (MeasureTheory.volume.restrict Ω) := by
              simpa [hMapNeg]
        _ = ∫ x in Ω, F x ∂ MeasureTheory.volume := rfl
    dsimp [Ωneg]
    calc
      (∫ x : (fun x => -x) ⁻¹' Ω, f ⟨-x.1, x.2⟩ ∂
          (MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume)) =
          ∫ x in Ωneg, F (-x) ∂ MeasureTheory.volume := hLeftRepr
      _ = ∫ x in Ω, F x ∂ MeasureTheory.volume := hSetIntegral
      _ = (∫ x : Ω, f x ∂ (MeasureTheory.Measure.comap Subtype.val MeasureTheory.volume)) := by
            exact hRightRepr.symm
      _ = A := hIntA
  refine ⟨hEqUL, hfInt, hAbsInt, ?_, hNegIntegralA, hUpperA, hLowerA, hNegUpperA, hNegLowerA⟩
  simpa [μ] using hIntA

/-- Proposition 8.11: if measurable real-valued functions `f` and `g` on `ℝ` are integrable,
satisfy `f x ≤ g x` for all `x`, and have equal integrals, then `f = g` almost everywhere
with respect to Lebesgue measure. -/
theorem ae_eq_of_integrable_le_and_integral_eq_on_real
    (f g : ℝ → ℝ) (hf_measurable : Measurable f) (hg_measurable : Measurable g)
    (hf_integrable : MeasureTheory.Integrable f) (hg_integrable : MeasureTheory.Integrable g)
    (hfg_le : ∀ x : ℝ, f x ≤ g x)
    (h_integral_eq : (∫ x, f x) = ∫ x, g x) :
    f =ᵐ[MeasureTheory.volume] g := by
  let _ := hf_measurable
  let _ := hg_measurable
  have hAeLe : f ≤ᵐ[MeasureTheory.volume] g := Filter.Eventually.of_forall hfg_le
  exact
    (MeasureTheory.integral_eq_iff_of_ae_le hf_integrable hg_integrable hAeLe).1 h_integral_eq

/-- Proposition 8.12: defining `fₙ = χ_[n,n+1) - χ_[n+1,n+2)` on `ℝ`, the partial sums
from `n = 1` converge pointwise to `g = χ_[1,2)`, and integration does not commute with
this series:
`∫ (∑_{n=1}^∞ fₙ) dm ≠ ∑_{n=1}^∞ ∫ fₙ dm`. -/
theorem proposition_8_12 :
    let f : ℕ → ℝ → ℝ := fun n x =>
      Set.indicator (Set.Ico (n : ℝ) ((n : ℝ) + 1)) (fun _ => (1 : ℝ)) x -
        Set.indicator (Set.Ico ((n : ℝ) + 1) ((n : ℝ) + 2)) (fun _ => (1 : ℝ)) x
    let g : ℝ → ℝ := fun x => Set.indicator (Set.Ico (1 : ℝ) 2) (fun _ => (1 : ℝ)) x
    (∀ x : ℝ,
      Filter.Tendsto
        (fun N : ℕ => Finset.sum (Finset.range N) (fun n => f (n + 1) x))
        Filter.atTop
        (nhds (g x))) ∧
      (∫ x, (tsum (fun n : ℕ => f (n + 1) x)) ∂ MeasureTheory.volume) ≠
        tsum (fun n : ℕ => (∫ x, f (n + 1) x ∂ MeasureTheory.volume)) := by
  classical
  let f : ℕ → ℝ → ℝ := fun n x =>
    Set.indicator (Set.Ico (n : ℝ) ((n : ℝ) + 1)) (fun _ => (1 : ℝ)) x -
      Set.indicator (Set.Ico ((n : ℝ) + 1) ((n : ℝ) + 2)) (fun _ => (1 : ℝ)) x
  let g : ℝ → ℝ := fun x => Set.indicator (Set.Ico (1 : ℝ) 2) (fun _ => (1 : ℝ)) x
  change (∀ x : ℝ,
      Filter.Tendsto
        (fun N : ℕ => Finset.sum (Finset.range N) (fun n => f (n + 1) x))
        Filter.atTop
        (nhds (g x))) ∧
      (∫ x, (tsum (fun n : ℕ => f (n + 1) x)) ∂ MeasureTheory.volume) ≠
        tsum (fun n : ℕ => (∫ x, f (n + 1) x ∂ MeasureTheory.volume))
  let tail : ℕ → ℝ → ℝ := fun N x =>
    Set.indicator (Set.Ico ((N : ℝ) + 1) ((N : ℝ) + 2)) (fun _ => (1 : ℝ)) x
  have h_f_succ : ∀ n x, f (n + 1) x = tail n x - tail (n + 1) x := by
    intro n x
    simp [f, tail, add_assoc, add_left_comm, add_comm]
    have htwo : (n : ℝ) + (1 + 1) = (n : ℝ) + 2 := by ring
    rw [htwo]
  have h_partialSum : ∀ x N,
      Finset.sum (Finset.range N) (fun n => f (n + 1) x) = g x - tail N x := by
    intro x N
    induction N with
    | zero =>
        simp [g, tail]
    | succ N hN =>
        rw [Finset.sum_range_succ, hN, h_f_succ]
        ring
  have h_tail_tendsto_zero : ∀ x : ℝ,
      Filter.Tendsto (fun N : ℕ => tail N x) Filter.atTop (nhds 0) := by
    intro x
    rcases exists_nat_gt x with ⟨N0, hN0⟩
    have h_eventually_eq_zero : (fun N : ℕ => tail N x) =ᶠ[Filter.atTop] fun _ => (0 : ℝ) := by
      refine Filter.eventually_atTop.2 ?_
      refine ⟨N0, ?_⟩
      intro N hN
      have hcast : (N0 : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast hN
      have hx_lt : x < (N : ℝ) + 1 := by linarith
      have hnotmem : x ∉ Set.Ico ((N : ℝ) + 1) ((N : ℝ) + 2) := by
        intro hxmem
        exact not_lt_of_ge hxmem.1 hx_lt
      simp [tail, hnotmem]
    exact Filter.Tendsto.congr' h_eventually_eq_zero.symm tendsto_const_nhds
  have h_pointwise_tendsto : ∀ x : ℝ,
      Filter.Tendsto
        (fun N : ℕ => Finset.sum (Finset.range N) (fun n => f (n + 1) x))
        Filter.atTop
        (nhds (g x)) := by
    intro x
    have hsum : (fun N : ℕ => Finset.sum (Finset.range N) (fun n => f (n + 1) x)) =
        (fun N : ℕ => g x - tail N x) := by
      funext N
      exact h_partialSum x N
    rw [hsum]
    have hgconst : Filter.Tendsto (fun _ : ℕ => g x) Filter.atTop (nhds (g x)) := tendsto_const_nhds
    have hsub : Filter.Tendsto (fun N : ℕ => g x - tail N x) Filter.atTop (nhds (g x - 0)) :=
      hgconst.sub (h_tail_tendsto_zero x)
    simpa using hsub
  have h_tsum_eq_g : ∀ x : ℝ, tsum (fun n : ℕ => f (n + 1) x) = g x := by
    intro x
    rcases exists_nat_gt x with ⟨M, hM⟩
    have h_tail_zero_of_ge : ∀ {N : ℕ}, M ≤ N → tail N x = 0 := by
      intro N hMN
      have hcast : (M : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast hMN
      have hx_lt : x < (N : ℝ) + 1 := by linarith
      have hnotmem : x ∉ Set.Ico ((N : ℝ) + 1) ((N : ℝ) + 2) := by
        intro hxmem
        exact not_lt_of_ge hxmem.1 hx_lt
      simp [tail, hnotmem]
    have h_zero_outside : ∀ n ∉ Finset.range M, f (n + 1) x = 0 := by
      intro n hn
      have hMn : M ≤ n := Nat.le_of_not_gt (by simpa [Finset.mem_range] using hn)
      calc
        f (n + 1) x = tail n x - tail (n + 1) x := h_f_succ n x
        _ = 0 := by
          have h1 : tail n x = 0 := h_tail_zero_of_ge hMn
          have h2 : tail (n + 1) x = 0 := h_tail_zero_of_ge (Nat.le_trans hMn (Nat.le_succ n))
          simp [h1, h2]
    calc
      tsum (fun n : ℕ => f (n + 1) x) =
          Finset.sum (Finset.range M) (fun n => f (n + 1) x) := by
            exact tsum_eq_sum h_zero_outside
      _ = g x - tail M x := h_partialSum x M
      _ = g x := by
            have hM0 : tail M x = 0 := h_tail_zero_of_ge le_rfl
            simp [hM0]
  have h_integrable_tail : ∀ n : ℕ,
      MeasureTheory.Integrable (fun x : ℝ => tail n x) MeasureTheory.volume := by
    intro n
    refine (MeasureTheory.integrable_indicator_iff (μ := MeasureTheory.volume)
      (f := fun _ : ℝ => (1 : ℝ))
      (s := Set.Ico ((n : ℝ) + 1) ((n : ℝ) + 2)) measurableSet_Ico).2 ?_
    have hfinite : MeasureTheory.volume (Set.Ico ((n : ℝ) + 1) ((n : ℝ) + 2)) ≠ ⊤ := by
      rw [Real.volume_Ico]
      simp
    exact MeasureTheory.integrableOn_const hfinite
  have h_integral_tail : ∀ n : ℕ,
      (∫ x, tail n x ∂ MeasureTheory.volume) = 1 := by
    intro n
    rw [MeasureTheory.integral_indicator_const (μ := MeasureTheory.volume) (X := ℝ)
      (s := Set.Ico ((n : ℝ) + 1) ((n : ℝ) + 2)) (e := (1 : ℝ)) measurableSet_Ico]
    simp [MeasureTheory.Measure.real, Real.volume_Ico]
    norm_num
  have h_integral_term_zero : ∀ n : ℕ,
      (∫ x, f (n + 1) x ∂ MeasureTheory.volume) = 0 := by
    intro n
    have h_fun : (fun x : ℝ => f (n + 1) x) = fun x : ℝ => tail n x - tail (n + 1) x := by
      funext x
      exact h_f_succ n x
    rw [h_fun]
    rw [MeasureTheory.integral_sub (h_integrable_tail n) (h_integrable_tail (n + 1))]
    rw [h_integral_tail n, h_integral_tail (n + 1)]
    norm_num
  have h_integral_g : (∫ x, g x ∂ MeasureTheory.volume) = 1 := by
    rw [MeasureTheory.integral_indicator_const (μ := MeasureTheory.volume) (X := ℝ)
      (s := Set.Ico (1 : ℝ) 2) (e := (1 : ℝ)) measurableSet_Ico]
    simp [MeasureTheory.Measure.real, Real.volume_Ico]
    norm_num
  have h_left_eq_one :
      (∫ x, (tsum (fun n : ℕ => f (n + 1) x)) ∂ MeasureTheory.volume) = 1 := by
    calc
      (∫ x, (tsum (fun n : ℕ => f (n + 1) x)) ∂ MeasureTheory.volume) =
          (∫ x, g x ∂ MeasureTheory.volume) := by
            refine MeasureTheory.integral_congr_ae ?_
            exact Filter.Eventually.of_forall h_tsum_eq_g
      _ = 1 := h_integral_g
  have h_right_eq_zero :
      tsum (fun n : ℕ => (∫ x, f (n + 1) x ∂ MeasureTheory.volume)) = 0 := by
    have hfun : (fun n : ℕ => (∫ x, f (n + 1) x ∂ MeasureTheory.volume)) =
        (fun _ : ℕ => (0 : ℝ)) := by
      funext n
      exact h_integral_term_zero n
    rw [hfun]
    simp
  constructor
  · exact h_pointwise_tendsto
  · intro hEq
    have hcontr : (1 : ℝ) = 0 := by
      calc
        (1 : ℝ) = (∫ x, (tsum (fun n : ℕ => f (n + 1) x)) ∂ MeasureTheory.volume) :=
          h_left_eq_one.symm
        _ = tsum (fun n : ℕ => (∫ x, f (n + 1) x ∂ MeasureTheory.volume)) := hEq
        _ = 0 := h_right_eq_zero
    norm_num at hcontr

end Section03
end Chap08
