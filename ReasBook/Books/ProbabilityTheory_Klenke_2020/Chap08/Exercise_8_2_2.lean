import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConditionalLExpectation
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.PSeries
import ProbabilityTheory_Klenke_2020.Chap08.Remark_8_16

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped ENNReal MeasureTheory

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/- Part (1) is a `source-facing` interval statement for the canonical owner `condExp`. Part (2)
uses the chapter's signed bridge `lowerCondExp`; the underlying nonnegative `condLExp`
counterexample is kept only as private support. -/

section FiniteMeasure

variable {P : Measure[mΩ] Ω} [IsFiniteMeasure P]

-- Proof sketch: write an interval in `ℝ` as an order-convex set, then prove separately that
-- conditional expectation preserves almost-sure lower and upper bounds by combining
-- `condExp_mono` with `condExp_const`. Intersect the two half-line bounds to recover membership
-- in the whole interval.
/-- Exercise 8.2.2 (1): If an integrable real-valued random variable `X` takes values almost surely
in an interval `I ⊆ ℝ`, then its conditional expectation with respect to `ℱ` also takes values
almost surely in `I`. The canonical owner is `condExp`, and the finite-measure hypothesis is the
minimal ambient assumption needed by the upstream conditional-expectation API used here. -/
theorem condExp_mem_interval_ae {ℱ : MeasurableSpace Ω} (hℱ : ℱ ≤ mΩ) {I : Set ℝ}
    (hI : Set.OrdConnected I) {X : Ω → ℝ} (hX : Integrable X P)
    (hXI : ∀ᵐ ω ∂P, X ω ∈ I) :
    ∀ᵐ ω ∂P, P[X | ℱ] ω ∈ I := sorry

end FiniteMeasure

private theorem counterexample_data :
    ∃ (P : Measure (ULift.{u} ℕ)) (_ : IsProbabilityMeasure P)
      (Xenn : ULift.{u} ℕ → ℝ≥0∞) (X : ULift.{u} ℕ → ℝ),
      (∀ᵐ n ∂P, Xenn n ∈ Set.Iio (∞ : ℝ≥0∞)) ∧
      (P⁻[Xenn|⊥] = fun _ ↦ ∞) ∧
      (lowerCondExp P ⊥ X = fun _ ↦ (⊤ : EReal)) ∧
      Integrable (fun n ↦ (X n)⁻) P := by
  let Ω' := ULift.{u} ℕ
  letI : MeasurableSpace Ω' := ⊤
  let harm : Ω' → ℝ≥0∞ := fun n ↦ ENNReal.ofReal ((1 : ℝ) / (n.down : ℝ))
  let f : Ω' → ℝ≥0∞ := fun n ↦ harm n * harm n
  have htsum_f :
      (∑' n : Ω', f n) = ∑' n : ℕ, ENNReal.ofReal ((1 : ℝ) / (n : ℝ) ^ (2 : ℕ)) := by
    simpa [Ω', f, harm, pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (Equiv.tsum_eq Equiv.ulift
        (fun n : ℕ ↦ ENNReal.ofReal ((1 : ℝ) / (n : ℝ) ^ (2 : ℕ))))
  have hf0 : (∑' n, f n) ≠ 0 := by
    rw [htsum_f]
    let g : ℕ → ℝ≥0∞ := fun n ↦ ENNReal.ofReal ((1 : ℝ) / (n : ℝ) ^ (2 : ℕ))
    have h1 : 0 < g 1 := by
      simp [g]
    have hle : g 1 ≤ ∑' n : ℕ, g n := ENNReal.le_tsum 1
    intro hzero
    rw [hzero] at hle
    exact (not_lt_of_ge hle) h1
  have hf_top : (∑' n, f n) ≠ ∞ := by
    rw [htsum_f]
    simpa using hasSum_zeta_two.summable.tsum_ofReal_ne_top
  let p : PMF Ω' := PMF.normalize f hf0 hf_top
  let P : Measure Ω' := p.toMeasure
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    infer_instance
  let Xenn : Ω' → ℝ≥0∞ := fun n ↦ n.down
  let X : Ω' → ℝ := fun n ↦ n.down
  let c : ℝ≥0∞ := (∑' n, f n)⁻¹
  have hsingle (n : Ω') : P {n} = p n := by
    simpa [P] using (PMF.toMeasure_apply_singleton p n (MeasurableSet.singleton n))
  have hcancel (n : Ω') (hn : n.down ≠ 0) : Xenn n * harm n = 1 := by
    have hn' : (n.down : ℝ) ≠ 0 := by
      exact_mod_cast hn
    change ((n.down : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((1 : ℝ) / (n.down : ℝ)) = 1
    rw [show ((n.down : ℕ) : ℝ≥0∞) = ENNReal.ofReal (n.down : ℝ) by simp,
      ← ENNReal.ofReal_mul]
    · field_simp [hn']
      simp
    · positivity
  have hterm (n : Ω') : Xenn n * P {n} = harm n * c := by
    rw [hsingle, PMF.normalize_apply]
    rcases eq_or_ne n.down 0 with hzero | hn
    · have : n = ⟨0⟩ := by
        cases n
        simp_all
      subst this
      simp [Xenn, harm, f, c]
    · calc
        Xenn n * (f n * c) = (Xenn n * f n) * c := by ac_rfl
        _ = ((Xenn n * harm n) * harm n) * c := by simp [f, mul_assoc]
        _ = harm n * c := by simp [hcancel n hn]
  have hharm_top_nat : (∑' n : ℕ, ENNReal.ofReal ((1 : ℝ) / (n : ℝ))) = ∞ := by
    by_contra htop
    have hs : Summable (fun n : ℕ ↦ (ENNReal.ofReal ((1 : ℝ) / (n : ℝ))).toReal) :=
      ENNReal.summable_toReal htop
    have hs' : Summable (fun n : ℕ ↦ (1 : ℝ) / (n : ℝ)) := by
      simpa using hs
    exact Real.not_summable_one_div_natCast hs'
  have htsum_harm :
      (∑' n : Ω', harm n) = ∑' n : ℕ, ENNReal.ofReal ((1 : ℝ) / (n : ℝ)) := by
    simpa [Ω', harm] using
      (Equiv.tsum_eq Equiv.ulift (fun n : ℕ ↦ ENNReal.ofReal ((1 : ℝ) / (n : ℝ))))
  have hharm_top : (∑' n : Ω', harm n) = ∞ := by
    rw [htsum_harm]
    exact hharm_top_nat
  have hc0 : c ≠ 0 := by
    simp [c, hf_top]
  have hX_top : ∫⁻ n, Xenn n ∂P = ∞ := by
    calc
      ∫⁻ n, Xenn n ∂P = ∑' n, Xenn n * P {n} := by
        simpa [Xenn] using
          (lintegral_countable' Xenn : ∫⁻ n, Xenn n ∂P = ∑' n, Xenn n * P {n})
      _ = ∑' n, harm n * c := by
        exact tsum_congr hterm
      _ = (∑' n, harm n) * c := by
        rw [ENNReal.tsum_mul_right]
      _ = ∞ := by
        simp [hharm_top, hc0]
  have hcond_top : P⁻[Xenn|⊥] = fun _ ↦ ∞ := by
    simpa [hX_top] using (condLExp_bot P Xenn)
  have hXenn_finite : ∀ᵐ n ∂P, Xenn n ∈ Set.Iio (∞ : ℝ≥0∞) := by
    filter_upwards with n
    simp [Xenn]
  have hpos_eq : (fun n ↦ ENNReal.ofReal (X n)) = Xenn := by
    funext n
    simp [X, Xenn]
  have hneg_zero : (fun n ↦ ENNReal.ofReal (-X n)) = (0 : Ω' → ℝ≥0∞) := by
    funext n
    simp [X]
  have hlower_top : lowerCondExp P ⊥ X = fun _ ↦ (⊤ : EReal) := by
    ext n
    rw [lowerCondExp, hpos_eq, hcond_top, hneg_zero, condLExp_zero]
    simp
  have hXneg : Integrable (fun n ↦ (X n)⁻) P := by
    simp [X]
  exact ⟨P, ‹IsProbabilityMeasure P›, Xenn, X, hXenn_finite, hcond_top, hlower_top, hXneg⟩

private theorem not_condLExp_mem_interval_ae_aux :
    ¬ ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {ℱ : MeasurableSpace Ω} {I : Set ℝ≥0∞} {X : Ω → ℝ≥0∞},
        ℱ ≤ mΩ →
        Set.OrdConnected I →
        (∀ x ∈ I, x < ∞) →
        (∀ᵐ ω ∂P, X ω ∈ I) →
        ∀ᵐ ω ∂P, P⁻[X|ℱ] ω ∈ I := by
  intro h
  obtain ⟨P, hP, X, _, hX_finite, hcond_top, _, _⟩ := counterexample_data
  letI : IsProbabilityMeasure P := hP
  have hbad :
      ∀ᵐ n ∂P, P⁻[X|⊥] n ∈ Set.Iio (∞ : ℝ≥0∞) :=
    h P bot_le Set.ordConnected_Iio (fun _ hx ↦ hx) hX_finite
  rw [hcond_top] at hbad
  simp at hbad
  exact NeZero.ne P hbad

-- Proof sketch: reuse the same heavy-tailed nonnegative counterexample as in the private
-- `condLExp` helper, but view it as a real-valued random variable. Then `X⁻ = 0`, so the
-- source-facing `lowerCondExp` is defined, yet conditioning on the trivial σ-algebra still gives
-- the constant value `⊤`, which leaves the interval `Set.Ioo ⊥ ⊤` of genuine real values.
/-- Exercise 8.2.2 (2): The interval-preservation statement from part (1) fails if one weakens
integrability to the one-sided hypothesis `X⁻ ∈ L¹` and replaces `condExp` by the lower
conditional expectation from Remark 8.16. A nonnegative real-valued `X` can satisfy `X⁻ = 0`
almost surely while `lowerCondExp P ℱ X` still takes the value `⊤`. -/
theorem not_lowerCondExp_mem_interval_ae :
    ¬ ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {ℱ : MeasurableSpace Ω} {I : Set EReal} {X : Ω → ℝ},
        ℱ ≤ mΩ →
        Set.OrdConnected I →
        Integrable (fun ω ↦ (X ω)⁻) P →
        (∀ᵐ ω ∂P, (X ω : EReal) ∈ I) →
        ∀ᵐ ω ∂P, lowerCondExp P ℱ X ω ∈ I := by
  intro h
  obtain ⟨P, hP, _, X, _, _, hlower_top, hXneg⟩ := counterexample_data
  letI : IsProbabilityMeasure P := hP
  have hXI : ∀ᵐ n ∂P, (X n : EReal) ∈ Set.Ioo (⊥ : EReal) ⊤ := by
    filter_upwards with n
    simp
  have hbad :
      ∀ᵐ n ∂P, lowerCondExp P ⊥ X n ∈ Set.Ioo (⊥ : EReal) ⊤ :=
    h P bot_le Set.ordConnected_Ioo hXneg hXI
  rw [hlower_top] at hbad
  simp at hbad
  exact NeZero.ne P hbad
