import Mathlib
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConditionalLExpectation
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_8_2_1 (from Items/Chap08) -/
/- Exercise 8.2.1 (1): If `X⁻` is integrable, then the lower conditional expectation is the
almost-sure limit of the conditional expectations of any admissible increasing integrable
approximation, hence is independent of the chosen approximation sequence. -/
recall ae_tendsto_condExp_of_admissible_increasing_integrable_approximation

/- Exercise 8.2.1 (2): For integrable `X`, the lower-integrable extension from Remark 8.16 agrees
almost surely with the usual conditional expectation `P[X | ℱ]`. -/
recall lowerCondExp_ae_eq_condExp

/- Exercise 8.2.1 (3): The lower-integrable conditional expectation is monotone with respect to
almost-sure order. This is the monotonicity assertion from Remark 8.16. -/
recall lowerCondExp_mono

/-! ### Definition_8_2 (from Items/Chap08) -/
/- Definition 8.2: For a probability measure `P` and an event `B`, the textbook conditional
probability `P[A | B]` is the canonical event evaluation of the conditioned measure `P[|B]`;
the defining formula is the canonical theorem `ProbabilityTheory.cond_apply`, namely
`P[A | B] = (P B)⁻¹ * P (B ∩ A)`, which is `P[A ∩ B] / P[B]` with value `0` when `P B = 0`. -/
recall ProbabilityTheory.cond_apply

/-! ### Exercise_8_2_2 (from Items/Chap08) -/
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

/-! ### Exercise_8_2_3 (from Items/Chap08) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

-- Proof sketch: rewrite `(P[B | A]).toReal` using `ProbabilityTheory.cond_apply`, then identify
-- the numerator and denominator with the set integral over `B` and the total integral of the
-- conditional probability `P⟦A | ℱ⟧` by `setIntegral_condExp`, `integral_condExp`, and the
-- integral of the indicator of `A`.
/-- Exercise 8.2.3: Bayes' formula identifies the conditional probability of an `ℱ`-measurable
event `B` given `A` with the ratio of the integral of the conditional probability `P⟦A | ℱ⟧`
over `B` and its total integral. If `ℱ` is generated by pairwise disjoint sets `B₁, B₂, …`,
this recovers the discrete Bayes formula from Theorem 8.7. -/
theorem bayes_formula_conditional_probability
    {ℱ : MeasurableSpace Ω} (hℱ : ℱ ≤ mΩ) {A B : Set Ω} (hA : MeasurableSet[mΩ] A)
    (hB : MeasurableSet[ℱ] B) :
      (P[B | A]).toReal =
      (∫ ω in B, (P⟦A | ℱ⟧) ω ∂P) / (∫ ω, (P⟦A | ℱ⟧) ω ∂P) := by
  have hB_mΩ : MeasurableSet[mΩ] B := hℱ B hB
  have hAint : Integrable (A.indicator (fun _ ↦ (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).indicator hA
  have hnum : ∫ ω in B, (P⟦A | ℱ⟧) ω ∂P = P.real (A ∩ B) := by
    rw [setIntegral_condExp hℱ hAint hB, ← integral_indicator hB_mΩ]
    simpa [Set.indicator_indicator, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm,
      smul_eq_mul] using integral_indicator_const (1 : ℝ) (hA.inter hB_mΩ)
  have hden : ∫ ω, (P⟦A | ℱ⟧) ω ∂P = P.real A := by
    rw [integral_condExp hℱ, integral_indicator hA, setIntegral_const, smul_eq_mul, mul_one]
  rw [cond_apply hA P B, ENNReal.toReal_mul, ENNReal.toReal_inv, ← measureReal_def,
    ← measureReal_def, hnum, hden, div_eq_mul_inv, mul_comm]

/-! ### Exercise_8_2_4 (from Items/Chap08) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

local notation "Ω₃" => Fin 3

/-- The σ-algebra generated by the partition `{0} | {1, 2}` on the three-point space. -/
abbrev threePointSubalgebra₀ : MeasurableSpace Ω₃ :=
  MeasurableSpace.generateFrom {({0} : Set Ω₃)}

/-- The σ-algebra generated by the partition `{0, 1} | {2}` on the three-point space. -/
abbrev threePointSubalgebra₂ : MeasurableSpace Ω₃ :=
  MeasurableSpace.generateFrom {({2} : Set Ω₃)}

/-- The uniform probability measure on the three-point space. -/
def threePointUniformMeasure : Measure Ω₃ :=
  uniformOn (Set.univ : Set Ω₃)

/-- The random variable taking the value `1` at `0` and `0` elsewhere. -/
def threePointIndicatorAtZero : Ω₃ → ℝ :=
  Set.indicator ({0} : Set Ω₃) (fun _ ↦ (1 : ℝ))

/-- Condition first on `{0} | {1, 2}`, then on `{0, 1} | {2}`. -/
def threePointLeftThenRight : Ω₃ → ℝ :=
  threePointUniformMeasure[threePointUniformMeasure[threePointIndicatorAtZero | threePointSubalgebra₀] |
    threePointSubalgebra₂]

/-- Condition first on `{0, 1} | {2}`, then on `{0} | {1, 2}`. -/
def threePointRightThenLeft : Ω₃ → ℝ :=
  threePointUniformMeasure[threePointUniformMeasure[threePointIndicatorAtZero | threePointSubalgebra₂] |
    threePointSubalgebra₀]

private theorem threePointUniformMeasure_singleton_one_ne_zero :
    threePointUniformMeasure ({1} : Set Ω₃) ≠ 0 := by
  norm_num [threePointUniformMeasure, uniformOn_univ]

/-- The two iterated conditional expectations in the exercise's three-point model already
disagree at `1`. -/
-- Proof sketch: evaluate each conditional expectation with
-- `condExp_generateFrom_singleton`. Since `threePointIndicatorAtZero` is already
-- `threePointSubalgebra₀`-measurable, `threePointLeftThenRight 1` equals `1 / 2`; the other
-- order first averages over `{0, 1}` and then over `{1, 2}`, producing
-- `threePointRightThenLeft 1 = 1 / 4`.
theorem iterated_condExp_order_ne_at_one :
    threePointLeftThenRight 1 ≠ threePointRightThenLeft 1 := sorry

/-- Exercise 8.2.4: on the uniform probability space on three points, with the partitions
`{0} | {1, 2}` and `{0, 1} | {2}`, iterating conditional expectation in the two possible orders
need not give almost surely equal random variables. -/
-- Proof sketch: a pointwise almost-everywhere equality on the countable three-point space holds at
-- every point of nonzero measure; apply this at `1`, where the singleton has positive
-- `threePointUniformMeasure`, and then use `iterated_condExp_order_ne_at_one`.
theorem iterated_condExp_order_ne :
    ¬ threePointLeftThenRight =ᵐ[threePointUniformMeasure] threePointRightThenLeft := by
  intro h
  exact iterated_condExp_order_ne_at_one <|
    ae_iff_of_countable.mp h 1 threePointUniformMeasure_singleton_one_ne_zero

/-- The same three-point model also yields genuinely different functions, not just distinct
almost-everywhere classes. -/
theorem iterated_condExp_order_pointwise_ne :
    threePointLeftThenRight ≠ threePointRightThenLeft := by
  intro h
  exact iterated_condExp_order_ne_at_one (congrArg (fun f : Ω₃ → ℝ ↦ f 1) h)

/-! ### Exercise_8_2_5 (from Items/Chap08) -/
open MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

-- Proof sketch: apply `condExp_mono` to the pointwise bound
-- `Set.indicator {ω | ε ≤ ‖X ω‖₊} (fun _ ↦ (1 : ℝ)) ≤ fun ω ↦ (f ‖X ω‖₊ : ℝ) / f ε`,
-- then use `condExp_smul` to pull out the constant factor `1 / f ε`; the left-hand side is
-- exactly `P⟦{ω | ε ≤ ‖X ω‖₊} | ℱ⟧`.
/-- Exercise 8.2.5: the conditional Markov inequality. For a monotone increasing function
`f : [0, ∞) → [0, ∞)` and a threshold `ε` with `f ε > 0`, the conditional probability of the tail event
`{ω | |X ω| ≥ ε}` is almost surely bounded by the conditional expectation of `f (|X|)` divided by
`f ε`. -/
theorem condProb_abs_ge_le_condExp_div_of_monotone
    {ℱ : MeasurableSpace Ω} {X : Ω → ℝ} (hX : Measurable[mΩ] X)
    {f : ℝ≥0 → ℝ≥0} (hf : Monotone f) {ε : ℝ≥0} (hfε : 0 < f ε)
    (hfi : Integrable (fun ω ↦ (f ‖X ω‖₊ : ℝ)) P) :
    P⟦{ω | ε ≤ ‖X ω‖₊} | ℱ⟧ ≤ᵐ[P]
      fun ω ↦ P[fun ω ↦ (f ‖X ω‖₊ : ℝ) | ℱ] ω / (f ε : ℝ) := by
  set A : Set Ω := {ω | ε ≤ ‖X ω‖₊}
  set g : Ω → ℝ := fun ω ↦ (f ‖X ω‖₊ : ℝ)
  set c : ℝ := (f ε : ℝ)
  have hXnn : @Measurable Ω ℝ≥0 mΩ NNReal.measurableSpace (fun ω ↦ ‖X ω‖₊) := by
    simpa using (@Measurable.nnnorm ℝ Ω inferInstance inferInstance inferInstance mΩ X hX)
  have hA : @MeasurableSet Ω mΩ A := by
    change @MeasurableSet Ω mΩ ((fun ω ↦ ‖X ω‖₊) ⁻¹' Set.Ici ε)
    exact MeasurableSet.preimage measurableSet_Ici hXnn
  have hc : 0 < c := by
    simpa [c] using hfε
  have hg_int : Integrable g P := by
    simpa [g] using hfi
  have hleft_int : Integrable (Set.indicator A (fun _ ↦ (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).indicator hA
  have hright_int : Integrable (fun ω ↦ g ω / c) P := by
    simpa [g, c, div_eq_mul_inv] using hg_int.mul_const c⁻¹
  have hpointwise : Set.indicator A (fun _ ↦ (1 : ℝ)) ≤ᵐ[P] fun ω ↦ g ω / c :=
    .of_forall fun ω ↦ by
      by_cases hω : ω ∈ A
      · have hge : f ε ≤ f ‖X ω‖₊ := hf hω
        have hdiv : 1 ≤ g ω / c := by
          rw [one_le_div hc]
          exact_mod_cast hge
        simpa [A, g, c, hω] using hdiv
      · have hnonneg : 0 ≤ g ω / c := by
          have hg_nonneg : 0 ≤ g ω := by
            change 0 ≤ (f ‖X ω‖₊ : ℝ)
            exact_mod_cast (f ‖X ω‖₊).2
          exact div_nonneg hg_nonneg hc.le
        simpa [A, g, c, hω] using hnonneg
  have hmono : P⟦A | ℱ⟧ ≤ᵐ[P] P[fun ω ↦ g ω / c | ℱ] := by
    simpa using condExp_mono hleft_int hright_int hpointwise
  have hpull : P[fun ω ↦ g ω / c | ℱ] =ᵐ[P] fun ω ↦ P[g | ℱ] ω / c := by
    simpa [g, c, div_eq_mul_inv, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      (condExp_smul c⁻¹ g ℱ)
  simpa [A, g, c] using hmono.trans_eq hpull

/-! ### Exercise_8_2_6 (from Items/Chap08) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {P : Measure Ω}

-- Proof sketch: for each rational `q`, apply `condExp_nonneg` to `(X + q • Y)^2`, then expand
-- the conditional expectation with `condExp_add` and `condExp_smul`. This yields a pointwise
-- nonnegative quadratic polynomial in `q`; extend it to all real `t` by density of `ℚ` and bound
-- the discriminant.
/-- Exercise 8.2.6: for square-integrable real random variables `X` and `Y`, the conditional
Cauchy--Schwarz inequality states that the square of the conditional expectation of `XY` is bounded
almost surely by the product of the conditional expectations of `X²` and `Y²`. -/
theorem condExp_mul_sq_ae_le_condExp_sq_mul_condExp_sq {ℱ : MeasurableSpace Ω}
    {X Y : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    P[X * Y | ℱ] ^ 2 ≤ᵐ[P] P[X ^ 2 | ℱ] * P[Y ^ 2 | ℱ] := by
  by_cases hℱ : ℱ ≤ mΩ
  · let A : Ω → ℝ := P[X ^ 2 | ℱ]
    let B : Ω → ℝ := P[X * Y | ℱ]
    let C : Ω → ℝ := P[Y ^ 2 | ℱ]
    have hXY_int : Integrable (X * Y) P := memLp_one_iff_integrable.1 <| hY.mul hX
    have hquad_rat (q : ℚ) : 0 ≤ᵐ[P] (q : ℝ) ^ 2 • C + (2 * (q : ℝ)) • B + A := by
      have hnonneg : 0 ≤ᵐ[P] P[(X + (q : ℝ) • Y) ^ 2 | ℱ] :=
        condExp_nonneg <| .of_forall fun _ ↦ sq_nonneg _
      refine hnonneg.trans_eq ?_
      calc
        P[(X + (q : ℝ) • Y) ^ 2 | ℱ]
            =ᵐ[P] P[X ^ 2 + (2 * (q : ℝ)) • (X * Y) + (q : ℝ) ^ 2 • (Y ^ 2) | ℱ] := by
              refine condExp_congr_ae <| .of_forall fun ω ↦ ?_
              change (X ω + (q : ℝ) * Y ω) ^ 2 =
                X ω ^ 2 + (2 * (q : ℝ)) * (X ω * Y ω) + (q : ℝ) ^ 2 * Y ω ^ 2
              ring
        _ =ᵐ[P] P[X ^ 2 | ℱ] + P[(2 * (q : ℝ)) • (X * Y) + (q : ℝ) ^ 2 • (Y ^ 2) | ℱ] := by
              simpa [A, add_assoc] using
                condExp_add hX.integrable_sq
                  ((hXY_int.const_mul _).add (hY.integrable_sq.const_mul _)) ℱ
        _ =ᵐ[P] P[X ^ 2 | ℱ] + (P[(2 * (q : ℝ)) • (X * Y) | ℱ] + P[(q : ℝ) ^ 2 • (Y ^ 2) | ℱ]) := by
              filter_upwards [condExp_add (hXY_int.const_mul _) (hY.integrable_sq.const_mul _) ℱ]
                with ω hω
              simpa using hω
        _ =ᵐ[P] A + ((2 * (q : ℝ)) • B + (q : ℝ) ^ 2 • C) := by
              filter_upwards [condExp_smul (2 * (q : ℝ)) (X * Y) ℱ,
                condExp_smul ((q : ℝ) ^ 2) (Y ^ 2) ℱ] with ω hω₁ hω₂
              simp [A, B, C, hω₁, hω₂]
        _ =ᵐ[P] (q : ℝ) ^ 2 • C + (2 * (q : ℝ)) • B + A := by
              refine .of_forall fun ω ↦ ?_
              simp [add_left_comm, add_comm]
    have hquad : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ ((q : ℝ) ^ 2 • C + (2 * (q : ℝ)) • B + A) ω :=
      ae_all_iff.2 hquad_rat
    filter_upwards [hquad] with ω hω
    have hreal : ∀ t : ℝ, 0 ≤ C ω * (t * t) + (2 * B ω) * t + A ω := by
      intro t
      refine Rat.denseRange_cast.induction_on t ?_ fun q ↦ ?_
      · have hcont : Continuous fun x : ℝ ↦ C ω * (x * x) + (2 * B ω) * x + A ω := by
          continuity
        exact isClosed_le continuous_const hcont
      · simpa [Pi.smul_apply, pow_two, mul_assoc, mul_left_comm, mul_comm] using hω q
    have hdisc : discrim (C ω) (2 * B ω) (A ω) ≤ 0 := discrim_le_zero hreal
    rw [discrim, sq] at hdisc
    have hpoint : B ω ^ 2 ≤ A ω * C ω := by
      nlinarith
    simpa [A, B, C, mul_comm] using hpoint
  · exact Filter.Eventually.of_forall fun _ ↦ by
      simp [condExp_of_not_le hℱ]

/-! ### Exercise_8_2_7 (from Items/Chap08) -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

-- Proof sketch: by exchangeability of an i.i.d. finite family, the pairs
-- `(X i, fun ω ↦ ∑ j : Fin n, X j ω)` and `(X j, fun ω ↦ ∑ j : Fin n, X j ω)` have the same law,
-- so the conditional expectations of the coordinates given the total sum agree almost surely.
-- Use identical distribution to propagate integrability from the chosen coordinate `X i` to every
-- other coordinate. Summing the equal conditional expectations over all coordinates and using
-- `condExp_finset_sum` together with `condExp_of_measurable_ae_eq` for the total sum yields
-- `n * P[X i | σ(S_n)] = S_n`, hence `P[X i | σ(S_n)] = S_n / n`.
/-- Exercise 8.2.7: for a measurable i.i.d. family `X : Fin n → Ω → ℝ`, the conditional
expectation of any integrable coordinate given the total sum is almost surely the sample mean. -/
theorem condExp_coordinate_given_sum_ae_eq_average {n : ℕ} {X : Fin n → Ω → ℝ}
    (hX_meas : ∀ i, Measurable (X i)) (hX_iid : IsIID X P) (i : Fin n)
    (hXi_int : Integrable (X i) P) :
    P[X i | MeasurableSpace.comap (fun ω ↦ ∑ j : Fin n, X j ω) inferInstance] =ᵐ[P]
      fun ω ↦ (∑ j : Fin n, X j ω) / n := sorry

/-! ### Exercise_8_2_8 (from Items/Chap08) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

-- Proof sketch: write the conditional expectation of `fun ω ↦ X₁ ω ⊓ X₂ ω` given `X₁`
-- using `ProbabilityTheory.condExp_prod_ae_eq_integral_condDistrib` for the function
-- `(x, y) ↦ x ⊓ y`. The measurability of `X₁` determines the conditioning σ-algebra
-- `MeasurableSpace.comap X₁ (borel ℝ)`, while `HasLaw X₂ (expMeasure θ) P` supplies the
-- `P`-almost-everywhere measurability required by the conditional-distribution API. Independence
-- then identifies the conditional distribution of `X₂` given `X₁` with `expMeasure θ`, and the
-- resulting one-dimensional integral evaluates to `(1 - exp (-θ x)) / θ`.
/-- Exercise 8.2.8: if `X₁` is measurable, `X₁` and `X₂` are independent, and both have
exponential law with common rate `θ`, then the conditional expectation of `X₁ ∧ X₂` given `X₁`
is `(1 - exp (-θ X₁)) / θ` almost surely. Since `P` is a probability measure, the law hypotheses
already force `expMeasure θ` to be a probability measure, hence in particular `θ > 0`. -/
theorem condExp_min_of_indep_exp_ae_eq {X₁ X₂ : Ω → ℝ} {θ : ℝ}
    (hX₁_meas : Measurable X₁)
    (hX₁_exp : HasLaw X₁ (expMeasure θ) P) (hX₂_exp : HasLaw X₂ (expMeasure θ) P)
    (h_indep : X₁ ⟂ᵢ[P] X₂) :
    P[fun ω ↦ X₁ ω ⊓ X₂ ω | MeasurableSpace.comap X₁ (borel ℝ)] =ᵐ[P]
      fun ω ↦ (1 - Real.exp (-(θ * X₁ ω))) / θ := sorry

/-! ### Exercise_8_2_9 (from Items/Chap08) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

-- Proof sketch: identify the conditional expectation of `h ∘ X` given `Y` with the integral of
-- `h` against the regular conditional distribution of `X` given `Y`, then use the joint-density
-- hypothesis to compute that conditional distribution by disintegrating the joint law of `(X, Y)`
-- along the second coordinate and normalizing by the marginal density of `Y`.
/-- Exercise 8.2.9 (1): If `X` and `Y` have joint Lebesgue density `f` and `h(X)` is integrable,
then the conditional expectation of `h(X)` given `Y` is almost surely the ratio of the `x`-integral
of `h(x) f(x, Y)` and the marginal density integral of `Y`. -/
theorem condExp_transform_given_right_ae_eq_joint_density_ratio
    {X Y : Ω → ℝ} {f : ℝ → ℝ → ENNReal} {h : ℝ → ℝ}
    (hf : Measurable fun z : ℝ × ℝ ↦ f z.1 z.2)
    (h_joint : HasLaw (fun ω ↦ (X ω, Y ω))
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
        fun z : ℝ × ℝ ↦ f z.1 z.2) P)
    (hh_meas : Measurable h) (hh_int : Integrable (fun ω ↦ h (X ω)) P) :
    P[h ∘ X | MeasurableSpace.comap Y (borel ℝ)] =ᵐ[P]
      fun ω ↦
        (∫ x, h x * (f x (Y ω)).toReal) /
          (first_marginal_density (fun y x ↦ f x y) (Y ω)).toReal := sorry

section IidExp

variable {X Y : Ω → ℝ} {θ : ℝ}

local notation "mSum" => MeasurableSpace.comap (X + Y) (borel ℝ)

-- Proof sketch: compute the conditional law of `X` given `X + Y = s` from the joint exponential
-- density in the setting of Exercise 8.2.9 (2). It is the conditioned Lebesgue measure on
-- `[0, s]`.
private theorem condDistrib_left_given_sum_of_iid_exp_ae_eq_uniform_interval_aux
    (hX : HasLaw X (expMeasure θ) P) (hY : HasLaw Y (expMeasure θ) P) (hXY : X ⟂ᵢ[P] Y) :
    ∀ᵐ s ∂P.map (X + Y), condDistrib X (X + Y) P s = volume[|Set.Icc 0 s] := sorry

-- Proof sketch: the pair `(X, Y)` is exchangeable because `X` and `Y` are independent with the
-- same exponential law. Hence the conditional expectations of `X` and `Y` given `X + Y` agree
-- almost surely. Summing them and using that `X + Y` is measurable with respect to its own
-- generated σ-algebra yields `2 * E[X | X + Y] = X + Y`.
/-- Exercise 8.2.9 (2), expectation consequence: if `X` and `Y` are independent and both have
exponential law with common rate `θ`, then the conditional expectation of `X` given `X + Y` is
almost surely half of the sum. -/
theorem condExp_left_given_sum_of_iid_exp_ae_eq_half_sum
    (hX : HasLaw X (expMeasure θ) P) (hY : HasLaw Y (expMeasure θ) P) (hXY : X ⟂ᵢ[P] Y) :
    P[X | mSum] =ᵐ[P] (X + Y) / 2 := sorry

-- Proof sketch: evaluate the auxiliary conditional-distribution formula on the event `(-∞, x]`. The
-- conditioned Lebesgue measure on `[0, s]` gives mass `1` when `s ≤ x` and `x / s` when `s > x`.
/-- Exercise 8.2.9 (3): if `X` and `Y` are independent and both have
exponential law with common rate `θ`, then for every `x ≥ 0` the conditional probability of the
event `X ≤ x` given `X + Y` is almost surely the truncated-uniform cdf on the random interval
`[0, X + Y]`. -/
theorem condProb_left_le_given_sum_of_iid_exp_ae_eq {x : ℝ} (hx : 0 ≤ x)
    (hX : HasLaw X (expMeasure θ) P) (hY : HasLaw Y (expMeasure θ) P) (hXY : X ⟂ᵢ[P] Y) :
    P⟦X ⁻¹' Set.Iic x | mSum⟧ =ᵐ[P]
      fun ω ↦ if X ω + Y ω ≤ x then 1 else x / (X ω + Y ω) := sorry

end IidExp
