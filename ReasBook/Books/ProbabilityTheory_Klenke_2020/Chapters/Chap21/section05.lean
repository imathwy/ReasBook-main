import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_21_5_1 (from Items/Chap21) -/
open Filter MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} {B : NNReal → Ω → ℝ}

/- Recalled clause (1): the Brownian bridge `Y_t = W_t - t W_1` associated to a Brownian motion
has almost surely continuous sample paths on `[0,1]`. -/
recall brownianBridge_hasAlmostSurelyContinuousPaths

/- Recalled clause (2): the Brownian bridge associated to a Brownian motion is a Gaussian process
on `[0,1]`. -/
recall brownianBridge_isGaussianProcess

/- Recalled clause (3): the covariance kernel of the Brownian bridge is
`Cov[Y_t, Y_s] = (s ∧ t) - st`. -/
recall brownianBridge_covariance_eq

/-- The conditioning event `{ω | B 1 ω ∈ (-ε, ε)}` used in Exercise 21.5.1. -/
def brownianEndpointWindow (B : NNReal → Ω → ℝ) (ε : ℝ) : Set Ω :=
  {ω | B 1 ω ∈ Set.Ioo (-ε) ε}

theorem measurable_brownianFiniteDimensionalCoordinates
    (hB : IsBrownianMotion μ B) {n : ℕ}
    (times : Fin (n + 1) → BrownianBridgeTime) :
    Measurable (finiteDimensionalEvaluation B fun i ↦ (times i : NNReal)) :=
  measurable_pi_lambda _ fun i ↦ (hB.stronglyMeasurable (times i)).measurable

theorem measurable_brownianBridgeFiniteDimensionalCoordinates
    (hB : IsBrownianMotion μ B) {n : ℕ}
    (times : Fin (n + 1) → BrownianBridgeTime) :
    Measurable (fun ω i ↦ brownianBridge B (times i) ω) := by
  refine measurable_pi_lambda _ ?_
  intro i
  have hB1_meas : Measurable (B 1) := (hB.stronglyMeasurable 1).measurable
  simpa [brownianBridge] using
    ((hB.stronglyMeasurable (times i)).measurable.sub (measurable_const.mul hB1_meas))

theorem brownianEndpointWindow_measure_ne_zero
    (hB : IsBrownianMotion μ B) {ε : ℝ} (hε : 0 < ε) :
    μ (brownianEndpointWindow B ε) ≠ 0 := by
  have hB1 : HasLaw (B 1) (gaussianReal 0 1) μ :=
    hB.gaussian_marginal (by positivity)
  have hB1_meas : Measurable (B 1) := (hB.stronglyMeasurable 1).measurable
  have hgauss_ne : gaussianReal 0 1 (Set.Ioo (-ε) ε) ≠ 0 := by
    intro hzero
    have hvol_zero : (volume : Measure ℝ) (Set.Ioo (-ε) ε) = 0 :=
      gaussianReal_absolutelyContinuous' 0 one_ne_zero hzero
    have hvol_pos : (0 : ENNReal) < (volume : Measure ℝ) (Set.Ioo (-ε) ε) := by
      rw [Real.volume_Ioo, ENNReal.ofReal_pos]
      linarith
    exact hvol_pos.ne' hvol_zero
  have hμeq :
      μ (brownianEndpointWindow B ε) = gaussianReal 0 1 (Set.Ioo (-ε) ε) := by
    calc
      μ (brownianEndpointWindow B ε) = μ ((B 1) ⁻¹' Set.Ioo (-ε) ε) := by
        rfl
      _ = Measure.map (B 1) μ (Set.Ioo (-ε) ε) := by
        rw [Measure.map_apply hB1_meas measurableSet_Ioo]
      _ = gaussianReal 0 1 (Set.Ioo (-ε) ε) := by
        rw [hB1.map_eq]
  rw [hμeq]
  exact hgauss_ne

/- For this item:
- `source-facing`: the conditioned finite-dimensional Brownian coordinate law and the matching
  Brownian-bridge finite-dimensional law.
- `core/canonical`: both are `ProbabilityMeasure (Fin (n + 1) → ℝ)` owners.
- `bridge/view`: the conditioning event and the coordinate pushforwards; the Brownian side uses
  the chapter owner `finiteDimensionalEvaluation`, and the right-limit is expressed directly on
  the positive parameter space `Set.Ioi 0` rather than through a second public law family.
-/

/-- The Brownian-bridge finite-dimensional law at the time tuple `times`. -/
def brownianBridgeFiniteDimensionalLaw
    (hB : IsBrownianMotion μ B) {n : ℕ}
    (times : Fin (n + 1) → BrownianBridgeTime) :
    ProbabilityMeasure (Fin (n + 1) → ℝ) :=
  ProbabilityMeasure.map ⟨μ, hB.isProbabilityMeasure⟩
    (measurable_brownianBridgeFiniteDimensionalCoordinates hB times).aemeasurable

/-- The finite-dimensional law of the Brownian coordinates at `times`, conditioned on the endpoint
event `B₁ ∈ (-ε, ε)` for a positive window radius `ε`. -/
def conditionedBrownianFiniteDimensionalLaw
    (hB : IsBrownianMotion μ B) {n : ℕ}
    (times : Fin (n + 1) → BrownianBridgeTime) (ε : Set.Ioi (0 : ℝ)) :
    ProbabilityMeasure (Fin (n + 1) → ℝ) :=
  ProbabilityMeasure.map
    ⟨μ[|brownianEndpointWindow B ε], by
      letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
      exact cond_isProbabilityMeasure (brownianEndpointWindow_measure_ne_zero hB ε.2)⟩
    (measurable_brownianFiniteDimensionalCoordinates hB times).aemeasurable

-- Proof sketch: for each fixed finite tuple of times in `[0,1]`, compute the conditioned Gaussian
-- law of `(W_{t₀}, …, W_{tₙ})` given `W₁ ∈ (-ε, ε)` and let `ε ↓ 0`. The limiting centered
-- Gaussian vector has covariance matrix `((tᵢ : NNReal) ⊓ (tⱼ : NNReal)) - tᵢ tⱼ`, which is the
-- finite-dimensional law of the Brownian bridge from the recalled Gaussianity and covariance
-- statements above.
/-- Exercise 21.5.1: for every finite tuple of times in `[0,1]`, the event-conditioned law of the
Brownian coordinates given `B₁ ∈ (-ε, ε)` converges, as `ε ↓ 0`, to the corresponding
Brownian-bridge finite-dimensional law. -/
theorem conditioned_brownian_finiteDimensionalDistributions_tendsto_brownianBridge
    (hB : IsBrownianMotion μ B) {n : ℕ}
    (times : Fin (n + 1) → BrownianBridgeTime) :
    Tendsto (fun ε : Set.Ioi (0 : ℝ) ↦ conditionedBrownianFiniteDimensionalLaw hB times ε)
      (Filter.comap (Subtype.val : Set.Ioi (0 : ℝ) → ℝ) (𝓝[>] (0 : ℝ)))
      (𝓝 (brownianBridgeFiniteDimensionalLaw hB times)) := sorry

end ProbabilityTheory

/-! ### Exercise_21_5_2 (from Items/Chap21) -/
open MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

namespace IsBrownianMotion

-- Proof sketch: write `B 1 = B T + (B 1 - B T)` with `0 < T < 1`. By the Brownian-motion axioms,
-- `B T` and `B 1 - B T` are independent centered Gaussians with variances `T` and `1 - T`.
-- Apply the Gaussian conditional-distribution formula from Example 8.32 to the pair
-- `(B T, B 1 - B T)` and simplify the resulting conditional mean and variance.
/-- Exercise 21.5.2: in kernel form, for `T ∈ (0,1)`, the regular conditional distribution of
`W_T` given `W_1` is, for `μ.map (B 1)`-almost every `x`, the Gaussian law with mean `Tx` and
variance `T(1 - T)`. -/
theorem condDistrib_timeValue_given_terminalValue_ae_eq
    {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) (T : Set.Ioo (0 : NNReal) 1) :
    letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
    condDistrib (B T) (B 1) μ =ᵐ[μ.map (B 1)]
      fun x ↦ gaussianReal ((T : ℝ) * x) ((T : NNReal) * (1 - (T : NNReal))) := by
  have hlawT' : HasLaw (B T)
      (gaussianReal 0 ⟨((NNReal.sqrt (T : NNReal) : ℝ) ^ 2), sq_nonneg _⟩) μ := by
    have hlawT : HasLaw (B T) (gaussianReal 0 (T : NNReal)) μ := hB.gaussian_marginal T.2.1
    simpa using hlawT
  have hinc' : HasLaw (fun ω ↦ B 1 ω - B T ω)
      (gaussianReal 0 ⟨((NNReal.sqrt (1 - (T : NNReal)) : ℝ) ^ 2), sq_nonneg _⟩) μ := by
    have hinc : HasLaw (fun ω ↦ B 1 ω - B T ω) (gaussianReal 0 (1 - (T : NNReal))) μ := by
      let U : NNReal := 1 - (T : NNReal)
      have hU_pos : 0 < U := by
        simpa [U] using T.2.2
      have hlawU : HasLaw (B U) (gaussianReal 0 U) μ := hB.gaussian_marginal hU_pos
      have hlawInc : HasLaw (fun ω ↦ B U ω - B 0 ω) (gaussianReal 0 U) μ := by
        refine hlawU.congr ?_
        simp [hB.zero]
      have hlawInc' : HasLaw (fun ω ↦ B (U + 0) ω - B 0 ω) (gaussianReal 0 U) μ := by
        simpa using hlawInc
      have hstationary := hB.stationaryIncrements 0 U T
      have hsum : (T : NNReal) + (1 - (T : NNReal)) = 1 := by
        exact add_tsub_cancel_of_le T.2.2.le
      simpa [U, hsum, add_comm, add_left_comm, add_assoc] using hstationary.symm.hasLaw hlawInc'
    simpa using hinc
  have hindep : (B T) ⟂ᵢ[μ] (fun ω ↦ B 1 ω - B T ω) := by
    have hzero : ∀ᵐ ω ∂μ, B 0 ω = 0 := by
      simp [hB.zero]
    simpa using hB.indepIncrements.indepFun_eval_sub T.2.1.le T.2.2.le hzero
  have hmain := condDistrib_gaussian_left_given_sum_ae_eq μ 0 0
    (NNReal.sqrt (T : NNReal)) (NNReal.sqrt (1 - (T : NNReal))) hlawT' hinc' hindep
  have hsum_fun : (B T + fun ω ↦ -B T ω + B 1 ω) = B 1 := by
    funext ω
    change B T ω + (-B T ω + B 1 ω) = B 1 ω
    ring
  have hsum_real : (T : ℝ) + ((1 - (T : NNReal) : NNReal) : ℝ) = 1 := by
    exact_mod_cast add_tsub_cancel_of_le T.2.2.le
  simpa [hsum_fun, hsum_real, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc,
    mul_left_comm, mul_comm] using hmain

/-- Pointwise form of `condDistrib_timeValue_given_terminalValue_ae_eq`. -/
theorem condDistrib_timeValue_given_terminalValue_ae_eq_apply
    {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion μ B) (T : Set.Ioo (0 : NNReal) 1) :
    letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
    ∀ᵐ x ∂μ.map (B 1),
      condDistrib (B T) (B 1) μ x =
        gaussianReal ((T : ℝ) * x) ((T : NNReal) * (1 - (T : NNReal))) := by
  simpa using condDistrib_timeValue_given_terminalValue_ae_eq hB T

end IsBrownianMotion

end ProbabilityTheory

/-! ### Exercise_21_5_3 (from Items/Chap21) -/
open MeasureTheory ProbabilityTheory

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: Exercise 26.1.1 later formalizes the process
-- `Y_t = X_t - a - t (b - a)` for the explicit Brownian-bridge SDE solution
-- `X = brownianBridgeSDESolutionCandidate a b W`. In the zero-endpoint case `a = b = 0`, this is
-- exactly the source process `Y_t = (1 - t) ∫_0^t (1 - s)⁻¹ dW_s`, and Exercise 26.1.1 proves the
-- Brownian-bridge owner statement directly for that centered process.
/-- Exercise 21.5.3: the zero-endpoint Brownian-bridge SDE solution,
viewed through its centered bridge process, is a Brownian bridge on `[0,1]`. -/
theorem brownianBridgeSDEZeroEndpoint_bridgeProcess_isBrownianBridge
    {μ : Measure Ω} {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W) :
    IsBrownianBridge μ
      (brownianBridgeSDEBridgeProcess (brownianBridgeSDESolutionCandidate 0 0 W) 0 0) :=
  brownianBridgeSDESolutionCandidate_bridgeProcess_isBrownianBridge hW 0 0

end ProbabilityTheory

/-! ### Exercise_21_5_4 (from Items/Chap21) -/
open MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

/-- The index set `[0,1]^d` for the `d`-parameter Brownian sheet. -/
abbrev BrownianSheetIndex (d : ℕ) := Fin d → Set.Icc (0 : ℝ) 1

/-- The covariance kernel `∏ᵢ min (sᵢ, tᵢ)` of the Brownian sheet on `[0,1]^d`. -/
def brownianSheetCovariance {d : ℕ} (s t : BrownianSheetIndex d) : ℝ :=
  ∏ i : Fin d, min (s i : ℝ) (t i : ℝ)

-- Proof sketch: unfold `brownianSheetCovariance`.
/-- Expanding `brownianSheetCovariance` gives the product of the coordinatewise minima. -/
theorem brownianSheetCovariance_def {d : ℕ} (s t : BrownianSheetIndex d) :
    brownianSheetCovariance s t = ∏ i : Fin d, min (s i : ℝ) (t i : ℝ) := sorry

/-- The canonical coordinate process on the Brownian-sheet path space `(BrownianSheetIndex d → ℝ)`.
-/
def brownianSheetCoordinateProcess (d : ℕ) :
    BrownianSheetIndex d → (BrownianSheetIndex d → ℝ) → ℝ :=
  fun t ω ↦ ω t

-- Proof sketch: unfold `brownianSheetCoordinateProcess`.
/-- Evaluating the Brownian-sheet coordinate process at `t` returns the coordinate `ω t`. -/
theorem brownianSheetCoordinateProcess_apply {d : ℕ}
    (t : BrownianSheetIndex d) (ω : BrownianSheetIndex d → ℝ) :
    brownianSheetCoordinateProcess d t ω = ω t := sorry

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Exercise 21.5.4: a Brownian sheet on `[0,1]^d` is a Gaussian process with covariance kernel
`∏ᵢ min (sᵢ, tᵢ)` that admits an almost surely continuous modification. -/
class IsBrownianSheet (d : ℕ) (μ : Measure Ω) (W : BrownianSheetIndex d → Ω → ℝ) : Prop
    extends IsGaussianProcess W μ where
  /-- The covariance kernel of a Brownian sheet is `∏ᵢ min (sᵢ, tᵢ)`. -/
  covariance_eq :
    ∀ s t : BrownianSheetIndex d, cov[W s, W t; μ] = brownianSheetCovariance s t
  /-- A Brownian sheet admits a modification with almost surely continuous sample paths. -/
  exists_continuous_modification :
    ∃ W' : BrownianSheetIndex d → Ω → ℝ,
      AreModifications μ W W' ∧ HasAlmostSurelyContinuousPaths μ W'

/-- A Gaussian process with Brownian-sheet covariance and almost surely continuous paths is a
Brownian sheet. -/
instance {d : ℕ} {μ : Measure Ω} {W : BrownianSheetIndex d → Ω → ℝ}
    (hgauss : IsGaussianProcess W μ)
    (hcov : ∀ s t : BrownianSheetIndex d, cov[W s, W t; μ] = brownianSheetCovariance s t)
    (hcont : HasAlmostSurelyContinuousPaths μ W) :
    IsBrownianSheet d μ W := sorry

-- Proof sketch: realize the coordinate process on path space under a Gaussian probability law
-- whose finite-dimensional marginals have covariance matrix
-- `(brownianSheetCovariance s t)_{s,t}`, obtained from a suitable orthonormal basis on
-- `[0,1]^d`.
/-- Part (1): there exists a Gaussian process on `[0,1]^d` whose covariance kernel is
`∏ᵢ min (sᵢ, tᵢ)`. -/
theorem exists_brownianSheetGaussianProcess (d : ℕ) :
    ∃ μ : ProbabilityMeasure (BrownianSheetIndex d → ℝ),
      IsGaussianProcess (brownianSheetCoordinateProcess d) (μ : Measure (BrownianSheetIndex d → ℝ)) ∧
      ∀ s t : BrownianSheetIndex d,
        cov[brownianSheetCoordinateProcess d s, brownianSheetCoordinateProcess d t;
          (μ : Measure (BrownianSheetIndex d → ℝ))] = brownianSheetCovariance s t := sorry

-- Proof sketch: apply the continuity criterion from Remark 21.7 to the Gaussian process from
-- part (1), using the Brownian-sheet covariance kernel to obtain the required moment bounds, and
-- then package the Gaussian, covariance, and path-regularity clauses into `IsBrownianSheet`.
/-- Part (2): the Brownian-sheet coordinate process on `[0,1]^d` carries a Brownian-sheet law on
path space. -/
theorem exists_brownianSheetContinuousModification (d : ℕ) :
    ∃ μ : ProbabilityMeasure (BrownianSheetIndex d → ℝ),
      IsBrownianSheet d (μ : Measure (BrownianSheetIndex d → ℝ))
        (brownianSheetCoordinateProcess d) := sorry

end ProbabilityTheory

/-! ### Exercise_21_5_5 (from Items/Chap21) -/
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u

noncomputable section

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- The coefficient sequence in the cosine-basis construction of Brownian motion from
Example 21.29: the zeroth coefficient is the constant-mode Gaussian coordinate, and the
positive-frequency coefficients are the cosine coordinates scaled by `1 / (nπ)` after integrating
the basis functions `b₀(x) = 1` and `bₙ(x) = √2 cos(nπx)` from `0` to `t`. -/
def brownianFourierCoefficients (ξ : ℕ → Lp ℝ 2 μ) : ℕ → Ω → ℝ
  | 0 => ξ 0
  | n + 1 => fun ω ↦ ξ (n + 1) ω / (((n + 1 : ℝ) * Real.pi))

@[simp] theorem brownianFourierCoefficients_zero (ξ : ℕ → Lp ℝ 2 μ) :
    brownianFourierCoefficients ξ 0 = ξ 0 :=
  rfl

@[simp] theorem brownianFourierCoefficients_succ (ξ : ℕ → Lp ℝ 2 μ) (n : ℕ) :
    brownianFourierCoefficients ξ (n + 1) =
      fun ω ↦ ξ (n + 1) ω / (((n + 1 : ℝ) * Real.pi)) :=
  rfl

section BrownianFourierCoefficients

variable [IsProbabilityMeasure μ]
variable (ξ : ℕ → Lp ℝ 2 μ)
variable (hξ_gaussian : ∀ n, HasLaw (ξ n : Ω → ℝ) (gaussianReal 0 1) μ)

-- Proof sketch: `brownianFourierCoefficients ξ 0` is just the zeroth Gaussian coordinate, and for
-- `n ≥ 1` the coefficient is `ξₙ / (nπ)`. Hence the second moments are `1` at `n = 0` and
-- `1 / (π² n²)` for positive modes, which is summable. Tonelli or monotone convergence gives
-- integrability of `∑ (Aₙ)²`, forcing almost-sure square summability.
/-- Exercise 21.5.5 (1): the coefficients in the cosine-basis construction of Brownian motion are
almost surely square-summable. -/
theorem brownianFourierCoefficients_sqSummable_ae :
    ∀ᵐ ω ∂μ, Summable (fun n ↦ (brownianFourierCoefficients ξ n ω) ^ (2 : ℕ)) := sorry

variable (hξ_indep : iIndepFun (fun n ↦ (ξ n : Ω → ℝ)) μ)

-- Proof sketch: the positive-mode coefficients are independent centered Gaussians with standard
-- deviation comparable to `1 / n`. Kolmogorov's three-series theorem applied to
-- `brownianFourierCoefficients ξ` yields almost-sure divergence of the nonnegative series
-- `∑ |Aₙ|`, and adding the zeroth term does not change the divergence conclusion.
/-- Exercise 21.5.5 (2): the series of absolute values of the Brownian Fourier coefficients
diverges to `+∞` almost surely. -/
theorem brownianFourierCoefficients_absPartialSums_tendsto_atTop_ae :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ ↦ ∑ k ∈ Finset.range (n + 1), |brownianFourierCoefficients ξ k ω|)
        atTop atTop := sorry

-- Proof sketch: the coefficients form an independent centered Gaussian sequence with summable
-- variances, namely `1` at index `0` and `1 / (π² n²)` on the positive modes. Kolmogorov's
-- three-series theorem therefore gives almost-sure convergence of the series `∑ Aₙ`.
/-- Exercise 21.5.5 (3): the Brownian Fourier coefficient series itself converges almost surely. -/
theorem brownianFourierCoefficients_summable_ae :
    ∀ᵐ ω ∂μ, Summable (fun n ↦ brownianFourierCoefficients ξ n ω) := sorry

end BrownianFourierCoefficients

end ProbabilityTheory

/-! ### Lemma_21_5 (from Items/Chap21) -/
open MeasureTheory Set

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [TopologicalSpace E]

-- Proof sketch: take the union of the null disagreement events over the countable index set.
/-- Lemma 21.5, countable-index case: if two processes indexed by a countable type are
modifications of one another, then they are indistinguishable. -/
theorem indistinguishable_of_forall_aeEq_of_countable
    {I : Type*} (μ : Measure Ω) (X Y : I → Ω → E)
    (hXY : AreModifications μ X Y) [Countable I] :
    AreIndistinguishable μ X Y := sorry

variable {I : Set ℝ}

-- Proof sketch: pass to a countable dense subset of the interval `I`, obtain a common null set
-- there, and then use almost sure right continuity and uniqueness of right limits in the
-- Hausdorff codomain to extend equality from the dense subset to every time.
/-- Lemma 21.5, interval/right-continuous case: if two processes indexed by an interval `I ⊆ ℝ`
are modifications of one another and both sample paths are almost surely right continuous on `I`,
then the processes are indistinguishable. -/
theorem indistinguishable_of_forall_aeEq_of_ordConnected_of_ae_rightContinuous
    [T2Space E]
    (μ : Measure Ω) (X Y : I → Ω → E)
    (hXY : AreModifications μ X Y) (hI : I.OrdConnected)
    (hX_rc : ∀ᵐ ω ∂μ, ∀ t : I, ContinuousWithinAt (processPath X ω) (Ici t) t)
    (hY_rc : ∀ᵐ ω ∂μ, ∀ t : I, ContinuousWithinAt (processPath Y ω) (Ici t) t) :
    AreIndistinguishable μ X Y := sorry

end ProbabilityTheory

/-! ### Exercise_21_5_6 (from Items/Chap21) -/
noncomputable section

/-- The positive-frequency cosine mode in the half-range Fourier expansion of `1_[0,t]`. -/
def indicator_Icc_zero_t_fourier_cosine_mode (t x : ℝ) (n : ℕ+) : ℝ :=
  (2 * Real.sin ((n : ℝ) * Real.pi * t)) / ((n : ℝ) * Real.pi) *
    Real.cos ((n : ℝ) * Real.pi * x)

/-- The Fourier-cosine term sequence whose sum recovers the indicator of `[0, t]` away from the
jump point. The zeroth term is the constant mode `t`, and the positive terms come from
`indicator_Icc_zero_t_fourier_cosine_mode`. -/
def indicator_Icc_zero_t_fourier_term (t x : ℝ) : ℕ → ℝ
  | 0 => t
  | n + 1 => indicator_Icc_zero_t_fourier_cosine_mode t x ⟨n + 1, Nat.succ_pos _⟩

@[simp] theorem indicator_Icc_zero_t_fourier_term_zero (t x : ℝ) :
    indicator_Icc_zero_t_fourier_term t x 0 = t :=
  rfl

@[simp] theorem indicator_Icc_zero_t_fourier_term_succ_eq_mode (t x : ℝ) (n : ℕ) :
    indicator_Icc_zero_t_fourier_term t x (n + 1) =
      indicator_Icc_zero_t_fourier_cosine_mode t x ⟨n + 1, Nat.succ_pos _⟩ :=
  rfl

-- Proof sketch: unfold the definition of `indicator_Icc_zero_t_fourier_term`; at index `n + 1`
-- it is exactly the positive-mode cosine coefficient from the exercise statement.
/-- The positive Fourier modes of `indicator_Icc_zero_t_fourier_term` are the cosine coefficients
`2 sin((n + 1)π t) / ((n + 1)π)`. -/
theorem indicator_Icc_zero_t_fourier_term_succ (t x : ℝ) (n : ℕ) :
    indicator_Icc_zero_t_fourier_term t x (n + 1) =
      (2 * Real.sin ((n + 1 : ℝ) * Real.pi * t)) / ((n + 1 : ℝ) * Real.pi) *
        Real.cos ((n + 1 : ℝ) * Real.pi * x) := by
  simp [indicator_Icc_zero_t_fourier_cosine_mode]

-- Proof sketch: identify `indicator_Icc_zero_t_fourier_term t x` as the cosine Fourier series of
-- the step function `1_[0,t]`, use the classical pointwise convergence theorem for Fourier series
-- of piecewise smooth functions on `(0,1)`, and evaluate away from the jump point `x = t`.
/-- Exercise 21.5.6: for `t ∈ (0, 1)` and `x ∈ (0, 1) \ {t}`, the Fourier-cosine series with
zeroth term `t` and coefficients `2 sin(nπ t) / (nπ)` sums to the indicator of `[0, t]` at
`x`. -/
theorem indicator_Icc_zero_t_hasSum_fourier_cosine_series {t x : ℝ}
    (ht : t ∈ Set.Ioo 0 1) (hx : x ∈ Set.Ioo 0 1) (hxt : x ≠ t) :
    HasSum (indicator_Icc_zero_t_fourier_term t x)
      ((Set.Icc 0 t).indicator (fun _ ↦ (1 : ℝ)) x) := sorry
