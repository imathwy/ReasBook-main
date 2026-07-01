import Mathlib
import AchimKlenkeLean.Items.Chap21.Definition_21_1
import AchimKlenkeLean.Items.Chap21.Definition_21_4
import AchimKlenkeLean.Items.Chap21.Definition_21_8
import AchimKlenkeLean.Items.Chap21.Theorem_21_18
import AchimKlenkeLean.Items.Chap21.Theorem_21_11

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

private lemma covariance_congr_ae {μ : Measure Ω} {X X' Y Y' : Ω → ℝ}
    (hX : X =ᵐ[μ] X') (hY : Y =ᵐ[μ] Y') :
    cov[X, Y; μ] = cov[X', Y'; μ] := by
  have hIntX : μ[X] = μ[X'] := integral_congr_ae hX
  have hIntY : μ[Y] = μ[Y'] := integral_congr_ae hY
  rw [covariance, covariance]
  refine integral_congr_ae ?_
  filter_upwards [hX, hY] with ω hωX hωY
  simp [hωX, hωY, hIntX, hIntY]

private def pinValueAtZero (X : NNReal → Ω → ℝ) : NNReal → Ω → ℝ :=
  fun t ω ↦ if t = 0 then 0 else X t ω

private lemma areModifications_pinValueAtZero
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : NNReal → Ω → ℝ}
    (hgauss : IsGaussianProcess X μ) (hstart : μ (X 0 ⁻¹' ({0} : Set ℝ)) = 1) :
    AreModifications μ (pinValueAtZero X) X := by
  have hX0_meas : NullMeasurableSet (X 0 ⁻¹' ({0} : Set ℝ)) μ :=
    (hgauss.aemeasurable 0).nullMeasurableSet_preimage (measurableSet_singleton (0 : ℝ))
  have hX0_ae_set : X 0 ⁻¹' ({0} : Set ℝ) ∈ ae μ := by
    rw [mem_ae_iff_prob_eq_one₀ hX0_meas]
    exact hstart
  have hX0_ae : ∀ᵐ ω ∂μ, X 0 ω = 0 := by
    simpa using hX0_ae_set
  intro t
  by_cases ht : t = 0
  · subst ht
    filter_upwards [hX0_ae] with ω hω
    simp [pinValueAtZero, hω]
  · filter_upwards [] with ω
    simp [pinValueAtZero, ht]

private lemma hasAlmostSurelyContinuousPaths_pinValueAtZero
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : NNReal → Ω → ℝ}
    (hgauss : IsGaussianProcess X μ) (hstart : μ (X 0 ⁻¹' ({0} : Set ℝ)) = 1)
    (hcont : HasAlmostSurelyContinuousPaths μ X) :
    HasAlmostSurelyContinuousPaths μ (pinValueAtZero X) := by
  have hX0_meas : NullMeasurableSet (X 0 ⁻¹' ({0} : Set ℝ)) μ :=
    (hgauss.aemeasurable 0).nullMeasurableSet_preimage (measurableSet_singleton (0 : ℝ))
  have hX0_ae_set : X 0 ⁻¹' ({0} : Set ℝ) ∈ ae μ := by
    rw [mem_ae_iff_prob_eq_one₀ hX0_meas]
    exact hstart
  have hX0_ae : ∀ᵐ ω ∂μ, X 0 ω = 0 := by
    simpa using hX0_ae_set
  filter_upwards [hX0_ae, hcont] with ω hω0 hωcont
  have hpath :
      processPath (pinValueAtZero X) ω = processPath X ω := by
    funext t
    by_cases ht : t = 0
    · simp [processPath, pinValueAtZero, ht, hω0]
    · simp [processPath, pinValueAtZero, ht]
  simpa [hpath] using hωcont

private lemma tendstoUniformlyOn_pinValueAtZero
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Xapprox : ℕ → NNReal → Ω → ℝ} {X : NNReal → Ω → ℝ}
    (hgauss : IsGaussianProcess X μ) (hstart : μ (X 0 ⁻¹' ({0} : Set ℝ)) = 1)
    (hconv :
      ∀ᵐ ω ∂μ,
        TendstoUniformlyOn
          (fun n t ↦ Xapprox n t ω)
          (fun t ↦ X t ω)
          atTop
          (Set.Icc (0 : NNReal) 1)) :
    ∀ᵐ ω ∂μ,
      TendstoUniformlyOn
        (fun n t ↦ Xapprox n t ω)
        (fun t ↦ pinValueAtZero X t ω)
        atTop
        (Set.Icc (0 : NNReal) 1) := by
  have hX0_meas : NullMeasurableSet (X 0 ⁻¹' ({0} : Set ℝ)) μ :=
    (hgauss.aemeasurable 0).nullMeasurableSet_preimage (measurableSet_singleton (0 : ℝ))
  have hX0_ae_set : X 0 ⁻¹' ({0} : Set ℝ) ∈ ae μ := by
    rw [mem_ae_iff_prob_eq_one₀ hX0_meas]
    exact hstart
  have hX0_ae : ∀ᵐ ω ∂μ, X 0 ω = 0 := by
    simpa using hX0_ae_set
  filter_upwards [hX0_ae, hconv] with ω hω0 hωconv
  have hpath : (fun t ↦ pinValueAtZero X t ω) = fun t ↦ X t ω := by
    funext t
    by_cases ht : t = 0
    · simp [pinValueAtZero, ht, hω0]
    · simp [pinValueAtZero, ht]
  simpa [hpath] using hωconv

section BrownianApproximation

variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {Xapprox : ℕ → NNReal → Ω → ℝ} {Xtilde X : NNReal → Ω → ℝ}

-- Proof sketch: the almost-sure sup-norm Cauchy condition yields, for almost every `ω`, a
-- uniform limit on `[0,1]`; the continuity of each approximant makes this limit continuous.
-- The deterministic-time `L^2` convergence identifies the limit with `Xtilde` at each time, so
-- the resulting process is a continuous version of `Xtilde`, and the same pathwise limit is the
-- asserted almost-sure uniform convergence.
/-- Theorem 21.28 (1): if the Levy approximants `Xapprox n` are pathwise continuous on `[0,1]`,
converge to `Xtilde` at each deterministic time in `L^2`, and are almost surely Cauchy in the
uniform topology on `[0,1]`, then `Xtilde` admits a continuous version `X` such that `Xapprox n`
converges uniformly to `X` on `[0,1]` almost surely. -/
theorem exists_continuous_version_with_uniform_limit_of_l2_approximants
    (hXapprox_cont :
      ∀ n : ℕ, ∀ ω : Ω,
        Continuous (fun t : Set.Icc (0 : NNReal) 1 ↦ Xapprox n t ω))
    (hL2 :
      ∀ t : Set.Icc (0 : NNReal) 1,
        Tendsto
          (fun n ↦ eLpNorm (fun ω ↦ Xapprox n t ω - Xtilde t ω) (2 : ℝ≥0∞) μ)
          atTop (nhds 0))
    (hCauchy :
      ∀ᵐ ω ∂μ,
        UniformCauchySeqOn
          (fun n t ↦ Xapprox n t ω)
          atTop
          (Set.Icc (0 : NNReal) 1)) :
    ∃ X : NNReal → Ω → ℝ,
      AreModifications μ X Xtilde ∧
        HasAlmostSurelyContinuousPaths μ X ∧
        ∀ᵐ ω ∂μ,
          TendstoUniformlyOn
            (fun n t ↦ Xapprox n t ω)
            (fun t ↦ X t ω)
            atTop
            (Set.Icc (0 : NNReal) 1) := sorry

omit [IsProbabilityMeasure μ] in
private theorem isBrownianMotionStartedAt_zero_of_brownian_covariance_of_modification
    (hgauss : IsGaussianProcess Xtilde μ)
    (hmean_zero : ∀ t : NNReal, ∫ ω, Xtilde t ω ∂μ = 0)
    (hcov : ∀ s t : NNReal, cov[Xtilde s, Xtilde t; μ] = ((s ⊓ t : NNReal) : ℝ))
    (hmod : AreModifications μ X Xtilde)
    (hcont : HasAlmostSurelyContinuousPaths μ X) :
    IsBrownianMotionStartedAt μ X 0 := by
  have hgaussX : IsGaussianProcess X μ := hgauss.congr fun t ↦ (hmod t).symm
  have hmean_zero_X : ∀ t : NNReal, ∫ ω, X t ω ∂μ = 0 := fun t ↦ by
    rw [integral_congr_ae (hmod t), hmean_zero t]
  have hcovX : ∀ s t : NNReal, cov[X s, X t; μ] = ((s ⊓ t : NNReal) : ℝ) := fun s t ↦ by
    rw [covariance_congr_ae (hmod s) (hmod t), hcov s t]
  rw [isBrownianMotionStartedAt_zero_iff_isCenteredGaussianProcessWithBrownianCovariance]
  exact ⟨hgaussX, hmean_zero_X, hcovX, hcont⟩

/-- Theorem 21.28: if the Lévy approximants `Xapprox n` are pathwise continuous on `[0,1]`,
converge to `Xtilde` at each deterministic time in `L²`, and are almost surely Cauchy in the
uniform topology on `[0,1]`, while `Xtilde` is a centered Gaussian process with covariance kernel
`s ∧ t`, then there exists a Brownian motion `X` under `μ` which is a version of `Xtilde` and to
which the approximants converge uniformly on `[0,1]` almost surely. -/
theorem exists_brownianMotion_with_uniform_limit_of_l2_approximants
    (hXapprox_cont :
      ∀ n : ℕ, ∀ ω : Ω,
        Continuous (fun t : Set.Icc (0 : NNReal) 1 ↦ Xapprox n t ω))
    (hL2 :
      ∀ t : Set.Icc (0 : NNReal) 1,
        Tendsto
          (fun n ↦ eLpNorm (fun ω ↦ Xapprox n t ω - Xtilde t ω) (2 : ℝ≥0∞) μ)
          atTop (nhds 0))
    (hCauchy :
      ∀ᵐ ω ∂μ,
        UniformCauchySeqOn
          (fun n t ↦ Xapprox n t ω)
          atTop
          (Set.Icc (0 : NNReal) 1))
    (hgauss : IsGaussianProcess Xtilde μ)
    (hmean_zero : ∀ t : NNReal, ∫ ω, Xtilde t ω ∂μ = 0)
    (hcov : ∀ s t : NNReal, cov[Xtilde s, Xtilde t; μ] = ((s ⊓ t : NNReal) : ℝ)) :
    ∃ X : NNReal → Ω → ℝ,
      IsBrownianMotion μ X ∧
        AreModifications μ X Xtilde ∧
        ∀ᵐ ω ∂μ,
          TendstoUniformlyOn
            (fun n t ↦ Xapprox n t ω)
            (fun t ↦ X t ω)
            atTop
            (Set.Icc (0 : NNReal) 1) := by
  rcases
    exists_continuous_version_with_uniform_limit_of_l2_approximants
      hXapprox_cont hL2 hCauchy with
    ⟨X, hmod, hcont, hunif⟩
  have hStarted :
      IsBrownianMotionStartedAt μ X 0 :=
    isBrownianMotionStartedAt_zero_of_brownian_covariance_of_modification
      hgauss hmean_zero hcov hmod hcont
  have hStartedData :
      IsGaussianProcess X μ ∧
        (∀ t : NNReal, ∫ ω, X t ω ∂μ = 0) ∧
        (∀ s t : NNReal, cov[X s, X t; μ] = ((s ⊓ t : NNReal) : ℝ)) ∧
        HasAlmostSurelyContinuousPaths μ X :=
    (isBrownianMotionStartedAt_zero_iff_isCenteredGaussianProcessWithBrownianCovariance μ X).mp
      hStarted
  let X₀ : NNReal → Ω → ℝ := pinValueAtZero X
  have hmodZeroX : AreModifications μ X₀ X :=
    areModifications_pinValueAtZero hStartedData.1 hStarted.start
  have hgaussX₀ : IsGaussianProcess X₀ μ :=
    hStartedData.1.congr fun t ↦ (hmodZeroX t).symm
  have hmean_zero_X₀ : ∀ t : NNReal, ∫ ω, X₀ t ω ∂μ = 0 := fun t ↦ by
    rw [integral_congr_ae (hmodZeroX t), hStartedData.2.1 t]
  have hcovX₀ : ∀ s t : NNReal, cov[X₀ s, X₀ t; μ] = ((s ⊓ t : NNReal) : ℝ) := fun s t ↦ by
    rw [covariance_congr_ae (hmodZeroX s) (hmodZeroX t), hStartedData.2.2.1 s t]
  have hcontX₀ : HasAlmostSurelyContinuousPaths μ X₀ :=
    hasAlmostSurelyContinuousPaths_pinValueAtZero hStartedData.1 hStarted.start hStartedData.2.2.2
  have hBrownianX₀ : IsBrownianMotion μ X₀ := by
    rw [isBrownianMotion_iff_isCenteredGaussianProcessWithBrownianCovariance]
    refine ⟨?_, hgaussX₀, hmean_zero_X₀, hcovX₀, hcontX₀⟩
    change pinValueAtZero X 0 = 0
    funext ω
    simp [pinValueAtZero]
  have hmodZeroTilde : AreModifications μ X₀ Xtilde := fun t ↦ (hmodZeroX t).trans (hmod t)
  have hunifZero :
      ∀ᵐ ω ∂μ,
        TendstoUniformlyOn
          (fun n t ↦ Xapprox n t ω)
          (fun t ↦ X₀ t ω)
          atTop
          (Set.Icc (0 : NNReal) 1) :=
    tendstoUniformlyOn_pinValueAtZero hStartedData.1 hStarted.start hunif
  exact ⟨X₀, hBrownianX₀, hmodZeroTilde, hunifZero⟩

end BrownianApproximation

end ProbabilityTheory
