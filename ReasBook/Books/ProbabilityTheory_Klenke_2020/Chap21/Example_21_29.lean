import Mathlib
import ProbabilityTheory_Klenke_2020.Chap07.Exercise_7_3_1
import ProbabilityTheory_Klenke_2020.Chap21.Definition_21_1
import ProbabilityTheory_Klenke_2020.Chap21.Definition_21_4
import ProbabilityTheory_Klenke_2020.Chap21.Definition_21_8

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped InnerProductSpace ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

local notation "UnitIntervalTime" => Set.Icc (0 : NNReal) 1

private theorem existsUnique_paleyWienerIntegralL2LinearIsometry
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Lp ℝ 2 μ) (b : HilbertBasis ℕ ℝ L2UnitInterval)
    (hξ_indep : iIndepFun (fun n ↦ (ξ n : Ω → ℝ)) μ)
    (hξ_gaussian : ∀ n : ℕ, HasLaw (ξ n : Ω → ℝ) (gaussianReal 0 1) μ) :
    ∃! I : L2UnitInterval →ₗᵢ[ℝ] Lp ℝ 2 μ,
      ∀ f : L2UnitInterval, HasSum (fun n : ℕ ↦ (b.repr f n) • ξ n) (I f) := sorry

private noncomputable def paleyWienerIntegralL2LinearIsometryData
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Lp ℝ 2 μ) (b : HilbertBasis ℕ ℝ L2UnitInterval)
    (hξ_indep : iIndepFun (fun n ↦ (ξ n : Ω → ℝ)) μ)
    (hξ_gaussian : ∀ n : ℕ, HasLaw (ξ n : Ω → ℝ) (gaussianReal 0 1) μ) :
    L2UnitInterval →ₗᵢ[ℝ] Lp ℝ 2 μ :=
  Classical.choose <|
    (existsUnique_paleyWienerIntegralL2LinearIsometry μ ξ b hξ_indep hξ_gaussian).exists

private theorem paleyWienerIntegralL2LinearIsometryData_hasSum
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Lp ℝ 2 μ) (b : HilbertBasis ℕ ℝ L2UnitInterval)
    (hξ_indep : iIndepFun (fun n ↦ (ξ n : Ω → ℝ)) μ)
    (hξ_gaussian : ∀ n : ℕ, HasLaw (ξ n : Ω → ℝ) (gaussianReal 0 1) μ)
    (f : L2UnitInterval) :
    HasSum
      (fun n : ℕ ↦ (b.repr f n) • ξ n)
      (paleyWienerIntegralL2LinearIsometryData μ ξ b hξ_indep hξ_gaussian f) :=
  (Classical.choose_spec <|
      (existsUnique_paleyWienerIntegralL2LinearIsometry μ ξ b hξ_indep hξ_gaussian).exists) f

/-- The canonical Paley--Wiener stochastic integral map attached to a Gaussian coordinate
sequence `ξ` and a Hilbert basis `b` of `L²([0,1])`. For each integrand `f`, its value is the
`L²(μ)` limit of the Gaussian series `∑ ξₙ ⟪f, bₙ⟫`. -/
noncomputable def paleyWienerIntegralL2
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Lp ℝ 2 μ) (b : HilbertBasis ℕ ℝ L2UnitInterval)
    (hξ_indep : iIndepFun (fun n ↦ (ξ n : Ω → ℝ)) μ)
    (hξ_gaussian : ∀ n : ℕ, HasLaw (ξ n : Ω → ℝ) (gaussianReal 0 1) μ) :
    L2UnitInterval → Lp ℝ 2 μ :=
  fun f ↦ paleyWienerIntegralL2LinearIsometryData μ ξ b hξ_indep hξ_gaussian f

/-- The derived linear isometry structure on the Paley--Wiener stochastic integral map. -/
noncomputable def paleyWienerIntegralL2LinearIsometry
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Lp ℝ 2 μ) (b : HilbertBasis ℕ ℝ L2UnitInterval)
    (hξ_indep : iIndepFun (fun n ↦ (ξ n : Ω → ℝ)) μ)
    (hξ_gaussian : ∀ n : ℕ, HasLaw (ξ n : Ω → ℝ) (gaussianReal 0 1) μ) :
    L2UnitInterval →ₗᵢ[ℝ] Lp ℝ 2 μ :=
  paleyWienerIntegralL2LinearIsometryData μ ξ b hξ_indep hξ_gaussian

@[simp] theorem paleyWienerIntegralL2LinearIsometry_apply
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Lp ℝ 2 μ) (b : HilbertBasis ℕ ℝ L2UnitInterval)
    (hξ_indep : iIndepFun (fun n ↦ (ξ n : Ω → ℝ)) μ)
    (hξ_gaussian : ∀ n : ℕ, HasLaw (ξ n : Ω → ℝ) (gaussianReal 0 1) μ)
    (f : L2UnitInterval) :
    paleyWienerIntegralL2LinearIsometry μ ξ b hξ_indep hξ_gaussian f =
      paleyWienerIntegralL2 μ ξ b hξ_indep hξ_gaussian f :=
  rfl

/-- The defining Gaussian series for `paleyWienerIntegralL2` converges in `L²(μ)`. -/
theorem paleyWienerIntegralL2_hasSum
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Lp ℝ 2 μ) (b : HilbertBasis ℕ ℝ L2UnitInterval)
    (hξ_indep : iIndepFun (fun n ↦ (ξ n : Ω → ℝ)) μ)
    (hξ_gaussian : ∀ n : ℕ, HasLaw (ξ n : Ω → ℝ) (gaussianReal 0 1) μ)
    (f : L2UnitInterval) :
    HasSum
      (fun n : ℕ ↦ (b.repr f n) • ξ n)
      (paleyWienerIntegralL2 μ ξ b hξ_indep hξ_gaussian f) :=
  paleyWienerIntegralL2LinearIsometryData_hasSum μ ξ b hξ_indep hξ_gaussian f

private theorem memLp_unitIntervalCutoff
    (t : UnitIntervalTime) (f : L2UnitInterval) :
    MemLp (Set.indicator (Set.Icc (0 : ℝ) (t : ℝ)) fun x ↦ f x) 2 unitIntervalMeasure :=
  (Lp.memLp f).indicator measurableSet_Icc

/-- The deterministic cutoff operator `f ↦ f 1_[0,t]` on `L²([0,1])`. -/
noncomputable def unitIntervalCutoff (t : UnitIntervalTime) :
    L2UnitInterval →L[ℝ] L2UnitInterval where
  toLinearMap :=
    { toFun := fun f ↦
        (memLp_unitIntervalCutoff t f).toLp
          (Set.indicator (Set.Icc (0 : ℝ) (t : ℝ)) fun x ↦ f x)
      map_add' := by
        sorry
      map_smul' := by
        sorry }
  cont := by
    sorry

/-- Coercing `unitIntervalCutoff t f` to an actual function recovers the pointwise product
`f 1_[0,t]` almost everywhere on `[0,1]`. -/
theorem unitIntervalCutoff_coeFn
    (t : UnitIntervalTime) (f : L2UnitInterval) :
    ((unitIntervalCutoff t f : L2UnitInterval) : ℝ → ℝ) =ᵐ[unitIntervalMeasure]
      Set.indicator (Set.Icc (0 : ℝ) (t : ℝ)) fun x ↦ f x :=
  MemLp.coeFn_toLp (memLp_unitIntervalCutoff t f)

/-- The stochastic-integral process `t ↦ I(f 1_[0,t])` on the unit interval. -/
noncomputable def paleyWienerIntegralProcess
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Lp ℝ 2 μ) (b : HilbertBasis ℕ ℝ L2UnitInterval)
    (hξ_indep : iIndepFun (fun n ↦ (ξ n : Ω → ℝ)) μ)
    (hξ_gaussian : ∀ n : ℕ, HasLaw (ξ n : Ω → ℝ) (gaussianReal 0 1) μ)
    (f : L2UnitInterval) :
    UnitIntervalTime → Ω → ℝ :=
  fun t ↦ paleyWienerIntegralL2 μ ξ b hξ_indep hξ_gaussian (unitIntervalCutoff t f)

-- Proof sketch: each time coordinate `t ↦ I(f 1_[0,t])` is a deterministic linear image of the
-- Gaussian coordinate family `(ξₙ)ₙ`, so every finite-dimensional law is Gaussian.
/-- For each deterministic integrand `f ∈ L²([0,1])`, the Paley--Wiener stochastic-integral
process `t ↦ I(f 1_[0,t])` is a Gaussian process on `[0,1]`. This is the canonical owner
abstraction for the source-facing process before imposing continuity. -/
theorem paleyWienerIntegralProcess_isGaussianProcess
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Lp ℝ 2 μ) (b : HilbertBasis ℕ ℝ L2UnitInterval)
    (hξ_indep : iIndepFun (fun n ↦ (ξ n : Ω → ℝ)) μ)
    (hξ_gaussian : ∀ n : ℕ, HasLaw (ξ n : Ω → ℝ) (gaussianReal 0 1) μ)
    (f : L2UnitInterval) :
    IsGaussianProcess (paleyWienerIntegralProcess μ ξ b hξ_indep hξ_gaussian f) μ := sorry

-- Proof sketch: each marginal `I(f 1_[0,t])` is a centered Gaussian linear combination of the
-- centered coordinates `ξₙ`, so its expectation vanishes.
/-- Every time marginal of the Paley--Wiener stochastic-integral process is centered. -/
theorem paleyWienerIntegralProcess_mean_zero
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Lp ℝ 2 μ) (b : HilbertBasis ℕ ℝ L2UnitInterval)
    (hξ_indep : iIndepFun (fun n ↦ (ξ n : Ω → ℝ)) μ)
    (hξ_gaussian : ∀ n : ℕ, HasLaw (ξ n : Ω → ℝ) (gaussianReal 0 1) μ)
    (f : L2UnitInterval) (t : UnitIntervalTime) :
    ∫ ω, paleyWienerIntegralProcess μ ξ b hξ_indep hξ_gaussian f t ω ∂μ = 0 := sorry

-- Proof sketch: approximate `f 1_[0,t]` by the finite partial sums of its Hilbert-basis
-- expansion. The corresponding finite Paley--Wiener sums have continuous paths in `t`, converge in
-- `L²(μ)` at each deterministic time, and are almost surely uniformly Cauchy on `[0,1]`, so the
-- continuity criterion of Theorem 21.28 yields a continuous version.
/-- The Paley--Wiener stochastic-integral process admits a version with almost surely continuous
sample paths on `[0,1]`. -/
theorem paleyWienerIntegralProcess_exists_continuous_version
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Lp ℝ 2 μ) (b : HilbertBasis ℕ ℝ L2UnitInterval)
    (hξ_indep : iIndepFun (fun n ↦ (ξ n : Ω → ℝ)) μ)
    (hξ_gaussian : ∀ n : ℕ, HasLaw (ξ n : Ω → ℝ) (gaussianReal 0 1) μ)
    (f : L2UnitInterval) :
    ∃ X : UnitIntervalTime → Ω → ℝ,
      AreModifications μ X (paleyWienerIntegralProcess μ ξ b hξ_indep hξ_gaussian f) ∧
        HasAlmostSurelyContinuousPaths μ X := sorry

/-- The unit-interval process obtained from the Paley--Wiener operator by integrating the constant
integrand `1` over `[0,t]`. The Brownian-version theorem below upgrades this source-facing process
to the chapter's canonical owner `IsBrownianMotion`. -/
noncomputable def paleyWienerBrownianMotion
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Lp ℝ 2 μ) (b : HilbertBasis ℕ ℝ L2UnitInterval)
    (hξ_indep : iIndepFun (fun n ↦ (ξ n : Ω → ℝ)) μ)
    (hξ_gaussian : ∀ n : ℕ, HasLaw (ξ n : Ω → ℝ) (gaussianReal 0 1) μ) :
    UnitIntervalTime → Ω → ℝ :=
  paleyWienerIntegralProcess μ ξ b hξ_indep hξ_gaussian
    (indicatorConstLp 2 MeasurableSet.univ (by simp [unitIntervalMeasure]) (1 : ℝ))

-- Proof sketch: this is the preceding Gaussian-process result specialized to the constant
-- integrand `1`.
/-- The Paley--Wiener unit-interval process `t ↦ I(1_[0,t])` is Gaussian. -/
theorem paleyWienerBrownianMotion_isGaussianProcess
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Lp ℝ 2 μ) (b : HilbertBasis ℕ ℝ L2UnitInterval)
    (hξ_indep : iIndepFun (fun n ↦ (ξ n : Ω → ℝ)) μ)
    (hξ_gaussian : ∀ n : ℕ, HasLaw (ξ n : Ω → ℝ) (gaussianReal 0 1) μ) :
    IsGaussianProcess (paleyWienerBrownianMotion μ ξ b hξ_indep hξ_gaussian) μ := by
  simpa [paleyWienerBrownianMotion] using
    paleyWienerIntegralProcess_isGaussianProcess μ ξ b hξ_indep hξ_gaussian
      (indicatorConstLp 2 MeasurableSet.univ (by simp [unitIntervalMeasure]) (1 : ℝ))

-- Proof sketch: this is the centeredness result for the Paley--Wiener integral process evaluated
-- at the constant integrand `1`.
/-- Every time marginal of the Paley--Wiener unit-interval Brownian process is centered. -/
theorem paleyWienerBrownianMotion_mean_zero
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Lp ℝ 2 μ) (b : HilbertBasis ℕ ℝ L2UnitInterval)
    (hξ_indep : iIndepFun (fun n ↦ (ξ n : Ω → ℝ)) μ)
    (hξ_gaussian : ∀ n : ℕ, HasLaw (ξ n : Ω → ℝ) (gaussianReal 0 1) μ)
    (t : UnitIntervalTime) :
    ∫ ω, paleyWienerBrownianMotion μ ξ b hξ_indep hξ_gaussian t ω ∂μ = 0 := by
  simpa [paleyWienerBrownianMotion] using
    paleyWienerIntegralProcess_mean_zero μ ξ b hξ_indep hξ_gaussian
      (indicatorConstLp 2 MeasurableSet.univ (by simp [unitIntervalMeasure]) (1 : ℝ)) t

-- Proof sketch: combine the Gaussianity, centeredness, and covariance identity for the
-- unit-interval process `t ↦ I(1_[0,t])` with the continuous-version theorem above, then apply the
-- Brownian characterization of Chapter 21 to obtain a Brownian motion on `NNReal` whose
-- restriction to `[0,1]` is a version of the Paley--Wiener process.
/-- The Paley--Wiener unit-interval process `t ↦ I(1_[0,t])` admits a Brownian-motion version in
the chapter's canonical sense. -/
theorem paleyWienerBrownianMotion_exists_brownianMotion
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Lp ℝ 2 μ) (b : HilbertBasis ℕ ℝ L2UnitInterval)
    (hξ_indep : iIndepFun (fun n ↦ (ξ n : Ω → ℝ)) μ)
    (hξ_gaussian : ∀ n : ℕ, HasLaw (ξ n : Ω → ℝ) (gaussianReal 0 1) μ) :
    ∃ B : NNReal → Ω → ℝ,
      IsBrownianMotion μ B ∧
        AreModifications μ (fun t : UnitIntervalTime ↦ B t)
          (paleyWienerBrownianMotion μ ξ b hξ_indep hξ_gaussian) := sorry

-- Proof sketch: show that the standard-normal assumptions imply that the coordinates `ξ n` form
-- an orthonormal sequence in `L²(μ)`. Then identify `paleyWienerIntegralL2 μ ξ b` with the map
-- sending the coefficient sequence `b.repr f` to the corresponding Gaussian series in `L²(μ)`,
-- and apply Parseval's identity for the Hilbert basis `b`.
/-- Example 21.29: the Paley--Wiener map `f ↦ I(f)` from `L²([0,1])` to `L²(μ)` is an isometry
when the coordinates `ξₙ` are independent standard Gaussian random variables. -/
theorem paleyWienerIntegralL2_isometry
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Lp ℝ 2 μ) (b : HilbertBasis ℕ ℝ L2UnitInterval)
    (hξ_indep : iIndepFun (fun n ↦ (ξ n : Ω → ℝ)) μ)
    (hξ_gaussian : ∀ n : ℕ, HasLaw (ξ n : Ω → ℝ) (gaussianReal 0 1) μ) :
    Isometry (paleyWienerIntegralL2 μ ξ b hξ_indep hξ_gaussian) := by
  simpa [paleyWienerIntegralL2] using
    (paleyWienerIntegralL2LinearIsometry μ ξ b hξ_indep hξ_gaussian).isometry

-- Proof sketch: expand both Gaussian series, use bilinearity of covariance, and kill the
-- off-diagonal terms by independence and centering of the standard-normal coordinates. The
-- remaining diagonal sum is exactly the Hilbert-space inner product `inner ℝ f g`.
/-- The covariance of two Paley--Wiener stochastic integrals is the `L²([0,1])` inner product of
their integrands. -/
theorem paleyWienerIntegralL2_covariance_eq
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Lp ℝ 2 μ) (b : HilbertBasis ℕ ℝ L2UnitInterval)
    (hξ_indep : iIndepFun (fun n ↦ (ξ n : Ω → ℝ)) μ)
    (hξ_gaussian : ∀ n : ℕ, HasLaw (ξ n : Ω → ℝ) (gaussianReal 0 1) μ)
    (f g : L2UnitInterval) :
    cov[(paleyWienerIntegralL2 μ ξ b hξ_indep hξ_gaussian f : Ω → ℝ),
      (paleyWienerIntegralL2 μ ξ b hξ_indep hξ_gaussian g : Ω → ℝ); μ] =
      inner ℝ f g := sorry

-- Proof sketch: specialize `paleyWienerIntegralL2_covariance_eq` to `f = g`. For a centered
-- Gaussian random variable, covariance with itself is the variance, so the result is Parseval's
-- identity in the form `Var[I(f)] = ‖f‖²`.
/-- The variance of the Paley--Wiener stochastic integral is the squared `L²([0,1])` norm of the
integrand. -/
theorem paleyWienerIntegralL2_variance_eq
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Lp ℝ 2 μ) (b : HilbertBasis ℕ ℝ L2UnitInterval)
    (hξ_indep : iIndepFun (fun n ↦ (ξ n : Ω → ℝ)) μ)
    (hξ_gaussian : ∀ n : ℕ, HasLaw (ξ n : Ω → ℝ) (gaussianReal 0 1) μ)
    (f : L2UnitInterval) :
    Var[(paleyWienerIntegralL2 μ ξ b hξ_indep hξ_gaussian f : Ω → ℝ); μ] = ‖f‖ ^ (2 : ℕ) := sorry

-- Proof sketch: apply `paleyWienerIntegralL2_covariance_eq` to the cutoff integrands
-- `f 1_[0,s]` and `g 1_[0,t]`.
/-- The covariance of two truncated Paley--Wiener stochastic integrals is the inner product of
their cutoff integrands. -/
theorem paleyWienerIntegralProcess_covariance_eq
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Lp ℝ 2 μ) (b : HilbertBasis ℕ ℝ L2UnitInterval)
    (hξ_indep : iIndepFun (fun n ↦ (ξ n : Ω → ℝ)) μ)
    (hξ_gaussian : ∀ n : ℕ, HasLaw (ξ n : Ω → ℝ) (gaussianReal 0 1) μ)
    (f g : L2UnitInterval) (s t : UnitIntervalTime) :
    cov[paleyWienerIntegralProcess μ ξ b hξ_indep hξ_gaussian f s,
      paleyWienerIntegralProcess μ ξ b hξ_indep hξ_gaussian g t; μ] =
      inner ℝ (unitIntervalCutoff s f) (unitIntervalCutoff t g) := sorry

-- Proof sketch: specialize `paleyWienerIntegralProcess_covariance_eq` to the constant integrand
-- `1`, and identify the inner product of two interval indicators with the overlap length
-- `min(s,t)`.
/-- The Paley--Wiener process `t ↦ I(1_[0,t])` has Brownian covariance on `[0,1]`. -/
theorem paleyWienerBrownianMotion_covariance_eq
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Lp ℝ 2 μ) (b : HilbertBasis ℕ ℝ L2UnitInterval)
    (hξ_indep : iIndepFun (fun n ↦ (ξ n : Ω → ℝ)) μ)
    (hξ_gaussian : ∀ n : ℕ, HasLaw (ξ n : Ω → ℝ) (gaussianReal 0 1) μ)
    (s t : UnitIntervalTime) :
    cov[paleyWienerBrownianMotion μ ξ b hξ_indep hξ_gaussian s,
      paleyWienerBrownianMotion μ ξ b hξ_indep hξ_gaussian t; μ] =
      ((s : NNReal) ⊓ (t : NNReal) : ℝ) := sorry

end ProbabilityTheory
