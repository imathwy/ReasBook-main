import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_7_3_1 (from Items/Chap07) -/
open MeasureTheory
open scoped InnerProductSpace

noncomputable section

/-- Lebesgue measure restricted to the unit interval `[0,1]`. -/
def unitIntervalMeasure : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

/-- The real Hilbert space `L²([0,1], λ)`. -/
abbrev L2UnitInterval :=
  ℝ →₂[unitIntervalMeasure] ℝ

/-- The source-facing coefficient space for real Fourier series on `[0,1]`: sine coefficients are
indexed by positive frequencies `n : ℕ+`, while cosine coefficients are indexed by `ℕ` and use
`b 0` for the normalized constant mode. -/
abbrev FourierCoefficients :=
  ℓ²(ℕ+, ℝ) × ℓ²(ℕ, ℝ)

/-- The sine function `Sₙ(x) = √2 sin (2π n x)` on the unit interval. -/
def fourierSineFun (n : ℕ) : ℝ → ℝ :=
  fun x ↦ Real.sqrt 2 * Real.sin (2 * Real.pi * n * x)

/-- The cosine function `Cₙ(x) = √2 cos (2π n x)` on the unit interval. -/
def fourierCosineFun (n : ℕ) : ℝ → ℝ :=
  fun x ↦ Real.sqrt 2 * Real.cos (2 * Real.pi * n * x)

/-- The normalized constant Fourier mode on `[0,1]`. -/
def fourierConstantFun : ℝ → ℝ :=
  fun _ ↦ 1

-- Proof sketch: the trigonometric function `fourierSineFun n` is continuous, hence strongly
-- measurable, and it is bounded on the compact interval `[0,1]`; finite measure then gives `L²`
-- integrability on `unitIntervalMeasure`.
/-- Each sine Fourier mode belongs to `L²([0,1], λ)`. -/
theorem fourierSineFun_memLp (n : ℕ) :
    MemLp (fourierSineFun n) 2 unitIntervalMeasure := sorry

-- Proof sketch: the trigonometric function `fourierCosineFun n` is continuous and bounded on the
-- compact interval `[0,1]`, so it is square-integrable for the restricted Lebesgue measure.
/-- Each cosine Fourier mode belongs to `L²([0,1], λ)`. -/
theorem fourierCosineFun_memLp (n : ℕ) :
    MemLp (fourierCosineFun n) 2 unitIntervalMeasure := sorry

-- Proof sketch: the constant function `1` is measurable and bounded on a finite-measure space,
-- so its square is integrable on `[0,1]`.
/-- The constant Fourier mode belongs to `L²([0,1], λ)`. -/
theorem fourierConstantFun_memLp :
    MemLp fourierConstantFun 2 unitIntervalMeasure := sorry

/-- The `L²` class of the sine mode `Sₙ`. -/
def fourierSine (n : ℕ) : L2UnitInterval :=
  (fourierSineFun_memLp n).toLp (fourierSineFun n)

/-- The `L²` class of the cosine mode `Cₙ`. -/
def fourierCosine (n : ℕ) : L2UnitInterval :=
  (fourierCosineFun_memLp n).toLp (fourierCosineFun n)

/-- The normalized constant mode in `L²([0,1], λ)`. -/
def fourierConstant : L2UnitInterval :=
  fourierConstantFun_memLp.toLp fourierConstantFun

/-- The textbook constant mode satisfies `C₀ = √2 · 1`. -/
theorem fourierCosine_zero_eq_smul_fourierConstant :
    fourierCosine 0 = Real.sqrt 2 • fourierConstant := sorry

/-- Indices for the trigonometric family `C₀, Sₙ, Cₙ` with `n ≥ 1`. -/
inductive FourierTrigonometricIndex
  | constant
  | sine (n : ℕ)
  | cosine (n : ℕ)

/-- The textbook trigonometric family `C₀, Sₙ, Cₙ` in `L²([0,1], λ)`, indexed so that `sine n`
and `cosine n` correspond to the positive frequencies `n + 1`. -/
def fourierTrigonometricSystem : FourierTrigonometricIndex → L2UnitInterval
  | .constant => fourierCosine 0
  | .sine n => fourierSine (n + 1)
  | .cosine n => fourierCosine (n + 1)

/-- The normalized orthonormal trigonometric system `1, Sₙ, Cₙ` in `L²([0,1], λ)`, indexed so
that `sine n` and `cosine n` correspond to the positive frequencies `n + 1`. -/
def normalizedFourierTrigonometricSystem : FourierTrigonometricIndex → L2UnitInterval
  | .constant => fourierConstant
  | .sine n => fourierSine (n + 1)
  | .cosine n => fourierCosine (n + 1)

/-- The positive-frequency Fourier summand determined by sine coefficients `a` and cosine
coefficients `b`, where `b 0` is reserved for the constant term. -/
def fourierSeriesSummand (coeffs : FourierCoefficients) (n : ℕ+) : L2UnitInterval :=
  coeffs.1 n • fourierSine n + coeffs.2 n • fourierCosine n

/-- The real Fourier series on `[0,1]` attached to the coefficient vector
`coeffs = (a, b) : ℓ²(ℕ+, ℝ) × ℓ²(ℕ, ℝ)`, where `a n` is the coefficient of `Sₙ` for the
positive frequency `n : ℕ+`, and `b 0` is the coefficient of the normalized constant mode `1`
(equivalently, `(b 0 / Real.sqrt 2)` is the coefficient of `C₀`). -/
def fourierSeries (coeffs : FourierCoefficients) : L2UnitInterval :=
  coeffs.2 0 • fourierConstant + ∑' n : ℕ+, fourierSeriesSummand coeffs n

/-- The linear Fourier-synthesis map from square-summable real coefficients to `L²([0,1], λ)`. -/
def fourierSeriesLinearMap : FourierCoefficients →ₗ[ℝ] L2UnitInterval where
  toFun := fourierSeries
  map_add' := sorry
  map_smul' := sorry

/-- Exercise 7.3.1: the source-facing space `W` of real Fourier series on `[0,1]`. -/
def W : Submodule ℝ L2UnitInterval :=
  LinearMap.range fourierSeriesLinearMap

/-- Every real Fourier series belongs to the space `W`. -/
theorem fourierSeries_mem_W (coeffs : FourierCoefficients) :
    fourierSeries coeffs ∈ W :=
  LinearMap.mem_range_self fourierSeriesLinearMap coeffs

/-- Exercise 7.3.1: the Fourier-series space `W` equals `L²([0,1], λ)`. -/
theorem W_eq_top : W = ⊤ := sorry

/-- Exercise 7.3.1: the Fourier-series space `W` is closed in `L²([0,1], λ)`. -/
theorem W_isClosed : IsClosed (W : Set L2UnitInterval) := by
  simp [W_eq_top]

-- Proof sketch: compute the inner products by integrating products of sines and cosines on
-- `[0,1]`, then use the standard trigonometric orthogonality identities and the chosen
-- normalization constants.
/-- The normalized system `1, Sₙ, Cₙ` with `n ≥ 1` is orthonormal in `L²([0,1], λ)`. -/
theorem normalizedFourierTrigonometricSystem_orthonormal :
    Orthonormal ℝ normalizedFourierTrigonometricSystem := sorry

-- Proof sketch: the closed linear span of the normalized trigonometric system contains the image
-- of all trigonometric polynomials, which are dense in `L²([0,1], λ)`.
/-- The normalized trigonometric system spans `L²([0,1], λ)` densely. -/
theorem normalizedFourierTrigonometricSystem_dense_span :
    (Submodule.span ℝ (Set.range normalizedFourierTrigonometricSystem)).topologicalClosure = ⊤ :=
  sorry

/-- The canonical Hilbert-basis owner for the normalized real trigonometric system on `[0,1]`. -/
def realFourierHilbertBasis : HilbertBasis FourierTrigonometricIndex ℝ L2UnitInterval :=
  HilbertBasis.mk normalizedFourierTrigonometricSystem_orthonormal
    (le_of_eq normalizedFourierTrigonometricSystem_dense_span.symm)

@[simp] theorem coe_realFourierHilbertBasis :
    ⇑realFourierHilbertBasis = normalizedFourierTrigonometricSystem := by
  simp [realFourierHilbertBasis]

/-- The Hilbert-basis Fourier coefficient of `f` is the inner product with the corresponding
normalized trigonometric mode. -/
theorem realFourierHilbertBasis_repr_apply
    (f : L2UnitInterval) (i : FourierTrigonometricIndex) :
    realFourierHilbertBasis.repr f i = ⟪normalizedFourierTrigonometricSystem i, f⟫_ℝ := by
  simpa [realFourierHilbertBasis] using
    HilbertBasis.repr_apply_apply realFourierHilbertBasis f i

/-- The normalized trigonometric expansion of an `L²([0,1], λ)` function converges to that
function in the Hilbert-space sense. -/
theorem hasSum_normalizedFourierExpansion (f : L2UnitInterval) :
    HasSum
      (fun i : FourierTrigonometricIndex ↦
        realFourierHilbertBasis.repr f i • normalizedFourierTrigonometricSystem i)
      f := by
  simpa [realFourierHilbertBasis] using HilbertBasis.hasSum_repr realFourierHilbertBasis f

/-- The textbook system `C₀, Sₙ, Cₙ` with `n ≥ 1` is pairwise orthogonal in `L²([0,1], λ)`. -/
theorem fourierTrigonometricSystem_pairwise_orthogonal :
    Pairwise fun i j : FourierTrigonometricIndex ↦
      ⟪fourierTrigonometricSystem i, fourierTrigonometricSystem j⟫_ℝ = 0 :=
  sorry

-- Proof sketch: use orthogonality of the trigonometric system together with square-summability
-- of the coefficients to obtain Cauchy partial sums in the Hilbert space `L²([0,1], λ)`.
/-- The nonconstant part of a real Fourier series converges in `L²([0,1], λ)`. -/
theorem fourierSeries_summable (coeffs : FourierCoefficients) :
    Summable (fourierSeriesSummand coeffs) := sorry

-- Proof sketch: first show existence of a Fourier expansion by density of step functions, then
-- prove uniqueness from orthogonality of the trigonometric system. Equivalently,
-- this is the source-facing coefficient statement obtained from the canonical Hilbert basis
-- `realFourierHilbertBasis`, with sine coefficients indexed by `ℕ+`.
/-- Exercise 7.3.1: every real `L²` function on `[0,1]` has a unique Fourier expansion with
square-summable sine coefficients `a : ℓ²(ℕ+, ℝ)` and cosine coefficients `b : ℓ²(ℕ, ℝ)`, where
`b 0` is the coefficient of the normalized constant mode `1` (equivalently,
`(b 0 / Real.sqrt 2)` is the coefficient of `C₀`). -/
theorem existsUnique_fourierSeries_coefficients (f : L2UnitInterval) :
    ∃! coeffs : FourierCoefficients, fourierSeries coeffs = f := sorry

-- Proof sketch: expand `f` in the orthogonal trigonometric system, apply the Pythagorean theorem
-- in the Hilbert space `L²([0,1], λ)`, and identify the squared norm of the coefficient vector.
/-- Parseval's identity for the real Fourier expansion on `[0,1]`. -/
theorem fourierSeries_parseval {f : L2UnitInterval} {coeffs : FourierCoefficients}
    (hf : fourierSeries coeffs = f) :
    ‖f‖ ^ 2 = coeffs.2 0 ^ 2 + ∑' n : ℕ+, (coeffs.1 n ^ 2 + coeffs.2 n ^ 2) := sorry

/-! ### Theorem_7_3 (from Items/Chap07) -/
open Filter MeasureTheory
open scoped ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {p : ℝ≥0∞}

-- Proof sketch: interpret `fₙ` as elements of `MeasureTheory.Lp ℝ p μ` via `MemLp.toLp`,
-- use completeness of `Lp` for `1 ≤ p` to get the Cauchy-criterion direction, and express the
-- limit via the chapter's owner notion `TendstoInLp`.
/-- Theorem 7.3 (1): for `1 ≤ p ≤ ∞`, a sequence of real-valued `L^p(μ)` functions converges in
`L^p(μ)` in the sense of Definition 7.2 if and only if the associated sequence in the canonical
metric space `Lp ℝ p μ` is Cauchy. -/
theorem lp_sequence_has_lp_limit_iff_cauchy
    [Fact (1 ≤ p)] (fSeq : ℕ → Ω → ℝ) (h_memLp : ∀ n, MemLp (fSeq n) p μ) :
    (∃ f : Ω → ℝ, TendstoInLp p μ fSeq f) ↔
      CauchySeq (fun n ↦ (h_memLp n).toLp (fSeq n)) := by
  constructor
  · rintro ⟨f, h_tendsto⟩
    have h_toLp :
        (fun n ↦ (h_tendsto.memLpSeq n).toLp (fSeq n)) =
          fun n ↦ (h_memLp n).toLp (fSeq n) := by
      funext n
      exact MemLp.toLp_congr (h_tendsto.memLpSeq n) (h_memLp n) Filter.EventuallyEq.rfl
    simpa [h_toLp] using h_tendsto.tendsto_toLp.cauchySeq
  · intro h_cauchy
    obtain ⟨F, hF⟩ := cauchySeq_tendsto_of_complete h_cauchy
    exact ⟨(F : Ω → ℝ), ⟨h_memLp, Lp.memLp F, by simpa using hF⟩⟩

-- Proof sketch: combine the previous Cauchy criterion with the general Vitali owner theorem
-- `tendstoInMeasure_iff_tendsto_Lp`, whose source-facing hypotheses are convergence in measure,
-- `UnifIntegrable`, and `UnifTight`.
/-- Theorem 7.3 (2): if `p < ∞`, then the following are equivalent for a real-valued `L^p(μ)`
sequence `fSeq`: (i) `fSeq` converges in `L^p(μ)`, (ii) `fSeq` is Cauchy in `L^p(μ)`, and (iii)
`fSeq` converges in `μ`-measure to an `L^p(μ)` limit and is uniformly integrable and uniformly
tight in the canonical measure-theoretic senses `UnifIntegrable` and `UnifTight`. -/
theorem lp_sequence_tfae_has_lp_limit_cauchy_uniformly_integrable_power_limit_in_measure
    [Fact (1 ≤ p)] (fSeq : ℕ → Ω → ℝ)
    (h_memLp : ∀ n, MemLp (fSeq n) p μ) (hp_top : p ≠ ∞) :
    List.TFAE
      [ ∃ f : Ω → ℝ, TendstoInLp p μ fSeq f
      , CauchySeq (fun n ↦ (h_memLp n).toLp (fSeq n))
      , ∃ f : Ω → ℝ, MemLp f p μ ∧ TendstoInMeasure μ fSeq atTop f ∧
          UnifIntegrable fSeq p μ ∧ UnifTight fSeq p μ
      ] := by
  -- Source/core/bridge triage:
  -- * source-facing: `TendstoInLp p μ fSeq f`
  -- * core/canonical owner: `MeasureTheory.Lp ℝ p μ`
  -- * bridge/view: `tendstoInMeasure_iff_tendsto_Lp`
  tfae_have 1 ↔ 2 := lp_sequence_has_lp_limit_iff_cauchy fSeq h_memLp
  tfae_have 1 → 3 := by
    rintro ⟨f, h_tendsto⟩
    exact ⟨f, h_tendsto.memLp, (tendstoInMeasure_iff_tendsto_Lp ‹Fact (1 ≤ p)›.out hp_top
      h_tendsto.memLpSeq h_tendsto.memLp).2 h_tendsto.tendsto_eLpNorm⟩
  tfae_have 3 → 1 := by
    rintro ⟨f, hf_memLp, h_meas, h_ui, h_tight⟩
    exact ⟨f, (tendstoInLp_iff_tendsto_eLpNorm).2
      ⟨h_memLp, hf_memLp, (tendstoInMeasure_iff_tendsto_Lp ‹Fact (1 ≤ p)›.out hp_top
        h_memLp hf_memLp).1 ⟨h_meas, h_ui, h_tight⟩⟩⟩
  tfae_finish

-- Proof sketch: each `L^p` convergence hypothesis implies convergence in measure by
-- `tendstoInMeasure_of_tendsto_eLpNorm`; the measure-limit is unique up to almost-everywhere
-- equality by `tendstoInMeasure_ae_unique`.
/-- Theorem 7.3 (3): if a real-valued `L^p(μ)` sequence converges in `L^p(μ)` to `f` and in
`μ`-measure to `g`, then the two limits agree almost everywhere. In particular, the limits in
clauses (i) and (iii) of Theorem 7.3 (2) coincide `μ`-a.e. -/
theorem ae_eq_of_tendstoInLp_and_tendstoInMeasure
    [Fact (1 ≤ p)] {fSeq : ℕ → Ω → ℝ} {f g : Ω → ℝ}
    (h_tendsto_lp : TendstoInLp p μ fSeq f) (h_tendsto_measure : TendstoInMeasure μ fSeq atTop g) :
    f =ᵐ[μ] g := by
  have hp_ne_zero : p ≠ 0 := (lt_of_lt_of_le zero_lt_one ‹Fact (1 ≤ p)›.out).ne'
  have h_tendsto_measure_lp : TendstoInMeasure μ fSeq atTop f :=
    tendstoInMeasure_of_tendsto_eLpNorm hp_ne_zero
      (fun n ↦ (h_tendsto_lp.memLpSeq n).aestronglyMeasurable)
      h_tendsto_lp.memLp.aestronglyMeasurable h_tendsto_lp.tendsto_eLpNorm
  exact tendstoInMeasure_ae_unique h_tendsto_measure_lp h_tendsto_measure

/-- Companion uniqueness statement: two `L^p` limits of the same sequence agree almost
everywhere. -/
theorem ae_eq_of_tendstoInLp_of_tendstoInLp
    [Fact (1 ≤ p)] {fSeq : ℕ → Ω → ℝ} {f g : Ω → ℝ}
    (h_tendsto_f : TendstoInLp p μ fSeq f) (h_tendsto_g : TendstoInLp p μ fSeq g) :
    f =ᵐ[μ] g := by
  have hp_ne_zero : p ≠ 0 := (lt_of_lt_of_le zero_lt_one ‹Fact (1 ≤ p)›.out).ne'
  exact ae_eq_of_tendstoInLp_and_tendstoInMeasure h_tendsto_f
    (tendstoInMeasure_of_tendsto_eLpNorm hp_ne_zero
      (fun n ↦ (h_tendsto_g.memLpSeq n).aestronglyMeasurable)
      h_tendsto_g.memLp.aestronglyMeasurable h_tendsto_g.tendsto_eLpNorm)
