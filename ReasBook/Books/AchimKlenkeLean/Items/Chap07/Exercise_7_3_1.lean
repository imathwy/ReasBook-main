import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
