import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap03.Exercise_3_1_1

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory unitInterval

noncomputable section

/-- The centered uniform law on the interval `[-a/2, a/2]`, interpreted for positive `a`. -/
noncomputable def symmetricUniformMeasure (a : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 / a) • volume.restrict (Set.Icc (-a / 2) (a / 2))

/-- The centered triangular law obtained by convolving the uniform law on `[-a/2, a/2]` with
itself. -/
noncomputable def symmetricTriangularMeasure (a : ℝ) : Measure ℝ :=
  symmetricUniformMeasure a ∗ symmetricUniformMeasure a

/-- The probability measure with density
`(1 / π) * (1 - cos (a x)) / (a x^2)`. -/
noncomputable def triangularCharacteristicMeasure (a : ℝ) : Measure ℝ :=
  volume.withDensity
    (fun x ↦ ENNReal.ofReal (((1 / Real.pi) * (1 - Real.cos (a * x))) / (a * x ^ 2)))

/-- The centered two-sided exponential law obtained as the law of `X - Y` for independent
`Exp(θ)` random variables `X` and `Y`. -/
noncomputable def twoSidedExponentialMeasure (θ : ℝ) : Measure ℝ :=
  ((expMeasure θ).prod (expMeasure θ)).map fun xy ↦ xy.1 - xy.2

/- Theorem 15.12: Item (i). The normal law is the canonical Gaussian
characteristic-function formula `charFun_gaussianReal`. -/
recall charFun_gaussianReal

-- Proof sketch: expand the characteristic function of the normalized restriction of Lebesgue
-- measure to `[-a/2, a/2]` and identify the resulting integral with the sinc kernel.
/-- Theorem 15.12 (1): Item (ii). The centered uniform law on `[-a/2, a/2]` has characteristic
function `t ↦ sinc (a t / 2)`. -/
theorem charFun_symmetricUniformMeasure (a : ℝ) (ha : 0 < a) (t : ℝ) :
    charFun (symmetricUniformMeasure a) t = Real.sinc (a * t / 2) := sorry

-- Proof sketch: unfold `symmetricTriangularMeasure`, then use multiplicativity of
-- characteristic functions under convolution and the uniform formula from item (ii).
/-- Theorem 15.12 (2): Item (iii). The centered triangular law has characteristic function
`(sinc (a t / 2))^2`. -/
theorem charFun_symmetricTriangularMeasure (a : ℝ) (ha : 0 < a) (t : ℝ) :
    charFun (symmetricTriangularMeasure a) t =
      (Real.sinc (a * t / 2) : ℂ) ^ 2 := sorry

-- Proof sketch: this is the explicit characteristic-function computation from Theorem 15.12,
-- identifying the Fourier transform of `triangularCharacteristicMeasure a` with the tent
-- function.
/-- Theorem 15.12: the measure with density
`(1 / π) * (1 - cos (a x)) / (a x^2)` has characteristic function
`t ↦ max (1 - |t| / a) 0`. -/
theorem charFun_triangularCharacteristicMeasure (a : ℝ) (ha : 0 < a) (t : ℝ) :
    charFun (triangularCharacteristicMeasure a) t =
      ((max (1 - |t| / a) 0 : ℝ) : ℂ) := sorry

/- The OCR-backed source inserts an item (iv) labeled `N.N.` between the triangle and Gamma
entries, but the supplied table image is not legible enough to recover a faithful Lean statement.
The declarations below formalize every other explicit formula that is visible in the proof text. -/

-- Proof sketch: rewrite the Gamma density integral as a contour integral after the substitution
-- `z = (θ - i t) x`, then use the holomorphicity argument from the textbook proof to recover the
-- Gamma integral.
/-- Theorem 15.12 (3): Item (v). The Gamma law with shape `r` and rate `θ` has characteristic
function `t ↦ (1 - i t / θ)^{-r}`. -/
theorem charFun_gammaMeasure (r θ : ℝ) (hr : 0 < r) (hθ : 0 < θ) (t : ℝ) :
    charFun (gammaMeasure r θ) t = (1 - (t / θ) * Complex.I) ^ (-r : ℂ) := sorry

-- Proof sketch: specialize the Gamma formula to shape parameter `1`, using
-- `expMeasure θ = gammaMeasure 1 θ`.
/-- Theorem 15.12 (4): Item (vi). The exponential law with rate `θ` has characteristic function
`t ↦ (1 - i t / θ)^{-1}`. -/
theorem charFun_expMeasure (θ : ℝ) (hθ : 0 < θ) (t : ℝ) :
    charFun (expMeasure θ) t = (1 - (t / θ) * Complex.I)⁻¹ := sorry

-- Proof sketch: unfold `twoSidedExponentialMeasure`, multiply the characteristic functions of
-- the two exponential factors at `t` and `-t`, and simplify the resulting product.
/-- Theorem 15.12 (5): Item (vii). The centered two-sided exponential law has characteristic
function `t ↦ (1 + (t / θ)^2)^{-1}`. -/
theorem charFun_twoSidedExponentialMeasure (θ : ℝ) (hθ : 0 < θ) (t : ℝ) :
    charFun (twoSidedExponentialMeasure θ) t =
      (((1 + (t / θ) ^ 2 : ℝ) : ℂ))⁻¹ := sorry

-- Proof sketch: identify the centered Cauchy law by contour integration, or recover it from the
-- two-sided exponential law via Fourier inversion as in the textbook proof.
/-- Theorem 15.12 (6): Item (viii). The centered Cauchy law with scale `a` has characteristic
function `t ↦ exp (-a |t|)`. -/
theorem charFun_centeredCauchyMeasure (a : ℝ) (ha : 0 < a) (t : ℝ) :
    charFun (cauchyMeasure 0 (Real.toNNReal a)) t = Complex.exp (-a * |t|) := sorry

-- Proof sketch: expand the characteristic function as the finite sum of the singleton masses of
-- `binomial n p`, then apply the binomial theorem with `e^{it}` in place of the indeterminate.
/-- Theorem 15.12 (7): Item (ix). The binomial law with parameters `n` and `p` has characteristic
function `t ↦ (1 - p + p e^{it})^n`. -/
theorem charFun_binomial (n : ℕ) (p : I) (t : ℝ) :
    charFun ((binomial n p).map fun k : ℕ ↦ (k : ℝ)) t =
      (1 - (p : ℂ) + (p : ℂ) * Complex.exp (t * Complex.I)) ^ n := sorry

-- Proof sketch: expand the characteristic function using the negative-binomial singleton masses,
-- then sum the resulting series by the generalized binomial theorem with
-- `x = (1 - p) * e^{it}`.
/-- Theorem 15.12 (8): Item (x). The negative-binomial law with parameters `r > 0` and
`p ∈ (0,1]` has characteristic function `t ↦ p^r (1 - (1 - p)e^{it})^{-r}`. -/
theorem charFun_negativeBinomialMeasure
    (r p : ℝ) (hr : 0 < r) (hp : 0 < p) (hp_le_one : p ≤ 1) (t : ℝ) :
    charFun ((negativeBinomialMeasure r p hr hp hp_le_one).map fun k : ℕ ↦ (k : ℝ)) t =
      (p : ℂ) ^ (r : ℂ) * (1 - ((1 - p : ℝ) : ℂ) * Complex.exp (t * Complex.I)) ^ (-r : ℂ) := sorry

-- Proof sketch: expand the characteristic function as the power series of the Poisson singleton
-- masses and recognize the exponential series.
/-- Theorem 15.12 (9): Item (xi). The Poisson law with rate `λ` has characteristic function
`t ↦ exp (λ (e^{it} - 1))`. -/
theorem charFun_poissonMeasure (lam : NNReal) (t : ℝ) :
    charFun ((poissonMeasure lam).map fun k : ℕ ↦ (k : ℝ)) t =
      Complex.exp ((lam : ℂ) * (Complex.exp (t * Complex.I) - 1)) := sorry
