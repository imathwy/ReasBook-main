import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap03.Exercise_3_1_1
import ProbabilityTheory_Klenke_2020.Items.Chap15.Corollary_15_25
import ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory NNReal unitInterval

noncomputable section

universe u

-- Proof sketch: the sum of `n` independent point masses at `x / n` is the point mass at `x`, so
-- the `n`th convolution power of `δ_{x / n}` is `δ_x`.
/-- Example 16.2 (1): The Dirac law `δ_x` is infinitely divisible, with explicit `n`th convolution
root `δ_{x / n}` for every positive integer `n`. -/
theorem measureConvolutionPower_dirac_div_eq_dirac (x : ℝ) (n : ℕ+) :
    let ν : ProbabilityMeasure ℝ := ⟨Measure.dirac (x / (n : ℝ)), inferInstance⟩
    ν ^ (n : ℕ) = diracProba x := sorry

-- Proof sketch: convolving Gaussian laws adds means and variances; iterating the Gaussian
-- convolution formula with mean `m / n` and variance `σ² / n` yields `N_{m,σ²}`.
/-- Example 16.2 (2): The Gaussian law `N_{m,σ²}` is infinitely divisible, with
`N_{m / n, σ² / n}` as an `n`th convolution root for every positive integer `n`. -/
theorem measureConvolutionPower_gaussianReal_div_eq_gaussianReal
    (m : ℝ) (σ2 : ℝ≥0) (n : ℕ+) :
    let ν : ProbabilityMeasure ℝ :=
      ⟨gaussianReal (m / (n : ℝ)) (σ2 / (n : ℝ≥0)), inferInstance⟩
    let μ : ProbabilityMeasure ℝ := ⟨gaussianReal m σ2, inferInstance⟩
    ν ^ (n : ℕ) = μ := sorry

-- Proof sketch: the centered Cauchy convolution law adds scale parameters; iterating the centered
-- convolution identity with scale `a / n` gives the scale `a` law.
/-- Example 16.2 (3): The centered Cauchy law with scale `a` is infinitely divisible, with
`Cau_{a / n}` as an `n`th convolution root for every positive integer `n`. -/
theorem measureConvolutionPower_centeredCauchy_div_eq_centeredCauchy
    (a : ℝ≥0) (n : ℕ+) :
    let ν : ProbabilityMeasure ℝ := ⟨cauchyMeasure 0 (a / (n : ℝ≥0)), inferInstance⟩
    let μ : ProbabilityMeasure ℝ := ⟨cauchyMeasure 0 a, inferInstance⟩
    ν ^ (n : ℕ) = μ := sorry

-- Proof sketch: apply the symmetric-stable existence theorem with scale
-- `γ / (n : ℝ) ^ (1 / α)` to realize the stated characteristic function by a probability law.
/-- Example 16.2 (4): Source item (4), existence part. For every positive integer `n`, there is a
probability law with
characteristic function `t ↦ exp (-|(γ / n^(1 / α)) t|^α)` whenever `α ∈ (0,2]` and `γ > 0`. -/
theorem exists_symmetricStable_root_measure
    (α γ : ℝ) (hα₀ : 0 < α) (hα₂ : α ≤ 2) (hγ : 0 < γ) :
    ∀ n : ℕ+, ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      ∀ t : ℝ, charFun ν t =
        symmetricStableCharFun α (γ / (n : ℝ) ^ (1 / α)) t := sorry

-- Proof sketch: the characteristic functions satisfy
-- `exp (-|γ t|^α) = exp (-|(γ / n^(1 / α)) t|^α) ^ (n : ℕ)`; then uniqueness of characteristic
-- functions identifies the `n`th convolution power of `ν` with `μ`.
/-- Example 16.2 (5): Source item (4), root-identification part. A probability law with
characteristic function
`t ↦ exp (-|(γ / n^(1 / α)) t|^α)` is an `n`th convolution root of the symmetric stable law with
characteristic function `t ↦ exp (-|γ t|^α)`. -/
theorem measureConvolutionPower_eq_of_charFun_eq_symmetricStable_root
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (α γ : ℝ) (hα₀ : 0 < α) (hα₂ : α ≤ 2) (hγ : 0 < γ) (n : ℕ+)
    (hμ : ∀ t : ℝ, charFun μ t = symmetricStableCharFun α γ t)
    (hν : ∀ t : ℝ, charFun ν t =
      symmetricStableCharFun α (γ / (n : ℝ) ^ (1 / α)) t) :
    let μ₀ : ProbabilityMeasure ℝ := ⟨μ, inferInstance⟩
    let ν₀ : ProbabilityMeasure ℝ := ⟨ν, inferInstance⟩
    ν₀ ^ (n : ℕ) = μ₀ := sorry

-- Proof sketch: for each `n`, choose `ν` from `exists_symmetricStable_root_measure` and apply
-- `measureConvolutionPower_eq_of_charFun_eq_symmetricStable_root`.
/-- Example 16.2 (6): Source item (4), infinite-divisibility conclusion. Every symmetric stable
law with index `α ∈ (0,2]` and scale parameter `γ > 0` is infinitely divisible. -/
theorem symmetricStable_isInfinitelyDivisible
    (μ : ProbabilityMeasure ℝ) (α γ : ℝ)
    (hα₀ : 0 < α) (hα₂ : α ≤ 2) (hγ : 0 < γ)
    (hchar : ∀ t : ℝ, charFun (μ : Measure ℝ) t = symmetricStableCharFun α γ t) :
    MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible μ := sorry

-- Proof sketch: Gamma convolution at fixed rate adds shape parameters; iterating the common-rate
-- convolution identity with shape `r / n` gives the shape `r` law.
/-- Example 16.2 (7): Source item (5). The Gamma law `Γ_{θ,r}` with `θ, r > 0` is infinitely
divisible, with `Γ_{θ, r / n}` as an `n`th convolution root for every positive integer `n`. -/
theorem measureConvolutionPower_gammaMeasure_shape_div_eq_gammaMeasure
    (θ r : ℝ) (hθ : 0 < θ) (hr : 0 < r) (n : ℕ+) :
    let ν : ProbabilityMeasure ℝ :=
      ⟨gammaMeasure (r / (n : ℝ)) θ,
        isProbabilityMeasure_gammaMeasure
          (div_pos hr (show (0 : ℝ) < (n : ℝ) by exact_mod_cast n.pos)) hθ⟩
    let μ : ProbabilityMeasure ℝ := ⟨gammaMeasure r θ, isProbabilityMeasure_gammaMeasure hr hθ⟩
    ν ^ (n : ℕ) = μ := sorry

-- Proof sketch: Poisson convolution adds intensities, so iterating the Poisson convolution law
-- with intensity `λ / n` produces `Poi_λ`.
/-- Example 16.2 (8): Source item (6). The Poisson law `Poi_λ` is infinitely divisible, with
`Poi_{λ / n}` as an `n`th convolution root for every positive integer `n`. -/
theorem measureConvolutionPower_poissonMeasure_div_eq_poissonMeasure
    (lam : ℝ≥0) (n : ℕ+) :
    let ν : ProbabilityMeasure ℕ := ⟨poissonMeasure (lam / (n : ℝ≥0)), inferInstance⟩
    let μ : ProbabilityMeasure ℕ := ⟨poissonMeasure lam, inferInstance⟩
    ν ^ (n : ℕ) = μ := sorry

-- Proof sketch: negative-binomial convolution at fixed success parameter adds the shape
-- parameters; iterating the convolution identity with shape `r / n` yields the law with shape
-- `r`.
/-- Example 16.2 (9): Source item (7). The negative-binomial law with parameters `r > 0` and
`p ∈ (0,1)` is infinitely divisible, with `b^-_{r / n, p}` as an `n`th convolution root for every
positive integer `n`. -/
theorem measureConvolutionPower_negativeBinomial_div_eq_negativeBinomial
    (r p : ℝ) (hr : 0 < r) (hp : 0 < p) (hp₁ : p < 1) (n : ℕ+) :
    let ν : ProbabilityMeasure ℕ :=
      ⟨negativeBinomialMeasure (r / (n : ℝ)) p
          (div_pos hr (show (0 : ℝ) < (n : ℝ) by exact_mod_cast n.pos)) hp
          (le_of_lt hp₁), inferInstance⟩
    let μ : ProbabilityMeasure ℕ := ⟨negativeBinomialMeasure r p hr hp (le_of_lt hp₁), inferInstance⟩
    ν ^ (n : ℕ) = μ := sorry

-- Proof sketch: one uses the cited representation theorem for the variance-mixture law
-- `X / √Y`; once that law is known to be infinitely divisible, the Student `t` family follows by
-- the stated parameter specialization.
/-- Example 16.2 (10): Source item (8). If `X` and `Y` are independent with `X ∼ N_{0,σ²}` and
`Y ∼ Γ_{θ,r}` for `σ², θ, r > 0`, then the law of `X / √Y` is infinitely divisible. In
particular, the same applies to Student's `t` laws obtained from the specialization `σ² = 1` and
`θ = r = k / 2`. -/
theorem ratio_gaussian_sqrtGamma_isInfinitelyDivisible
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hXY : IndepFun X Y P) (σ2 : ℝ≥0) (θ r : ℝ)
    (hσ2 : 0 < σ2) (hθ : 0 < θ) (hr : 0 < r)
    (hX : HasLaw X (gaussianReal (0 : ℝ) σ2) P)
    (hY : HasLaw Y (gammaMeasure r θ) P) :
    IsInfinitelyDivisibleRandomVariable P (fun ω ↦ X ω / Real.sqrt (Y ω)) := sorry

/-- The binomial law viewed as a probability measure on `ℝ` via the inclusion `ℕ ↪ ℝ`. -/
noncomputable def binomialRealProbabilityMeasure (n : ℕ) (p : I) : ProbabilityMeasure ℝ :=
  let ν : ProbabilityMeasure ℕ := ⟨binomial n p, inferInstance⟩
  ν.map (show AEMeasurable (fun k : ℕ ↦ (k : ℝ)) ν from Measurable.of_discrete.aemeasurable)

-- Proof sketch: a nondegenerate binomial law is finitely supported on `{0, …, n}`; any
-- hypothetical convolution roots would force an impossible bounded-support infinitely divisible
-- law, so the binomial law cannot be infinitely divisible.
/-- Example 16.2 (11): Source item (9). The nondegenerate binomial law with parameters `n ≥ 1` and
`p ∈ (0,1)`, viewed as a probability law on `ℝ` via the inclusion `ℕ ↪ ℝ`, is not infinitely
divisible. -/
theorem binomial_not_isInfinitelyDivisible
    (n : ℕ+) (p : I) (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) < 1) :
    ¬ MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible
      (binomialRealProbabilityMeasure (n : ℕ) p) := sorry

-- Proof sketch: if an infinitely divisible probability law has full mass on a bounded interval,
-- repeated convolution roots shrink the interval width; letting the width tend to `0` forces the
-- law to collapse to a single Dirac mass.
/-- Example 16.2 (12): Source item (10). An infinitely divisible probability distribution
concentrated on a bounded interval must be a Dirac mass. Equivalently, there is no nontrivial
infinitely divisible distribution supported in a bounded interval. -/
theorem eq_dirac_of_isInfinitelyDivisible_of_measure_Icc_eq_one
    (μ : ProbabilityMeasure ℝ) [MeasureTheory.ProbabilityMeasure.IsInfinitelyDivisible μ]
    (a b : ℝ)
    (hμ : (μ : Measure ℝ) (Set.Icc a b) = 1) :
    ∃ x ∈ Set.Icc a b, (μ : Measure ℝ) = Measure.dirac x := sorry
