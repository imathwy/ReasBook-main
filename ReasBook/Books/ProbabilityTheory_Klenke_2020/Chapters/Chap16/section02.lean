import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_16_2_1 (from Items/Chap16) -/
open MeasureTheory ProbabilityTheory
open MeasureTheory.ProbabilityMeasure

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

/-- Source-facing strict `α`-stability for real probability laws. Unlike the chapter owner
`IsStableWithIndex`, this predicate keeps the textbook positivity and scaling law visible without
baking in the later conclusion that `α ≤ 2`. -/
def IsStrictlyStableWithIndex (μ : ProbabilityMeasure ℝ) (α : ℝ) : Prop :=
  0 < α ∧
    (∀ x : ℝ, μ ≠ diracProba x) ∧
      ∀ n : ℕ+,
        μ ^ (n : ℕ) =
          map μ (measurable_affineMap ((n : ℝ) ^ (1 / α)) 0).aemeasurable

/-- Source-facing broad `α`-stability for real probability laws. This keeps the centering data in
the public interface while deferring only the later upper bound `α ≤ 2` to a bridge lemma. -/
def IsBroadlyStableWithIndex (μ : ProbabilityMeasure ℝ) (α : ℝ) : Prop :=
  0 < α ∧
    (∀ x : ℝ, μ ≠ diracProba x) ∧
      ∃ d : ℕ+ → ℝ,
        ∀ n : ℕ+,
          μ ^ (n : ℕ) =
            map μ (measurable_affineMap ((n : ℝ) ^ (1 / α)) (d n)).aemeasurable

variable {μ : ProbabilityMeasure ℝ} {α : ℝ}

namespace IsStrictlyStableWithIndex

/-- On the admissible index range, the source-facing strict `α`-stability predicate specializes to
the chapter owner abstraction `IsStableWithIndex`. -/
theorem toIsStableWithIndex
    (hμ : IsStrictlyStableWithIndex μ α) (hα : α ≤ 2) :
    IsStableWithIndex μ α :=
  ⟨hμ.2.1, ⟨hμ.1, hα⟩, hμ.2.2⟩

end IsStrictlyStableWithIndex

namespace IsBroadlyStableWithIndex

/-- On the admissible index range, the source-facing broad `α`-stability predicate specializes to
the chapter owner abstraction `IsStableInBroadSenseWithIndex`. -/
theorem toIsStableInBroadSenseWithIndex
    (hμ : IsBroadlyStableWithIndex μ α) (hα : α ≤ 2) :
    IsStableInBroadSenseWithIndex μ α :=
  ⟨hμ.2.1, ⟨hμ.1, hα⟩, hμ.2.2⟩

end IsBroadlyStableWithIndex

-- Proof sketch: pass to the chapter owner abstraction on the admissible range via
-- `IsStrictlyStableWithIndex.toIsStableWithIndex`, rewrite the resulting scaling law on
-- characteristic functions, and choose `n` comparable to `|t|^{-α}` to obtain the Hölder bound
-- near the origin.
/-- Exercise 16.2.1 (1): if a real probability law is strictly stable with index `α`, then its
characteristic function satisfies `|φ(t) - 1| ≤ C |t|^α` for all sufficiently small `t`. -/
theorem norm_charFun_sub_one_le_const_mul_rpow_of_isStrictlyStableWithIndex
    (hμ : IsStrictlyStableWithIndex μ α) :
    ∃ C > 0, ∃ δ > 0, ∀ t : ℝ, |t| < δ →
      ‖charFun (μ : Measure ℝ) t - 1‖ ≤ C * Real.rpow |t| α := sorry

-- Proof sketch: combine the small-frequency bound from item (1) with the second-order criterion
-- from Exercise 15.3.2; for `α > 2`, the source-facing strict `α`-stability relation forces the
-- characteristic function to be flatter than quadratic at the origin, hence the law is the Dirac
-- mass at `0`.
/-- Exercise 16.2.1 (2): a strictly stable real probability law with index `α > 2` is
necessarily the Dirac mass at `0`. -/
theorem eq_dirac_zero_of_two_lt_of_isStrictlyStableWithIndex
    (hμ : IsStrictlyStableWithIndex μ α) (hα : 2 < α) :
    (μ : Measure ℝ) = Measure.dirac 0 := sorry

-- Proof sketch: adapt the argument from item (2) to the source-facing affine scaling relation for
-- broad `α`-stability, absorbing the centering term into the characteristic-function identity and
-- then applying the same quadratic flatness criterion at the origin.
/-- Exercise 16.2.1 (3): a broadly stable real probability law with index `α > 2` is
necessarily the Dirac mass at `0`. -/
theorem eq_dirac_zero_of_two_lt_of_isBroadlyStableWithIndex
    (hμ : IsBroadlyStableWithIndex μ α) (hα : 2 < α) :
    (μ : Measure ℝ) = Measure.dirac 0 := sorry

end MeasureTheory.ProbabilityMeasure

/-! ### Example_16_2 (from Items/Chap16) -/
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

/-! ### Exercise_16_2_2 (from Items/Chap16) -/
open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

/-- The textbook density `x ↦ (1 - cos x) / (π x^2)`. -/
noncomputable def cosineDensity (x : ℝ) : ℝ :=
  (1 - Real.cos x) / (Real.pi * x ^ 2)

/-- The measure on `ℝ` with density `x ↦ (1 - cos x) / (π x^2)` with respect to Lebesgue
measure. -/
noncomputable def cosineDensityMeasure : Measure ℝ :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (cosineDensity x))

/-- The density measure `cosineDensityMeasure` has total mass `1`. -/
instance cosineDensityMeasure_isProbabilityMeasure :
    IsProbabilityMeasure cosineDensityMeasure := sorry

/-- The probability distribution on `ℝ` with density `x ↦ (1 - cos x) / (π x^2)`. -/
noncomputable def cosineDensityProbabilityMeasure : ProbabilityMeasure ℝ :=
  ⟨cosineDensityMeasure, inferInstance⟩

-- Proof sketch: compute the Fourier transform of `cosineDensityMeasure`; it is the triangular
-- function `t ↦ max (1 - |t|) 0`, which vanishes at `t = 1`.
/-- The characteristic function of `cosineDensityProbabilityMeasure` vanishes at `t = 1`. -/
theorem charFun_cosineDensityProbabilityMeasure_one :
    charFun (cosineDensityProbabilityMeasure : Measure ℝ) (1 : ℝ) = 0 := sorry

-- Proof sketch: if the law were infinitely divisible, then the owner-level nonvanishing theorem
-- `charFun_ne_zero_of_isInfinitelyDivisible` from Exercise 16.1.2 would force its characteristic
-- function to be
-- nonzero at every real argument, contradicting `charFun_cosineDensityProbabilityMeasure_one`.
/-- Exercise 16.2.2: the probability distribution on `ℝ` with density
`x ↦ (1 - cos x) / (π x^2)` is not infinitely divisible. -/
theorem cosineDensityProbabilityMeasure_not_isInfinitelyDivisible :
    ¬ IsInfinitelyDivisible cosineDensityProbabilityMeasure := by
  intro hμ
  exact (charFun_ne_zero_of_isInfinitelyDivisible hμ 1)
    charFun_cosineDensityProbabilityMeasure_one

end MeasureTheory.ProbabilityMeasure

/-! ### Exercise_16_2_3 (from Items/Chap16) -/
open MeasureTheory ProbabilityTheory Filter
open MeasureTheory.ProbabilityMeasure
open scoped MeasureTheory Topology

noncomputable section

universe u

private def exercise1623DistributionFormula (x : ℝ) : ℝ :=
  if 0 < x then 2 * (1 - cdf (gaussianReal (0 : ℝ) 1) (1 / Real.sqrt x)) else 0

private theorem exercise1623DistributionFormula_monotone :
    Monotone exercise1623DistributionFormula := sorry

private theorem exercise1623DistributionFormula_rightContinuous (x : ℝ) :
    ContinuousWithinAt exercise1623DistributionFormula (Set.Ici x) x := sorry

/-- The textbook distribution function `F` from Exercise 16.2.3, viewed as the canonical Chapter 1
distribution-function owner object. -/
def exercise1623DistributionFunction : StieltjesFunction ℝ where
  toFun := exercise1623DistributionFormula
  mono' := exercise1623DistributionFormula_monotone
  right_continuous' := exercise1623DistributionFormula_rightContinuous

/-- The textbook formula for the distribution function in Exercise 16.2.3. -/
@[simp] theorem exercise1623DistributionFunction_apply (x : ℝ) :
    exercise1623DistributionFunction x =
      if 0 < x then 2 * (1 - cdf (gaussianReal (0 : ℝ) 1) (1 / Real.sqrt x)) else 0 := rfl

/-- The textbook function in Exercise 16.2.3 is a distribution function in the Chapter 1 sense. -/
instance : IsDistributionFunction exercise1623DistributionFunction := sorry

-- Proof sketch: unfold `exercise1623DistributionFunction`; on the nonpositive branch the defining
-- `if` returns `0`.
/-- The textbook function `F` vanishes on `(-∞, 0]`. -/
theorem exercise1623DistributionFunction_of_nonpos
    {x : ℝ} (hx : x ≤ 0) :
    exercise1623DistributionFunction x = 0 := sorry

-- Proof sketch: use the hint to identify the law with the positive `1 / 2`-stable law having
-- Laplace transform `λ ↦ exp (-√(2λ))`, then translate strict stability into the displayed
-- convolution-scaling relation.
/-- Exercise 16.2.3 (1): the textbook function
`F(x) = 2 (1 - cdf (gaussianReal 0 1) (x^{-1/2}))` for `x > 0` and `F(x) = 0` for `x ≤ 0`
is the cumulative distribution function of a `1 / 2`-stable probability law on `ℝ`. -/
theorem exists_halfStable_measure_with_exercise1623_distributionFunction
    :
    ∃ μ : ProbabilityMeasure ℝ,
      cdf (μ : Measure ℝ) = exercise1623DistributionFunction ∧
        IsStableWithIndex μ (1 / 2 : ℝ) := sorry

-- Proof sketch: for the positive `1 / 2`-stable law the first moment is infinite, and the
-- classical heavy-tail law of large numbers implies that the Cesàro averages of an i.i.d.
-- sequence with this law fail to converge almost surely.
/-- Exercise 16.2.3 (2): if `μ` has the distribution function from Exercise 16.2.3 and
`X₀, X₁, …` are i.i.d. with law `μ`, then their Cesàro averages diverge almost surely. -/
theorem iid_exercise1623_partialAverage_ae_diverges
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : ProbabilityMeasure ℝ)
    (hμ : cdf (μ : Measure ℝ) = exercise1623DistributionFunction)
    (X : ℕ → Ω → ℝ) (h_indep : iIndepFun X P)
    (h_law : ∀ n : ℕ, HasLaw (X n) (μ : Measure ℝ) P) :
    ∀ᵐ ω ∂P, ¬ ∃ x : ℝ,
      Tendsto (fun n : ℕ+ ↦ partialRealSum X n ω / (n : ℝ)) atTop (nhds x) := sorry

/-! ### Exercise_16_2_4 (from Items/Chap16) -/
open MeasureTheory ProbabilityTheory

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

/-- The stable index determined by two power-law contributions is the smaller tail index,
truncated above by the Gaussian value `2`. -/
def heavyTailStableIndex (α β : ℝ) : ℝ :=
  min (2 : ℝ) (min (-1 - α) (-1 - β))

/-- The stable index of the textbook piecewise power-tail law. When `ρ = 0`, only the right tail
survives; when `ρ = 1`, only the left tail survives; otherwise both tails contribute and the
smaller tail index dominates, truncated above by the Gaussian value `2`. -/
def piecewisePowerTailStableIndex (α β ρ : ℝ) : ℝ :=
  if ρ = 0 then
    min (2 : ℝ) (-1 - β)
  else if ρ = 1 then
    min (2 : ℝ) (-1 - α)
  else
    heavyTailStableIndex α β

/-- The textbook piecewise power-law density with left exponent `α`, right exponent `β`, and left
tail mass parameter `ρ`, normalized so that the left and right tails have masses `ρ` and
`1 - ρ`. -/
def piecewisePowerTailDensity (α β ρ : ℝ) : ℝ → ENNReal :=
  fun x ↦
    if x < -1 then
      ENNReal.ofReal (ρ * (-(1 + α)) * Real.rpow |x| α)
    else if 1 < x then
      ENNReal.ofReal ((1 - ρ) * (-(1 + β)) * Real.rpow x β)
    else
      0

/-- The textbook two-sided piecewise power-tail measure on `ℝ`. -/
def piecewisePowerTailMeasure (α β ρ : ℝ) : Measure ℝ :=
  volume.withDensity (piecewisePowerTailDensity α β ρ)

/-- For admissible exponents and mixing parameter, the textbook piecewise power-tail measure is a
probability measure. -/
theorem piecewisePowerTailMeasure_isProbabilityMeasure
    {α β ρ : ℝ} (hα : α < -1) (hβ : β < -1) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (piecewisePowerTailMeasure α β ρ) := sorry

/-- The textbook two-sided piecewise power-tail law on `ℝ`. -/
def piecewisePowerTailLaw (α β ρ : ℝ) (hα : α < -1) (hβ : β < -1)
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) : ProbabilityMeasure ℝ :=
  ⟨piecewisePowerTailMeasure α β ρ, piecewisePowerTailMeasure_isProbabilityMeasure hα hβ hρ⟩

/-- The normalization constant in the parity-dependent power-law distribution from the exercise.
-/
def oddEvenPowerNormConst (α β : ℝ) : ℝ :=
  (Real.rpow (2 : ℝ) α) * Complex.re (riemannZeta (-α)) +
    (1 - Real.rpow (2 : ℝ) β) * Complex.re (riemannZeta (-β))

/-- The parity-dependent power-law weights on `ℕ`, with even weights proportional to `n^α`, odd
weights proportional to `n^β`, and the exercise's normalization constant. -/
def oddEvenPowerWeight (α β : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then
    0
  else if Even n then
    (oddEvenPowerNormConst α β)⁻¹ * Real.rpow (n : ℝ) α
  else
    (oddEvenPowerNormConst α β)⁻¹ * Real.rpow (n : ℝ) β

/-- For admissible exponents, the parity-dependent power-law weights sum to `1` as an `ENNReal`
series. -/
theorem oddEvenPowerWeight_hasSum_ennreal
    {α β : ℝ} (hα : α < -1) (hβ : β < -1) :
    HasSum (fun n : ℕ ↦ ENNReal.ofReal (oddEvenPowerWeight α β n)) 1 := sorry

/-- The parity-dependent power-law distribution on `ℕ`, realized as a probability mass function.
-/
def oddEvenPowerPMF (α β : ℝ) (hα : α < -1) (hβ : β < -1) : PMF ℕ :=
  ⟨fun n ↦ ENNReal.ofReal (oddEvenPowerWeight α β n),
    oddEvenPowerWeight_hasSum_ennreal hα hβ⟩

/-- The parity-dependent power-law distribution on `ℕ`, viewed as a law on `ℝ`. -/
def oddEvenPowerLaw (α β : ℝ) (hα : α < -1) (hβ : β < -1) : ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map
    ⟨(oddEvenPowerPMF α β hα hβ).toMeasure, inferInstance⟩
    (measurable_of_countable fun n : ℕ ↦ (n : ℝ)).aemeasurable

-- Proof sketch: compute the left and right tails of the density, identify the dominating regularly
-- varying exponent `piecewisePowerTailStableIndex α β ρ`, and then apply the stable
-- domain-of-attraction criterion for one-dimensional laws.
/-- Exercise 16.2.4 (1): source clause (i). A real probability law with the textbook two-sided
piecewise power-law density belongs to the domain of attraction of a stable law with index
`piecewisePowerTailStableIndex α β ρ`. -/
theorem piecewisePowerTailLaw_mem_domainOfAttraction_stableWithIndex
    {α β ρ : ℝ} (hα : α < -1) (hβ : β < -1) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    IsInDomainOfAttractionOfStableWithIndex
      (piecewisePowerTailLaw α β ρ hα hβ hρ)
      (piecewisePowerTailStableIndex α β ρ) := sorry

-- Proof sketch: exponential laws have finite variance, so after centering and `√n` scaling their
-- i.i.d. sums converge to a Gaussian law; in the chapter API this means the law belongs to the
-- domain of attraction of a stable law with index `2`.
/-- Exercise 16.2.4 (2): source clause (ii). The exponential law with rate `θ > 0` belongs to the
domain of attraction of a stable law with parameter `2`. -/
theorem exponentialLaw_mem_domainOfAttraction_stableWithIndex_two {θ : ℝ} (hθ : 0 < θ) :
    IsInDomainOfAttractionOfStableWithIndex
      (⟨expMeasure θ, isProbabilityMeasure_expMeasure hθ⟩ : ProbabilityMeasure ℝ) 2 := sorry

-- Proof sketch: compare the parity-dependent tails with the corresponding regularly varying
-- sequences, identify the dominating exponent `heavyTailStableIndex α β`, and then apply the
-- one-dimensional stable domain-of-attraction criterion.
/-- Exercise 16.2.4 (3): source clause (iii). The parity-dependent power-law distribution on `ℕ`,
viewed as a law on `ℝ`, belongs to the domain of attraction of a stable law with index
`heavyTailStableIndex α β`. -/
theorem oddEvenPowerLaw_mem_domainOfAttraction_stableWithIndex
    {α β : ℝ} (hα : α < -1) (hβ : β < -1) :
    IsInDomainOfAttractionOfStableWithIndex
      (oddEvenPowerLaw α β hα hβ)
      (heavyTailStableIndex α β) := sorry

end MeasureTheory.ProbabilityMeasure
