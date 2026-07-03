import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_23_2_1 (from Items/Chap23) -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

noncomputable section

namespace ProbabilityTheory

/-- The quadratic rate function `x ↦ x^2 / 2` valued in `ℝ≥0∞`. -/
noncomputable def gaussianQuadraticRateFunction (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (x ^ 2 / 2)

/-- The same quadratic rate function viewed in `EReal` for the variational bounds. -/
noncomputable def gaussianQuadraticRateFunctionEReal (x : ℝ) : EReal :=
  gaussianQuadraticRateFunction x

/-- The small-variance centered Gaussian law `μ_ε = N(0, ε)` for positive `ε`. -/
noncomputable def centeredGaussianSmallVarianceLaw (ε : ℝ) : Measure ℝ :=
  gaussianReal 0 (Real.toNNReal ε)

/-- The exponential rate expression `ε log μ_ε(s)` used in the LDP bounds. -/
noncomputable def centeredGaussianSmallVarianceExponent (s : Set ℝ) (ε : ℝ) : EReal :=
  (ε : EReal) * ENNReal.log (centeredGaussianSmallVarianceLaw ε s)

-- Proof sketch: the map `x ↦ x ^ 2 / 2` is continuous on `ℝ`, hence lower semicontinuous after
-- composing with `ENNReal.ofReal`; its finite sublevel sets are closed bounded intervals, so they
-- are compact by Heine--Borel.
/-- Exercise 23.2.1 (1): the quadratic map `I(x) = x^2 / 2`, viewed as an `ℝ≥0∞`-valued map, is a
good rate function on `ℝ`: it is lower semicontinuous and every finite sublevel set is compact. -/
theorem gaussianQuadraticRateFunction_isGood :
    IsGoodRateFunction gaussianQuadraticRateFunction := sorry

-- Proof sketch: evaluate the Gaussian cumulant generating function, derive the exponential lower
-- bound by the standard Laplace-Varadhan argument, and identify the Legendre transform with
-- `x ↦ x^2 / 2` as `ε ↓ 0`.
/-- Exercise 23.2.1 (2): for every open set `G ⊆ ℝ`, the centered Gaussian family
`μ_ε = N(0, ε)` satisfies the LDP lower bound with rate function `I(x) = x^2 / 2`. -/
theorem centeredGaussianSmallVariance_ldp_lowerBound :
    ∀ G : Set ℝ, IsOpen G →
      -sInf (gaussianQuadraticRateFunctionEReal '' G) ≤
        Filter.liminf (centeredGaussianSmallVarianceExponent G) (𝓝[>] (0 : ℝ)) := sorry

-- Proof sketch: apply Gaussian tail estimates or exponential Chebyshev bounds on closed sets,
-- optimize the exponent, and obtain the negative infimum of the quadratic rate function.
/-- Exercise 23.2.1 (3): for every closed set `F ⊆ ℝ`, the centered Gaussian family
`μ_ε = N(0, ε)` satisfies the LDP upper bound with rate function `I(x) = x^2 / 2`. -/
theorem centeredGaussianSmallVariance_ldp_upperBound :
    ∀ F : Set ℝ, IsClosed F →
      Filter.limsup (centeredGaussianSmallVarianceExponent F) (𝓝[>] (0 : ℝ)) ≤
        -sInf (gaussianQuadraticRateFunctionEReal '' F) := sorry

-- Proof sketch: choose the closed set `{0}`. Since every nondegenerate Gaussian `N(0, ε)` is
-- atomless, `μ_ε({0}) = 0` for all `ε > 0`, so the left-hand side is `-∞`, while the rate side is
-- `-I(0) = 0`.
/-- Exercise 23.2.1 (4): the closed set `{0}` gives a strict instance of the LDP upper bound for
`μ_ε = N(0, ε)`, so equality need not hold in (LDP 2). -/
theorem centeredGaussianSmallVariance_ldp_upperBound_strictAtSingletonZero :
    Filter.limsup (centeredGaussianSmallVarianceExponent ({0} : Set ℝ)) (𝓝[>] (0 : ℝ)) <
      -sInf (gaussianQuadraticRateFunctionEReal '' ({0} : Set ℝ)) := sorry

end ProbabilityTheory

/-! ### Exercise_23_2_2 (from Items/Chap23) -/
open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal

noncomputable section

/-- The Gaussian family `μ_ε = 𝒩(0, ε²)` from Exercise 23.2.2. -/
def smallVarianceGaussianFamily : PositiveProbabilityFamily ℝ :=
  fun ε ↦
    ⟨gaussianReal 0 ⟨(ε : ℝ) ^ 2, sq_nonneg (ε : ℝ)⟩, inferInstance⟩

-- Proof sketch: unfold `smallVarianceGaussianFamily`; the statement is exactly its defining
-- equation.
/-- Evaluating `smallVarianceGaussianFamily` at `ε` gives the centered Gaussian law with variance
`ε²`. -/
theorem smallVarianceGaussianFamily_apply (ε : PositiveParameter) :
    (smallVarianceGaussianFamily ε : Measure ℝ) =
      gaussianReal 0 ⟨(ε : ℝ) ^ 2, sq_nonneg (ε : ℝ)⟩ := sorry

/-- The rate function from Exercise 23.2.2, equal to `0` at the origin and `∞` away from `0`. -/
def zeroDiracRateFunction (x : ℝ) : ℝ≥0∞ :=
  if x = 0 then 0 else ⊤

-- Proof sketch: unfold `zeroDiracRateFunction`; when `x ≠ 0` the defining `if` takes the second
-- branch.
/-- Away from the origin, `zeroDiracRateFunction` is infinite. -/
theorem zeroDiracRateFunction_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    zeroDiracRateFunction x = ⊤ := sorry

-- Proof sketch: the Gaussian family collapses exponentially fast onto the singleton `{0}` as
-- `ε ↓ 0`, so the large-deviation bounds are governed by the rate that is `0` at `0` and `∞`
-- elsewhere; the finite sublevel sets are either empty or `{0}`, hence compact.
/-- Exercise 23.2.2: the family `μ_ε = 𝒩(0, ε²)` satisfies the large deviations principle with
good rate function `I(x) = ∞ · 𝟙_{ℝ \ {0}}(x)`, written here as the function that is `0` at `0`
and `∞` elsewhere. -/
theorem smallVarianceGaussianFamily_satisfiesLDPWithGoodRate :
    HasLargeDeviationsPrinciple smallVarianceGaussianFamily zeroDiracRateFunction ∧
      IsGoodRateFunction zeroDiracRateFunction := sorry

-- Proof sketch: take the open set `(0, ∞)`. Its rate infimum is `∞`, so the LDP lower bound gives
-- only `-∞`, while the Gaussian symmetry gives `μ_ε (0, ∞) = 1 / 2`, hence `ε log μ_ε (0, ∞) → 0`.
/-- The open half-line `(0, ∞)` witnesses that the lower bound in the large deviations principle
can be strict for `μ_ε = 𝒩(0, ε²)`. -/
theorem smallVarianceGaussianFamily_strict_lowerBound_on_positiveHalfline :
    -sInf ((fun x : ℝ ↦ (zeroDiracRateFunction x : EReal)) '' Set.Ioi (0 : ℝ)) <
      liminf
        (scaledLogMassAlong (fun ε ↦ (smallVarianceGaussianFamily ε : Measure ℝ)) (fun ε ↦ ε)
          (Set.Ioi (0 : ℝ)))
        positiveParameterFilter := sorry

/-! ### Remark_23_2 (from Items/Chap23) -/
open Set

noncomputable section

namespace ProbabilityTheory

/-- The finite-value branch of the Bernoulli Cramér rate function, namely
`((1 + x) log (1 + x) + (1 - x) log (1 - x)) / 2`. -/
def bernoulliCramerRateFunction (x : ℝ) : ℝ :=
  ((1 + x) * Real.log (1 + x) + (1 - x) * Real.log (1 - x)) / 2

-- Proof sketch: combine mathlib's canonical continuity theorem `Real.continuous_mul_log` with the
-- affine maps `x ↦ 1 + x` and `x ↦ 1 - x`; on `[-1,1]` both arguments stay in `[0,2]`, so the sum
-- and scalar multiple remain continuous.
/-- Remark 23.2: with the convention `0 log 0 = 0`, the restriction of the Bernoulli Cramér rate
function to `[-1,1]` is continuous. -/
theorem bernoulliCramerRateFunction_continuousOn :
    ContinuousOn bernoulliCramerRateFunction (Icc (-1 : ℝ) 1) := sorry

-- Proof sketch: substitute `x = -1` into the explicit formula; the `0 log 0` term vanishes and
-- the remaining term is `(2 * log 2) / 2`.
/-- The Bernoulli Cramér rate function takes the endpoint value `log 2` at `-1`. -/
theorem bernoulliCramerRateFunction_neg_one :
    bernoulliCramerRateFunction (-1) = Real.log 2 := sorry

-- Proof sketch: substitute `x = 1` into the explicit formula; again the `0 log 0` term vanishes
-- and the remaining term is `(2 * log 2) / 2`.
/-- The Bernoulli Cramér rate function takes the endpoint value `log 2` at `1`. -/
theorem bernoulliCramerRateFunction_one :
    bernoulliCramerRateFunction 1 = Real.log 2 := sorry

-- Proof sketch: combine the canonical strict convexity of `x ↦ x * Real.log x` on `Ici 0` given by
-- `Real.strictConvexOn_mul_log` with the affine maps `x ↦ 1 + x` and `x ↦ 1 - x`, then use the
-- endpoint continuity to extend strict convexity to the closed interval.
/-- The Bernoulli Cramér rate function is strictly convex on `[-1,1]`. -/
theorem bernoulliCramerRateFunction_strictConvexOn :
    StrictConvexOn ℝ (Icc (-1 : ℝ) 1) bernoulliCramerRateFunction := sorry

-- Proof sketch: evaluate the explicit formula at `x = 0`; both logarithmic terms are
-- `1 * log 1 = 0`.
/-- The Bernoulli Cramér rate function vanishes at the origin. -/
theorem bernoulliCramerRateFunction_zero :
    bernoulliCramerRateFunction 0 = 0 := sorry

-- Proof sketch: the derivative of the explicit formula is nonnegative on `[0,1]`, so the
-- function is monotone increasing there.
/-- The Bernoulli Cramér rate function is monotone increasing on `[0,1]`. -/
theorem bernoulliCramerRateFunction_monotoneOn_nonneg :
    MonotoneOn bernoulliCramerRateFunction (Icc (0 : ℝ) 1) := sorry

-- Proof sketch: the derivative of the explicit formula is nonpositive on `[-1,0]`, so the
-- function is monotone decreasing there.
/-- The Bernoulli Cramér rate function is monotone decreasing on `[-1,0]`. -/
theorem bernoulliCramerRateFunction_antitoneOn_nonpos :
    AntitoneOn bernoulliCramerRateFunction (Icc (-1 : ℝ) 0) := sorry

end ProbabilityTheory

/-! ### Exercise_23_2_3 (from Items/Chap23) -/
open Filter MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Topology

noncomputable section

universe u

namespace ProbabilityTheory

/-- The Gaussian-mixture family
`μ_ε = (1 / 2) N(-1, ε) + (1 / 2) N(1, ε)` from the exercise, indexed by `ε > 0`. -/
def twoPointGaussianMixtureMeasureFamily (ε : PositiveParameter) : Measure ℝ :=
  (1 / 2 : ℝ≥0∞) • gaussianReal (-1) (Real.toNNReal ε) +
    (1 / 2 : ℝ≥0∞) • gaussianReal 1 (Real.toNNReal ε)

/-- The rate function `x ↦ (1 / 2) min ((x + 1)^2, (x - 1)^2)` from the exercise, valued in
`ℝ≥0∞`. -/
def twoWellQuadraticRateFunction (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (((1 : ℝ) / 2) * min ((x + 1) ^ (2 : ℕ)) ((x - 1) ^ (2 : ℕ)))

-- Proof sketch: unfold `twoPointGaussianMixtureMeasureFamily`; this is exactly the textbook definition of the
-- Gaussian mixture `μ_ε`.
/-- Expanding `twoPointGaussianMixtureMeasureFamily` gives the explicit symmetric mixture of the two Gaussian
laws centered at `-1` and `1` with variance parameter `ε`. -/
theorem twoPointGaussianMixtureMeasureFamily_def (ε : PositiveParameter) :
    twoPointGaussianMixtureMeasureFamily ε =
      (1 / 2 : ℝ≥0∞) • gaussianReal (-1) (Real.toNNReal ε) +
        (1 / 2 : ℝ≥0∞) • gaussianReal 1 (Real.toNNReal ε) := sorry

/-- Each Gaussian mixture `μ_ε` is a probability measure. -/
theorem twoPointGaussianMixtureMeasureFamily_isProbabilityMeasure (ε : PositiveParameter) :
    IsProbabilityMeasure (twoPointGaussianMixtureMeasureFamily ε) := by
  refine ⟨by
    simp [twoPointGaussianMixtureMeasureFamily, one_div, ENNReal.inv_two_add_inv_two]
  ⟩

-- Proof sketch: unfold `twoWellQuadraticRateFunction`; the statement is exactly the explicit formula
-- displayed in the exercise, rewritten as an `ℝ≥0∞`-valued function.
/-- Expanding `twoWellQuadraticRateFunction` gives the explicit formula
`x ↦ (1 / 2) min ((x + 1)^2, (x - 1)^2)`. -/
theorem twoWellQuadraticRateFunction_def (x : ℝ) :
    twoWellQuadraticRateFunction x =
      ENNReal.ofReal (((1 : ℝ) / 2) * min ((x + 1) ^ (2 : ℕ)) ((x - 1) ^ (2 : ℕ))) := sorry

/-- The two-well quadratic rate function is a good rate function on `ℝ`. -/
instance instIsGoodRateFunctionTwoWellQuadraticRateFunction :
    IsGoodRateFunction twoWellQuadraticRateFunction := sorry

-- Proof sketch: on each side of the origin, the family is a small-variance Gaussian perturbation
-- of one of the two atoms `-1` and `1`, so the local Gaussian LDP gives the quadratic costs
-- `(x + 1)^2 / 2` and `(x - 1)^2 / 2`; exponential asymptotics for the symmetric mixture are then
-- governed by the larger exponential term, which yields the minimum of the two costs.
/-- Exercise 23.2.3: the family
`μ_ε = (1 / 2) N(-1, ε) + (1 / 2) N(1, ε)` satisfies the large deviations principle on `ℝ` as
`ε ↓ 0`, with rate function `x ↦ (1 / 2) min ((x + 1)^2, (x - 1)^2)`. -/
theorem gaussianMixture_smallVariance_satisfiesLDP :
    HasLargeDeviationsPrinciple
      (fun ε ↦
        ⟨twoPointGaussianMixtureMeasureFamily ε,
          twoPointGaussianMixtureMeasureFamily_isProbabilityMeasure ε⟩)
      twoWellQuadraticRateFunction := sorry

end ProbabilityTheory

/-! ### Exercise_23_2_4 (from Items/Chap23) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

-- Helper for the source-facing rate formula below: evaluate the exponential moment of
-- `expMeasure θ` by the standard density integral on `(0, ∞)`, obtaining `θ / (θ - t)`, and then
-- pass to the chapter owner `extendedLogMomentGeneratingFunction`.
private theorem extendedLogMomentGeneratingFunction_id_expMeasure_of_lt
    {θ t : ℝ} (hθ : 0 < θ) (ht : t < θ) :
    Λ(id; expMeasure θ) t = Real.log (θ / (θ - t)) := by
  letI : IsProbabilityMeasure (expMeasure θ) := isProbabilityMeasure_expMeasure hθ
  have hmgf : mgf id (expMeasure θ) t = θ / (θ - t) :=
    expMeasure_mgf_eq θ hθ ht
  have hmgf_pos : 0 < mgf id (expMeasure θ) t := by
    rw [hmgf]
    exact div_pos hθ (sub_pos.mpr ht)
  have ht_mem : t ∈ integrableExpSet id (expMeasure θ) :=
    (mgf_pos_iff).1 hmgf_pos
  calc
    Λ(id; expMeasure θ) t = (cgf id (expMeasure θ) t : EReal) := by
      simpa using
        extendedLogMomentGeneratingFunction_eq_cgf_of_mem_integrableExpSet
          id (expMeasure θ) ht_mem
    _ = Real.log (θ / (θ - t)) := by
      rw [cgf, hmgf]

-- Helper for the source-facing rate formula below: when `t ≥ θ`, the exponential moment
-- diverges, so the chapter owner `extendedLogMomentGeneratingFunction` takes the value `∞`.
private theorem extendedLogMomentGeneratingFunction_id_expMeasure_of_ge
    {θ t : ℝ} (hθ : 0 < θ) (ht : θ ≤ t) :
    Λ(id; expMeasure θ) t = ⊤ := by
  simpa using
    extendedLogMomentGeneratingFunction_eq_top_of_not_mem_integrableExpSet
      id (expMeasure θ) (expMeasure_not_mem_integrableExpSet_of_ge θ hθ ht)

-- Proof sketch: split on `0 < x`; on the positive branch, substitute the explicit optimizer
-- `t = θ - 1 / x` into the Legendre transform of `Λ`, and on the nonpositive branch use that the
-- supremum diverges to `∞`.
/-- Exercise 23.2.4: for the exponential law with rate `θ`, the Legendre transform `Λ*` is
`x ↦ θ x - log (θ x) - 1` on `(0, ∞)` and `∞` on `(-∞, 0]`. -/
theorem legendreFenchelRateFunction_id_expMeasure_eq
    {θ x : ℝ} (hθ : 0 < θ) :
    legendreFenchelRateFunction (Λ(id; expMeasure θ)) x =
      if 0 < x then ((θ * x - Real.log (θ * x) - 1 : ℝ) : EReal) else ⊤ := sorry

-- Proof sketch: on `(0, ∞)`, differentiate `x ↦ θ x - log (θ x) - 1` and solve
-- `θ - 1 / x = 0`, obtaining `x = 1 / θ`; strict convexity then shows this is the unique zero.
/-- The exponential-law Legendre transform has its unique zero at the mean `1 / θ` of `Exp(θ)`. -/
theorem legendreFenchelRateFunction_id_expMeasure_eq_zero_iff {θ x : ℝ} (hθ : 0 < θ) :
    legendreFenchelRateFunction (Λ(id; expMeasure θ)) x = 0 ↔ x = 1 / θ := sorry

-- `bridge/view` layer: the source-facing exercise statement specializes the Chapter 23 owner
-- theorem `cramer_empiricalMean_largeDeviationPrinciple` to the exponential law and then rewrites
-- the rate through the chapter owner `legendreFenchelRateFunction (Λ(id; expMeasure θ))`, whose
-- explicit source-facing formula is recorded above.
/-- For an i.i.d. sequence with common law `Exp(θ)`, the normalized partial sums satisfy the large
deviation principle with the canonical Chapter 23 rate function
`legendreFenchelRateFunction (Λ(id; expMeasure θ))`. The companion theorem
`legendreFenchelRateFunction_id_expMeasure_eq` records the textbook explicit formula for this
rate. -/
theorem normalizedPartialSumLaw_satisfiesLargeDeviationPrinciple_of_hasLaw_expMeasure
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {θ : ℝ}
    (hθ : 0 < θ) (hX_iid : IsIID X P)
    (hX0_law : HasLaw (X 0) (expMeasure θ) P) :
    SatisfiesLargeDeviationPrinciple (normalizedPartialSumLaw X P)
      (legendreFenchelRateFunction (Λ(id; expMeasure θ))) := sorry

end ProbabilityTheory

/-! ### Exercise_23_2_5 (from Items/Chap23) -/
open scoped ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

/-- At the origin, the chapter's extended logarithmic moment-generating function of a Cauchy law
equals `0`. -/
theorem cauchyMeasure_extendedLogMomentGeneratingFunction_zero
    (x₀ : ℝ) (γ : NNReal) :
    Λ(id; cauchyMeasure x₀ γ) 0 = 0 := sorry

-- Proof sketch: for every nonzero `t`, one of the tails of `exp (t x)` against a nondegenerate
-- Cauchy density is nonintegrable, so the chapter's extended logarithmic moment-generating
-- function takes the value `⊤`.
/-- Away from the origin, the chapter's extended logarithmic moment-generating function of a
nondegenerate Cauchy law equals `⊤`. -/
theorem cauchyMeasure_extendedLogMomentGeneratingFunction_eq_top
    (x₀ : ℝ) {γ : NNReal} (hγ : γ ≠ 0) {t : ℝ} (ht : t ≠ 0) :
    Λ(id; cauchyMeasure x₀ γ) t = ⊤ := sorry

-- Proof sketch: after substituting the explicit Cauchy formula for `Λ`, every term with `t ≠ 0`
-- becomes `-∞`, while the term `t = 0` contributes `0`; hence the supremum defining the
-- Legendre-Fenchel transform is `0` for every `x`.
/-- Exercise 23.2.5: for a nondegenerate Cauchy law, the chapter's extended logarithmic
moment-generating function is `Λ(0) = 0` and `Λ(t) = ⊤` for `t ≠ 0`, so its Legendre-Fenchel
transform is the trivial rate function `Λ*(x) = 0` for every `x`. This means that Theorem 23.11
yields only the degenerate large-deviation picture with zero exponential rate in the Cauchy
case. -/
theorem cauchyMeasure_legendreFenchelRateFunction_eq_zero
    (x₀ : ℝ) {γ : NNReal} (hγ : γ ≠ 0) (x : ℝ) :
    legendreFenchelRateFunction (Λ(id; cauchyMeasure x₀ γ)) x = 0 := sorry

end ProbabilityTheory

/-! ### Exercise_23_2_6 (from Items/Chap23) -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

noncomputable section

namespace ProbabilityTheory

private def poissonScaling (ε : PositiveParameter) : ℕ → ℝ :=
  fun n ↦ ε * (n : ℝ)

private theorem poissonScaling_measurable (ε : PositiveParameter) :
    Measurable (poissonScaling ε) :=
  measurable_of_countable (poissonScaling ε)

/-- The family `μ_ε` obtained by pushing forward the Poisson law with parameter `λ / ε` under the
scaling map `n ↦ ε n`. -/
def poissonScaledLaw (lam : ℝ) : PositiveProbabilityFamily ℝ :=
  fun ε ↦
    ProbabilityMeasure.map
      (⟨poissonMeasure (Real.toNNReal (lam / (ε : ℝ))), inferInstance⟩ : ProbabilityMeasure ℕ)
      (poissonScaling_measurable ε).aemeasurable

/-- The Poisson Cramér rate function `x log (x / λ) + λ - x` on `[0, ∞)` and `∞` on `(-∞, 0)`. -/
def poissonScaledRateFunction (lam : ℝ) (x : ℝ) : ENNReal :=
  if 0 ≤ x then ENNReal.ofReal (x * Real.log (x / lam) + lam - x) else ⊤

-- Proof sketch: unfold `poissonScaledRateFunction`; under the hypothesis `0 ≤ x`, the defining
-- `if` takes its finite branch.
/-- On `[0, ∞)`, `poissonScaledRateFunction` is given by the explicit Poisson entropy formula. -/
theorem poissonScaledRateFunction_of_nonneg (lam : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    poissonScaledRateFunction lam x = ENNReal.ofReal (x * Real.log (x / lam) + lam - x) := sorry

-- Proof sketch: verify lower semicontinuity of the explicit formula on `[0, ∞)`, show that every
-- finite sublevel set is closed and bounded, and conclude compactness by Heine-Borel.
/-- The explicit Poisson Cramér rate function is a good rate function for every positive
parameter `λ`. -/
theorem poissonScaledRateFunction_isGoodRateFunction {lam : ℝ} (hlam : 0 < lam) :
    IsGoodRateFunction (poissonScaledRateFunction lam) := sorry

-- Proof sketch: compute the logarithmic moment generating function of `ε X_(λ / ε)` from the
-- Poisson law, identify its Legendre transform as `poissonScaledRateFunction lam`, and then apply
-- the chapter's large-deviation theorem for exponentially tilted logarithmic moment generating
-- functions.
/-- Exercise 23.2.6: for `λ > 0`, the laws `μ_ε = P_(ε X_(λ / ε))` satisfy the large deviations
principle on `ℝ` with rate function `x log (x / λ) + λ - x` for `x ≥ 0` and `∞` for `x < 0`. -/
theorem poissonScaledLaw_satisfiesLDPWithRate {lam : ℝ} (hlam : 0 < lam) :
    HasLargeDeviationsPrinciple
      (poissonScaledLaw lam)
      (poissonScaledRateFunction lam) := sorry

end ProbabilityTheory

/-! ### Exercise_23_2_7 (from Items/Chap23) -/
open MeasureTheory Set
open scoped ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

private def rescaledWalkTime (ε : PositiveParameter) : NNReal :=
  Real.toNNReal ε⁻¹

/-- The rescaled position map `ω ↦ ε X_{1 / ε}(ω)` of the continuous-time symmetric walk. -/
def continuousTimeSymmetricRandomWalkRescaled
    (X : NNReal → Ω → ℤ) (ε : PositiveParameter) : Ω → ℝ :=
  fun ω ↦ ε * (X (rescaledWalkTime ε) ω : ℝ)

/-- The increment law at time `t` of the continuous-time symmetric random walk on `ℤ`, realized as
the difference of two independent Poisson variables with common parameter `t / 2`. -/
def continuousTimeSymmetricRandomWalkIncrementLaw (t : NNReal) : ProbabilityMeasure ℤ :=
  ⟨((poissonPMF (t / 2)).bind fun n ↦
      (poissonPMF (t / 2)).map fun m ↦ (n : ℤ) - m).toMeasure,
    inferInstance⟩

/-- A process on `ℤ` is the continuous-time symmetric random walk when it starts at `0`, has
independent increments, and each increment over `(s,t]` has the canonical symmetric
difference-of-Poisson law with jump rates `1 / 2` to the right and left. -/
class IsContinuousTimeSymmetricRandomWalk
    (μ : Measure Ω) (X : NNReal → Ω → ℤ) : Prop where
  /-- The walk is a stochastic process. -/
  stochastic : IsStochasticProcess X
  /-- The walk starts from the origin. -/
  zero : X 0 = 0
  /-- The walk has independent increments. -/
  indepIncrements : HasIndepIncrements X μ
  /-- The increment over `(s,t]` has the canonical symmetric continuous-time random-walk law. -/
  increment_law :
    ∀ ⦃s t : NNReal⦄, s ≤ t →
      HasLaw
        (fun ω ↦ X t ω - X s ω)
        (continuousTimeSymmetricRandomWalkIncrementLaw (t - s))
        μ

namespace IsContinuousTimeSymmetricRandomWalk

/-- Every time slice of a continuous-time symmetric random walk is measurable. -/
theorem measurable
    {μ : Measure Ω} {X : NNReal → Ω → ℤ}
    (hX : IsContinuousTimeSymmetricRandomWalk μ X) (t : NNReal) :
    Measurable (X t) :=
  hX.stochastic t

/-- The increment law forces the underlying measure of a continuous-time symmetric random walk to
be a probability measure. -/
theorem isProbabilityMeasure
    {μ : Measure Ω} {X : NNReal → Ω → ℤ}
    (hX : IsContinuousTimeSymmetricRandomWalk μ X) :
    IsProbabilityMeasure μ := by
  exact (hX.increment_law (show (0 : NNReal) ≤ 1 by norm_num)).isProbabilityMeasure

end IsContinuousTimeSymmetricRandomWalk

/-- The rescaled position map `ω ↦ ε X_{1 / ε}(ω)` is measurable when the coordinate maps of `X`
are measurable. -/
theorem measurable_continuousTimeSymmetricRandomWalkRescaled
    (X : NNReal → Ω → ℤ) (hXmeas : ∀ t, Measurable (X t)) (ε : PositiveParameter) :
    Measurable (continuousTimeSymmetricRandomWalkRescaled X ε) := by
  have hcast : Measurable (fun z : ℤ ↦ (z : ℝ)) :=
    measurable_of_countable (fun z : ℤ ↦ (z : ℝ))
  simpa [continuousTimeSymmetricRandomWalkRescaled] using
    measurable_const.mul (hcast.comp <| hXmeas (rescaledWalkTime ε))

/-- The law family `ε ↦ P_{ε X_{1/ε}}` of the rescaled continuous-time walk on the positive
parameter space `ε > 0`, built from the source-facing owner
`IsContinuousTimeSymmetricRandomWalk μ X`. -/
def continuousTimeSymmetricRandomWalkRescaledLaw
    (μ : Measure Ω) (X : NNReal → Ω → ℤ)
    (hX : IsContinuousTimeSymmetricRandomWalk μ X) :
    PositiveProbabilityFamily ℝ :=
  letI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  fun ε ↦
    ProbabilityMeasure.map ⟨μ, inferInstance⟩
      (measurable_continuousTimeSymmetricRandomWalkRescaled X hX.measurable ε).aemeasurable

/-- The candidate good rate function
`x ↦ 1 + x arsinh(x) - sqrt (1 + x^2)`, viewed as an `ℝ≥0∞`-valued map. -/
def continuousTimeSymmetricRandomWalkRateFunction (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 + x * Real.arsinh x - Real.sqrt (1 + x ^ (2 : ℕ)))

-- Proof sketch: unfold `continuousTimeSymmetricRandomWalkRescaledLaw`; it is the pushforward of
-- `P` by the map `ω ↦ ε * X_(1 / ε)(ω)` with the chapter's `NNReal` time parameter
-- `rescaledWalkTime ε`.
/-- Expanding `continuousTimeSymmetricRandomWalkRescaledLaw` gives the pushforward law of the
rescaled position `ε X_{1/ε}`. -/
theorem continuousTimeSymmetricRandomWalkRescaledLaw_def
    (μ : Measure Ω) (X : NNReal → Ω → ℤ)
    (hX : IsContinuousTimeSymmetricRandomWalk μ X) (ε : PositiveParameter) :
    continuousTimeSymmetricRandomWalkRescaledLaw μ X hX ε =
      ProbabilityMeasure.map ⟨μ, hX.isProbabilityMeasure⟩
        (measurable_continuousTimeSymmetricRandomWalkRescaled X hX.measurable ε).aemeasurable := by
  letI : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  rfl

-- Proof sketch: unfold `continuousTimeSymmetricRandomWalkRateFunction`; this is exactly the
-- explicit formula displayed in the exercise, rewritten as an `ℝ≥0∞`-valued map.
/-- Expanding `continuousTimeSymmetricRandomWalkRateFunction` gives the explicit textbook formula
`x ↦ 1 + x arsinh(x) - sqrt (1 + x^2)`. -/
theorem continuousTimeSymmetricRandomWalkRateFunction_def (x : ℝ) :
    continuousTimeSymmetricRandomWalkRateFunction x =
      ENNReal.ofReal (1 + x * Real.arsinh x - Real.sqrt (1 + x ^ (2 : ℕ))) := rfl

-- Proof sketch: the real-valued branch is continuous and coercive, so the `ℝ≥0∞`-valued rate
-- function is lower semicontinuous and its finite sublevel sets are compact in `ℝ`.
/-- The explicit rate function of the rescaled continuous-time symmetric walk is a good rate
function on `ℝ`. -/
instance continuousTimeSymmetricRandomWalkRateFunction_isGoodRateFunction :
    IsGoodRateFunction continuousTimeSymmetricRandomWalkRateFunction := sorry

-- Proof sketch: compute the second derivative of the real-valued branch
-- `x ↦ 1 + x arsinh(x) - sqrt (1 + x^2)` as `(1 + x^2)^(-1/2)`, which is nonnegative on `ℝ`,
-- and conclude convexity on the whole line.
/-- The finite real-valued branch of the rate function is convex on `ℝ`. -/
theorem continuousTimeSymmetricRandomWalkRateFunction_convex :
    ConvexOn ℝ univ
      (fun x : ℝ ↦ 1 + x * Real.arsinh x - Real.sqrt (1 + x ^ (2 : ℕ))) := sorry

/-- A Poisson right/left decomposition is a bridge to the intrinsic owner
`IsContinuousTimeSymmetricRandomWalk`. -/
theorem isContinuousTimeSymmetricRandomWalk_of_eq_poissonDifference
    (μ : Measure Ω) (X : NNReal → Ω → ℤ)
    {Nright Nleft : NNReal → Ω → ℕ}
    (hNright : IsPoissonProcess (1 / 2 : NNReal) μ Nright)
    (hNleft : IsPoissonProcess (1 / 2 : NNReal) μ Nleft)
    (hindep : IndepFun (fun ω t ↦ Nright t ω) (fun ω t ↦ Nleft t ω) μ)
    (hX : X = fun t ω ↦ (Nright t ω : ℤ) - Nleft t ω) :
    IsContinuousTimeSymmetricRandomWalk μ X := sorry

-- Proof sketch: compute the logarithmic moment generating function of the canonical increment law,
-- identify its Legendre transform as the explicit rate function below, and apply the chapter's
-- large-deviation theorem to the rescaled one-time marginals of the continuous-time symmetric
-- random walk.
/-- Exercise 23.2.7: for a continuous-time symmetric random walk on `ℤ` with jump rates `1 / 2`
to the right and left, the family of laws `P_{ε X_{1/ε}}` satisfies the large deviations
principle as `ε ↓ 0`, with rate function
`I(x) = 1 + x arsinh(x) - sqrt (1 + x^2)`. -/
theorem continuousTimeSymmetricRandomWalk_rescaled_satisfiesLDP
    (μ : Measure Ω)
    (X : NNReal → Ω → ℤ)
    (hX : IsContinuousTimeSymmetricRandomWalk μ X) :
    HasLargeDeviationsPrinciple
      (continuousTimeSymmetricRandomWalkRescaledLaw μ X hX)
      continuousTimeSymmetricRandomWalkRateFunction := sorry

/-- Bridge form of Exercise 23.2.7: a Poisson right/left decomposition yields the intrinsic
continuous-time symmetric random-walk hypothesis, so the LDP follows from the source-facing owner
theorem. -/
theorem continuousTimeSymmetricRandomWalk_rescaled_satisfiesLDP_of_eq_poissonDifference
    (μ : Measure Ω)
    (X : NNReal → Ω → ℤ)
    {Nright Nleft : NNReal → Ω → ℕ}
    (hNright : IsPoissonProcess (1 / 2 : NNReal) μ Nright)
    (hNleft : IsPoissonProcess (1 / 2 : NNReal) μ Nleft)
    (hindep : IndepFun (fun ω t ↦ Nright t ω) (fun ω t ↦ Nleft t ω) μ)
    (hX : X = fun t ω ↦ (Nright t ω : ℤ) - Nleft t ω) :
    HasLargeDeviationsPrinciple
      (continuousTimeSymmetricRandomWalkRescaledLaw μ X
        (isContinuousTimeSymmetricRandomWalk_of_eq_poissonDifference
          μ X hNright hNleft hindep hX))
      continuousTimeSymmetricRandomWalkRateFunction := by
  exact continuousTimeSymmetricRandomWalk_rescaled_satisfiesLDP
    μ X
    (isContinuousTimeSymmetricRandomWalk_of_eq_poissonDifference
      μ X hNright hNleft hindep hX)

end ProbabilityTheory
