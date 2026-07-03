import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_21_3_1 (from Items/Chap21) -/
open MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/- Exercise 21.3.1 concerns the canonical source-facing owner
`IsBrownianMotionStartedAt μ X x`; the translated centered model is only a proof device behind the
reflection argument. The exit time is expressed directly through the canonical hitting-time owner
`hittingAfter` for the Brownian motion started at `x`. -/

section BrownianMotionExercise

variable {μ : Measure Ω}
variable {X : NNReal → Ω → ℝ}

-- Proof sketch: apply the reflection principle to the translated Brownian motion
-- `t ↦ x + B_t`, which starts from `x` and is killed when it reaches `{0, a}`. Iterating the
-- reflections across the endpoints produces the alternating image sum over the strips
-- `[na, (n + 1)a]`.
/-- Exercise 21.3.1 (1): for Brownian motion started at `x ∈ (0, a)`, the probability of staying
inside `(0, a)` up to time `T` is the alternating reflection sum of the terminal interval
probabilities over the strips `[na, (n + 1)a]`. -/
theorem brownianIntervalExitTime_survivalProbability_eq_reflectionSeries
    {a x : ℝ} (hX : IsBrownianMotionStartedAt μ X x) (hx : x ∈ Set.Ioo 0 a) (T : NNReal) :
    μ.real {ω | T < hittingAfter X ({0, a} : Set ℝ) 0 ω} =
      ∑' n : ℤ,
        ((-1 : ℝ) ^ Int.natAbs n) *
          μ.real {ω | X T ω ∈ Set.Icc ((n : ℝ) * a) (((n + 1 : ℤ) : ℝ) * a)} := sorry

end BrownianMotionExercise

-- Proof sketch: periodize the genuine nonnegative density `f`, identify the Fourier coefficients
-- of the periodization by integrating against the complex exponentials, and use the boundedness of
-- `x ↦ x^2 f x` to justify the summation and Fourier-inversion steps. Since mathlib defines
-- `charFun μ t = ∫ exp (t * x * I) dμ`, the Fourier coefficients are sampled at the negative
-- frequencies `-2πk`.
/-- Exercise 21.3.1 (2): if a probability law on `ℝ` has nonnegative density `f`, and if
`x ↦ x^2 f x` is bounded above, then the periodization of `f` is given by the Fourier series built
from the characteristic function `charFun μ`, sampled with the sign convention coming from Lean's
Fourier coefficients. -/
theorem poissonSummationFormula_of_density
    {f : ℝ → ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hμ : μ = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)))
    (hbound : BddAbove (Set.range fun x ↦ x ^ 2 * f x)) (s : ℝ) :
    ((∑' n : ℤ, f (s + n) : ℝ) : ℂ) =
      ∑' k : ℤ,
        charFun μ (-2 * Real.pi * k) * Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * s) := sorry

section BrownianMotionExercise

variable {μ : Measure Ω}
variable {X : NNReal → Ω → ℝ}

-- Proof sketch: start from the reflection-series identity in part (1), identify each strip
-- probability with an integral of the Gaussian density of `x + B_T`, apply the Poisson summation
-- formula from part (2) to that nonnegative Gaussian density, and rewrite the resulting odd
-- Fourier modes as the sine series of the killed heat kernel on `(0, a)`.
/-- Exercise 21.3.1 (3): combining the reflection-series formula with Poisson summation yields the
classical Fourier-sine expansion for the probability that Brownian motion started at
`x ∈ (0, a)` stays inside `(0, a)` up to time `T`. -/
theorem brownianIntervalExitTime_survivalProbability_eq_fourierSineSeries
    {a x : ℝ} (hX : IsBrownianMotionStartedAt μ X x) (hx : x ∈ Set.Ioo 0 a) (T : NNReal) :
    μ.real {ω | T < hittingAfter X ({0, a} : Set ℝ) 0 ω} =
      (4 / Real.pi) *
        ∑' k : ℕ,
          (1 / (2 * k + 1 : ℝ)) *
            Real.exp (-(((2 * k + 1 : ℝ) ^ 2) * Real.pi ^ 2 * T / (2 * a ^ 2))) *
              Real.sin (((2 * k + 1 : ℝ) * Real.pi * x) / a) := sorry

end BrownianMotionExercise

end ProbabilityTheory

/-! ### Lemma_21_3 (from Items/Chap21) -/
open scoped NNReal Topology

section RealLocalHolder

variable {I : Set ℝ} {f : I → ℝ} {γ γ' : Set.Ioc (0 : ℝ≥0) 1} {Cε : ℝ≥0} {ε T : ℝ}

-- Proof sketch: around each point, shrink a local `γ`-Hölder neighborhood to diameter at most
-- `1`, then use monotonicity of the power function on `[0,1]` to replace the exponent `γ` by the
-- smaller exponent `γ'`.
/-- Lemma 21.3 (1): if `f : I → ℝ` is locally Hölder-continuous of order `γ ∈ (0,1]`, then it is
also locally Hölder-continuous of every order `γ' ∈ (0, γ)`. -/
theorem locallyHolderWith_subexponent
    (hf : LocallyHolderWith γ f)
    (hγ'γ : (γ' : ℝ≥0) < γ) :
    LocallyHolderWith γ' f := sorry

-- Proof sketch: choose finitely many local Hölder neighborhoods from compactness, take a Lebesgue
-- number for this finite cover, and bound large distances by the sup norm on the compact domain.
/-- Lemma 21.3 (2): if `I` is compact and `f : I → ℝ` is locally Hölder-continuous of order
`γ ∈ (0,1]`, then `f` is globally Hölder-continuous on `I`. -/
theorem exists_holderWith_of_isCompact
    (hI : IsCompact I)
    (hf : LocallyHolderWith γ f) :
    ∃ C : ℝ≥0, HolderWith C γ f := sorry

-- Proof sketch: subdivide the segment between two points of the interval into
-- `⌈T / ε⌉` subsegments of length at most `ε`, apply the local small-scale Hölder estimate on
-- each subsegment, and sum the resulting bounds.
/-- Lemma 21.3 (3): for an interval `I` of length at most `T`, a small-scale Hölder estimate with
range `ε` upgrades to a global `γ`-Hölder estimate with constant
`Cε * ⌈T / ε⌉ ^ (1 - γ)`. -/
theorem holderWith_of_small_scale_on_interval
    (hI : Convex ℝ I)
    (hT : ∀ s t : I, dist s t ≤ T)
    (hε : 0 < ε)
    (hsmall :
      ∀ s t : I, dist s t ≤ ε → dist (f t) (f s) ≤ Cε * dist s t ^ (γ : ℝ)) :
    HolderWith (Cε * (Nat.ceil (T / ε) : ℝ≥0) ^ (1 - (γ : ℝ≥0) : ℝ)) γ f := sorry

end RealLocalHolder
