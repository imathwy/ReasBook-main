import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_21_2_1 (from Items/Chap21) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u}

local notation "nonnegativeLebesgue" => volume.restrict (Set.Ici (0 : ℝ))

section BrownianMotionExercise

variable [MeasurableSpace Ω]
variable {μ : Measure Ω}
variable {B : NNReal → Ω → ℝ}

-- Proof sketch: write the average as a centered Gaussian linear functional of the Brownian path.
-- Fubini and the Brownian covariance kernel `min(s,t)` give expectation `0` and covariance
-- integral `∫₀¹∫₀¹ min(s,t) ds dt = 1/3`; the expectation statement is the first moment
-- computation.
/-- Exercise 21.2.1 (1): item (i), the expectation of the Brownian sample-path average over
`[0,1]` is zero. -/
theorem brownianUnitIntervalAverage_expectation (hB : IsBrownianMotion μ B) :
    ∫ ω, (∫ t in (0 : ℝ)..1, B (Real.toNNReal t) ω) ∂μ = 0 := sorry

-- Proof sketch: the same covariance computation as in part (i) shows that
-- `Var[∫₀¹ B_s ds] = ∫₀¹∫₀¹ min(s,t) ds dt = 1/3`.
/-- Exercise 21.2.1 (2): item (i), the variance of the Brownian sample-path average over `[0,1]`
is `1 / 3`. -/
theorem brownianUnitIntervalAverage_variance (hB : IsBrownianMotion μ B) :
    Var[fun ω ↦ ∫ t in (0 : ℝ)..1, B (Real.toNNReal t) ω; μ] = 1 / 3 := sorry

-- Proof sketch: almost every Brownian sample path is continuous, so its zero set is closed. A
-- nontrivial interval of zeros would force a constant segment and hence violate the Gaussian
-- increment law; cover the zero set by intervals on which oscillation is small and conclude it has
-- Lebesgue measure zero.
/-- Exercise 21.2.1 (3): item (ii), almost every Brownian sample path has zero set of Lebesgue
measure zero on `[0, ∞)`, modeled here by Lebesgue measure on `ℝ` restricted to `Set.Ici 0`. -/
theorem brownianZeroSet_volume_eq_zero_ae (hB : IsBrownianMotion μ B) :
    ∀ᵐ ω ∂μ, nonnegativeLebesgue {t : ℝ | B (Real.toNNReal t) ω = 0} = 0 := sorry

-- Proof sketch: expand the square, use linearity of expectation, and evaluate the resulting
-- covariance integrals for `B_t` and the path average. This yields
-- `∫₀¹ E[(B_t - ∫₀¹ B_s ds)^2] dt = 1/6`.
/-- Exercise 21.2.1 (4): item (iii), the expectation of the integrated squared deviation from the
unit-interval Brownian average is `1 / 6`. -/
theorem brownianUnitIntervalCenteredQuadraticDeviation_expectation (hB : IsBrownianMotion μ B) :
    ∫ ω, (∫ t in (0 : ℝ)..1,
      (B (Real.toNNReal t) ω - ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω) ^ 2) ∂μ = 1 / 6 := sorry

-- Proof sketch: the centered process `t ↦ B_t - ∫₀¹ B_s ds` is Gaussian with explicit covariance
-- kernel. For a centered Gaussian process, the variance of the integrated square is
-- `2 ∫₀¹∫₀¹ K(s,t)^2 ds dt`, and evaluating this kernel integral gives `1/45`.
/-- Exercise 21.2.1 (5): item (iii), the variance of the integrated squared deviation from the
unit-interval Brownian average is `1 / 45`. -/
theorem brownianUnitIntervalCenteredQuadraticDeviation_variance (hB : IsBrownianMotion μ B) :
    Var[fun ω ↦ ∫ t in (0 : ℝ)..1,
      (B (Real.toNNReal t) ω - ∫ s in (0 : ℝ)..1, B (Real.toNNReal s) ω) ^ 2; μ] = 1 / 45 := sorry

end BrownianMotionExercise

end ProbabilityTheory

/-! ### Definition_21_2 (from Items/Chap21) -/
universe u v

open scoped NNReal Topology

section HolderAt

variable {X : Type u} {Y : Type v} [PseudoMetricSpace X] [PseudoMetricSpace Y]
variable {γ : Set.Ioc (0 : ℝ≥0) 1} {f : X → Y} {x : X}

/-- Definition 21.2 (1): a map is Hölder-continuous of order `γ ∈ (0,1]` at the point `r` if
there are a radius `ε > 0` and a finite Hölder constant `C` such that nearby points satisfy the
textbook inequality `dist (φ r) (φ s) ≤ C * dist r s ^ γ`. -/
def HolderContinuousAt (γ : Set.Ioc (0 : ℝ≥0) 1) (f : X → Y) (x : X) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ≥0, ∀ y : X, dist y x < ε →
    dist (f x) (f y) ≤ C * dist x y ^ (γ : ℝ)

/-- A Hölder-continuous map at a point admits a positive-radius neighborhood and a finite Hölder
constant controlling the oscillation from the center point. -/
theorem HolderContinuousAt.exists_dist_le_mul_rpow (hf : HolderContinuousAt γ f x) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ≥0, ∀ y : X, dist y x < ε →
      dist (f x) (f y) ≤ C * dist x y ^ (γ : ℝ) :=
  hf

end HolderAt

section LocalHolder

variable {X : Type u} {Y : Type v} [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-- A map is locally Hölder of exponent `r` if every point has a neighborhood on which it is
Hölder with exponent `r` and some local Hölder constant. -/
def LocallyHolderWith (r : ℝ≥0) (f : X → Y) : Prop :=
  ∀ x : X, ∃ s : Set X, s ∈ 𝓝 x ∧ ∃ C : ℝ≥0, HolderOnWith C r f s

-- Proof sketch: use the whole space as the neighborhood of each point and keep the same Hölder
-- constant.
/-- A globally Hölder map is locally Hölder with the same exponent. -/
theorem HolderWith.locallyHolderWith
    {C r : ℝ≥0} {f : X → Y} (hf : HolderWith C r f) :
    LocallyHolderWith r f := sorry

end LocalHolder

section MetricLocalHolder

variable {X : Type u} {Y : Type v} [MetricSpace X] [PseudoMetricSpace Y]

/- Definition 21.2 (2): local Hölder continuity is the canonical owner predicate
`LocallyHolderWith`. -/
#check LocallyHolderWith

/-- In a metric space, a locally Hölder map admits a Hölder estimate on some open ball around each
point. -/
theorem LocallyHolderWith.exists_holderOnWith_ball {r : ℝ≥0} {f : X → Y}
    (hf : LocallyHolderWith r f) (x : X) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ≥0, HolderOnWith C r f (Metric.ball x ε) := sorry

end MetricLocalHolder

section GlobalHolder

variable {X : Type u} {Y : Type v} [PseudoMetricSpace X] [PseudoMetricSpace Y]
variable (γ : Set.Ioc (0 : ℝ≥0) 1) (f : X → Y)

/- Definition 21.2 (3): global Hölder continuity of order `γ` is the existence of a
`HolderWith` constant. -/
#check (∃ C : ℝ≥0, HolderWith C γ f)

end GlobalHolder

/-! ### Exercise_21_2_2 (from Items/Chap21) -/
open MeasureTheory

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} {B : NNReal → Ω → ℝ}

-- Proof sketch: for `s ≤ t`, write `B t = B s + (B t - B s)`. Brownian increments after time `s`
-- are independent of the natural filtration up to time `s`, centered, and have variance `t - s`.
-- Expanding the square and taking the conditional expectation therefore gives
-- `E[B_t^2 - t | 𝓕_s] = B_s^2 - s`.
/-- Exercise 21.2.2: for a Brownian motion `B`, the compensated squared process
`(B_t^2 - t)_{t ≥ 0}` is a martingale with respect to the natural filtration generated by `B`. -/
theorem brownian_sq_sub_time_martingale
    (hB : IsBrownianMotion μ B) :
    Martingale (fun t ω ↦ B t ω ^ 2 - (t : ℝ))
      (Filtration.natural B hB.stronglyMeasurable) μ := sorry

end ProbabilityTheory

/-! ### Exercise_21_2_3 (from Items/Chap21) -/
open MeasureTheory ProbabilityTheory

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: for `s ≤ t`, split the exponent into the time-`s` part and the increment
-- `B_t - B_s`. Brownian independent increments imply that this increment is independent of the
-- natural filtration up to time `s`, while its centered Gaussian law gives expectation
-- `exp ((σ^2 / 2) * (t - s))`. This exactly cancels the compensator, yielding the martingale
-- conditional-expectation identity.
/-- Exercise 21.2.3: for a Brownian motion `B`, the process
`t ↦ exp (σ B_t - (σ^2 / 2) t)` is a martingale with respect to the natural filtration generated
by `B`. -/
theorem brownianStochasticExponential_martingale
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) (σ : ℝ) :
    Martingale
      (fun t ω ↦ Real.exp (σ * B t ω - (σ ^ 2 / 2) * (t : ℝ)))
      (Filtration.natural B hB.stronglyMeasurable)
      μ := sorry

end ProbabilityTheory

/-! ### Exercise_21_2_4 (from Items/Chap21) -/
open MeasureTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: use recurrence of one-dimensional Brownian motion together with continuity of the
-- sample paths to show that one of the two boundary levels is hit in finite time almost surely.
/-- Exercise 21.2.4 (1): for a Brownian motion and levels `a < 0 < b`, the first hitting time of
the boundary set `{a, b}` is almost surely finite. -/
theorem brownianMotion_twoSidedHittingTime_ae_ne_top
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {a b : ℝ} (ha : a < 0) (hb : 0 < b) :
    ∀ᵐ ω ∂μ, hittingAfter B ({a, b} : Set ℝ) 0 ω ≠ ⊤ := sorry

-- Proof sketch: apply optional stopping to the Brownian martingale `t ↦ B t` at the exit time
-- `τ_{a,b}`. Since the stopped value can only be `a` or `b`, the mean-zero identity yields the
-- affine equation determining the probability of exiting through `b`.
/-- Exercise 21.2.4 (2): the probability that Brownian motion exits the interval `(a, b)` through
the upper endpoint `b` is `-a / (b - a)`. -/
theorem brownianMotion_twoSidedHittingTime_prob_hit_right
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {a b : ℝ} (ha : a < 0) (hb : 0 < b) :
    μ {ω | stoppedValue B (hittingAfter B ({a, b} : Set ℝ) 0) ω = b} =
      ENNReal.ofReal (-a / (b - a)) := sorry

-- Proof sketch: use Exercise 21.2.2 for the martingale `t ↦ B t ^ 2 - t`, stop at `τ_{a,b}`,
-- insert the almost-sure identity `B_{τ_{a,b}} ∈ {a, b}`, and combine it with the exit
-- probability from the previous clause to compute the expected stopping time.
/-- Exercise 21.2.4 (3): the expectation of the two-sided Brownian hitting time `τ_{a,b}` is
`-ab`. -/
theorem brownianMotion_twoSidedHittingTime_expectation_eq
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {a b : ℝ} (ha : a < 0) (hb : 0 < b) :
    ∫ ω, ENNReal.toReal (hittingAfter B ({a, b} : Set ℝ) 0 ω) ∂μ = -a * b := sorry

end ProbabilityTheory

/-! ### Exercise_21_2_5 (from Items/Chap21) -/
open MeasureTheory ProbabilityTheory MeasureTheory.ProbabilityMeasure
open scoped ENNReal NNReal Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The first time at which the Brownian path `t ↦ B t ω` hits the level `b`. -/
def brownianLevelHittingTime (B : NNReal → Ω → ℝ) (b : ℝ) : Ω → ENNReal :=
  hittingAfter B ({b} : Set ℝ) (0 : NNReal)

-- Proof sketch: `brownianLevelHittingTime` is exactly the canonical hitting time `hittingAfter`
-- for the Brownian path into the singleton level set `{b}`.
omit [MeasurableSpace Ω] in
/-- Expanding `brownianLevelHittingTime` gives the canonical owner `hittingAfter` for the
Brownian path at level `b`. -/
theorem brownianLevelHittingTime_eq_hittingAfter
    (B : NNReal → Ω → ℝ) (b : ℝ) :
    brownianLevelHittingTime B b =
      hittingAfter B ({b} : Set ℝ) (0 : NNReal) := by
  rfl

/- For this item:
- `source-facing`: `brownianLevelHittingTime B b`, the singleton specialization of the canonical
  hitting-time owner `hittingAfter`.
- `core/canonical`: `brownianLevelHittingTimeLaw hB b : ProbabilityMeasure ℝ`, since the stable-law
  and Lévy--Khintchine APIs in chapter 16 are owned by `ProbabilityMeasure ℝ`.
- `bridge/view`: the underlying `Measure ℝ` of that probability law and the `toReal` model of the
  extended-valued hitting time; for `b > 0`, the companion finiteness theorem below makes that view
  source-faithful.
-/

/-- The Brownian level-hitting time, viewed as the real-valued random variable
`ω ↦ (τ_b ω).toReal`, is measurable. -/
theorem aemeasurable_brownianLevelHittingTime_toReal
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) (b : ℝ) :
    AEMeasurable (fun ω ↦ (brownianLevelHittingTime B b ω).toReal) μ := sorry

/-- For a positive level, Brownian motion hits that level in finite time almost surely. -/
theorem brownianLevelHittingTime_ae_ne_top
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) {b : ℝ} (hb : 0 < b) :
    ∀ᵐ ω ∂μ, brownianLevelHittingTime B b ω ≠ ⊤ := sorry

/-- The canonical `ProbabilityMeasure ℝ` law of the Brownian hitting time `τ_b`, viewed through
the real-valued random variable `ω ↦ (τ_b ω).toReal`. -/
def brownianLevelHittingTimeLaw
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) (b : ℝ) :
    ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map ⟨μ, hB.isProbabilityMeasure⟩
    (aemeasurable_brownianLevelHittingTime_toReal hB b)

/-- Coercing `brownianLevelHittingTimeLaw hB b` to `Measure ℝ` recovers the corresponding
pushforward measure. -/
theorem brownianLevelHittingTimeLaw_toMeasure
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) (b : ℝ) :
    (brownianLevelHittingTimeLaw hB b : Measure ℝ) =
      μ.map (fun ω ↦ (brownianLevelHittingTime B b ω).toReal) :=
  rfl

/-- The density of the first hitting time of level `b` by Brownian motion on `(0, ∞)`. -/
def brownianLevelHittingTimeDensity (b : ℝ) (x : ℝ) : ℝ :=
  if 0 < x then
    (b / Real.sqrt (2 * Real.pi)) * Real.exp (-(b ^ (2 : ℕ)) / (2 * x)) * x ^ (-(3 : ℝ) / 2)
  else
    0

-- Proof sketch: apply the exponential-martingale optional-sampling argument from Exercise
-- 21.2.3 to the stopped process at the level-hitting time, and then let the deterministic
-- localization bound tend to infinity.
/-- Exercise 21.2.5 (1): for `b > 0`, the Laplace transform of the Brownian first hitting time
`τ_b` is `exp (-b * sqrt (2 λ))` for every `λ ≥ 0`. -/
theorem brownianLevelHittingTime_laplaceTransform
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) {b : ℝ} (hb : 0 < b)
    (l : NNReal) :
    ∫ x : ℝ, Real.exp (-((l : ℝ) * x)) ∂(brownianLevelHittingTimeLaw hB b : Measure ℝ) =
      Real.exp (-b * Real.sqrt (2 * (l : ℝ))) := sorry

-- Proof sketch: identify the Laplace transform from part (1) with the characteristic exponent of
-- the positive `1 / 2`-stable law, then read off the corresponding one-sided Lévy measure and the
-- strict-stability scaling relation from the chapter-16 stable-law interface.
/-- Exercise 21.2.5 (2): the law of `τ_b`, viewed as a probability law on `ℝ`, is `1 / 2`-stable;
in a
canonical Lévy--Khintchine representation its Lévy measure is
`stableLevyMeasure (1 / 2) 0 (b / sqrt (2 π))`, i.e. `ν(dx) = (b / sqrt (2π)) x^(-3/2) 1_{x>0}
dx`. -/
theorem brownianLevelHittingTimeLaw_isHalfStable_withLevyMeasure
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) {b : ℝ} (hb : 0 < b) :
    IsStableWithIndex (brownianLevelHittingTimeLaw hB b) (1 / 2 : ℝ) ∧
      ∃ d : ℝ,
        HasLevyKhinchinRepresentation
          (brownianLevelHittingTimeLaw hB b)
          { sigma2 := 0
            b := d
            ν := stableLevyMeasure (1 / 2 : ℝ) 0 (b / Real.sqrt (2 * Real.pi)) } := sorry

-- Proof sketch: invert the Laplace transform from part (1), or equivalently evaluate the
-- density of the positive `1 / 2`-stable law with scale parameter `b / sqrt (2π)` and identify
-- the resulting pushforward law.
/-- Exercise 21.2.5 (3): the law of `τ_b`, viewed as a measure on `ℝ`, has density
`f_b(x) = (b / sqrt (2π)) * exp (-b^2 / (2x)) * x^(-3/2)` on `(0, ∞)`. -/
theorem brownianLevelHittingTimeLaw_toMeasure_eq_withDensity
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) {b : ℝ} (hb : 0 < b) :
    (brownianLevelHittingTimeLaw hB b : Measure ℝ) =
      volume.withDensity (fun x ↦ ENNReal.ofReal (brownianLevelHittingTimeDensity b x)) := sorry

end ProbabilityTheory

/-! ### Exercise_21_2_6 (from Items/Chap21) -/
open MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The first time at which the path of `B` meets the affine boundary `t ↦ a * t + b`. -/
def brownianAffineBoundaryHittingTime (B : NNReal → Ω → ℝ) (a b : ℝ) : Ω → ENNReal :=
  hittingAfter (fun t ω ↦ B t ω - a * (t : ℝ)) ({b} : Set ℝ) (0 : NNReal)

-- Proof sketch: `brownianAffineBoundaryHittingTime` is the canonical hitting time `hittingAfter`
-- for the drifted process `t ↦ B_t - a t` into the singleton level `{b}`.
omit [MeasurableSpace Ω] in
/-- Expanding `brownianAffineBoundaryHittingTime` gives the canonical owner `hittingAfter` for the
drifted process `t ↦ B_t - a t` at the level `b`. -/
theorem brownianAffineBoundaryHittingTime_eq_hittingAfter
    (B : NNReal → Ω → ℝ) (a b : ℝ) :
    brownianAffineBoundaryHittingTime B a b =
      hittingAfter (fun t ω ↦ B t ω - a * (t : ℝ)) ({b} : Set ℝ) (0 : NNReal) := by
  rfl

/-- The samplewise factor `e^{-λτ}` attached to the affine-boundary hitting time `τ`, taken to be
`0` on the event that the boundary is never hit. -/
def brownianAffineBoundaryHittingTimeLaplaceWeight
    (B : NNReal → Ω → ℝ) (a b lam : ℝ) : Ω → ℝ :=
  fun ω ↦
    Set.indicator
      {ω | brownianAffineBoundaryHittingTime B a b ω < ⊤}
      (fun ω ↦ Real.exp (-lam * (brownianAffineBoundaryHittingTime B a b ω).toReal)) ω

-- Proof sketch: unfold `brownianAffineBoundaryHittingTimeLaplaceWeight`.
omit [MeasurableSpace Ω] in
/-- The affine-boundary Laplace weight is the exponential factor on the finite-hitting event and
vanishes otherwise. -/
theorem brownianAffineBoundaryHittingTimeLaplaceWeight_def
    (B : NNReal → Ω → ℝ) (a b lam : ℝ) :
    brownianAffineBoundaryHittingTimeLaplaceWeight B a b lam =
      fun ω ↦
        Set.indicator
          {ω | brownianAffineBoundaryHittingTime B a b ω < ⊤}
          (fun ω ↦ Real.exp (-lam * (brownianAffineBoundaryHittingTime B a b ω).toReal)) ω := by
  rfl

section BrownianMotionExercise

variable {μ : Measure Ω}
variable {B : NNReal → Ω → ℝ}

-- Proof sketch: apply exponential martingales to the drifted process `t ↦ B t - a t`, stop at the
-- first hitting time of level `b`, and use optional stopping. Solving the resulting quadratic
-- equation for the martingale parameter yields the exponent
-- `-b * a - b * sqrt (a ^ 2 + 2 * λ)`.
/-- Exercise 21.2.6 (1): for Brownian motion `B`, if `b > 0` and `τ` is the first time with
`B_t = a t + b`, then the Laplace transform of `τ`, interpreted as `0` on the event `{τ = ∞}`,
is `exp (-b a - b sqrt (a^2 + 2 λ))`. -/
theorem brownianAffineBoundaryHittingTime_laplaceTransform
    (hB : IsBrownianMotion μ B) {a b lam : ℝ} (hb : 0 < b) (hlam : 0 ≤ lam) :
    ∫ ω, brownianAffineBoundaryHittingTimeLaplaceWeight B a b lam ω ∂μ =
      Real.exp (-b * a - b * Real.sqrt (a ^ 2 + 2 * lam)) := sorry

-- Proof sketch: specialize part (1) at `λ = 0`. Then the Laplace weight reduces to the indicator
-- of `{τ < ∞}`, and `sqrt (a ^ 2) = |a|`, so the right-hand side becomes `1` when `a ≤ 0` and
-- `exp (-2 * b * a)` when `a > 0`, equivalently `min 1 (exp (-2 * b * a))`.
/-- Exercise 21.2.6 (2): consequently, the probability that the affine boundary `t ↦ a t + b` is
ever hit is `min (1, exp (-2 b a))`. -/
theorem brownianAffineBoundaryHittingTime_lt_top_prob
    (hB : IsBrownianMotion μ B) {a b : ℝ} (hb : 0 < b) :
    μ {ω | brownianAffineBoundaryHittingTime B a b ω < ⊤} =
      ENNReal.ofReal (min 1 (Real.exp (-2 * b * a))) := sorry

end BrownianMotionExercise

end ProbabilityTheory
