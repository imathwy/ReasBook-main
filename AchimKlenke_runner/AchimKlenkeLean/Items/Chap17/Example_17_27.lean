import Mathlib
import AchimKlenkeLean.Items.Chap05.Theorem_5_36
import AchimKlenkeLean.Items.Chap17.Exercise_17_3_2

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

/- Example 17.27 is `source-facing` at the level of the induced Boolean-valued draw process. The
exponential clock family and its product law are the `bridge/view` layer, while the owner
abstraction for the resulting urn path is `IsGeneralizedPolyaUrnWithWeights`. For the cumulative
clock bookkeeping, the chapter's owner declaration is `arrivalTime`, so the file reuses that API
instead of keeping a parallel local partial-sum layer. -/

/-- A trajectory of the exponential-clock realization of the weighted Pólya urn, with genuine
nonnegative waiting times. The value `ω (true, n)` is the `(n + 1)`st black clock increment and
`ω (false, n)` is the `(n + 1)`st red clock increment. -/
abbrev WeightedUrnClockTrajectory := Bool × ℕ → NNReal

/-- The product law of the exponential-clock construction of the weighted Pólya urn with weight
sequence `w`. For each color and each `n`, the corresponding clock increment has law
`Exp (w n)` transported to the nonnegative waiting-time space, and all increments are independent.
-/
noncomputable def weightedUrnClockLaw (w : ℕ → ℝ) : Measure WeightedUrnClockTrajectory :=
  Measure.infinitePi fun i : Bool × ℕ ↦ (expMeasure (w i.2)).map Real.toNNReal

-- Proof sketch: `isProbabilityMeasure_expMeasure (hw n)` makes each coordinate law a probability
-- measure, and the canonical `Measure.infinitePi` instance promotes their product law to a
-- probability measure.
/-- The exponential-clock law is a probability measure whenever every rate `w n` is positive. -/
theorem weightedUrnClockLaw_isProbabilityMeasure
    (w : ℕ → ℝ) (hw : ∀ n : ℕ, 0 < w n) :
    IsProbabilityMeasure (weightedUrnClockLaw w) := by
  letI : ∀ i : Bool × ℕ, IsProbabilityMeasure ((expMeasure (w i.2)).map Real.toNNReal) :=
    fun i ↦ by
      letI : IsProbabilityMeasure (expMeasure (w i.2)) := isProbabilityMeasure_expMeasure (hw i.2)
      exact Measure.isProbabilityMeasure_map (by fun_prop)
  simpa [weightedUrnClockLaw] using
    (inferInstance :
      IsProbabilityMeasure
        (Measure.infinitePi fun i : Bool × ℕ ↦ (expMeasure (w i.2)).map Real.toNNReal))

/-- The arrival time of the `(n + 1)`st clock ring of one fixed color in the exponential embedding
of the weighted urn. -/
def weightedUrnColorArrivalTime (color : Bool) (n : ℕ) : WeightedUrnClockTrajectory → ℝ :=
  arrivalTime (fun k ω ↦ (ω (color, k) : ℝ)) n

/-- The black/red draw counts after the first `n` draws of the clock-embedded urn process. -/
def weightedUrnDrawCounts : ℕ → WeightedUrnClockTrajectory → ℕ × ℕ
  | 0, _ => (0, 0)
  | n + 1, ω =>
      let counts := weightedUrnDrawCounts n ω
      if weightedUrnColorArrivalTime true (counts.1 + 1) ω <
          weightedUrnColorArrivalTime false (counts.2 + 1) ω then
        (counts.1 + 1, counts.2)
      else
        (counts.1, counts.2 + 1)

/-- The source-facing draw process induced by the merged exponential clock rings, where `true`
encodes a black draw and `false` a red draw. -/
def weightedUrnDrawProcess (n : ℕ) (ω : WeightedUrnClockTrajectory) : Bool :=
  let counts := weightedUrnDrawCounts n ω
  weightedUrnColorArrivalTime true (counts.1 + 1) ω <
    weightedUrnColorArrivalTime false (counts.2 + 1) ω

-- Proof sketch: under the product law, after any finite prefix with `ℓ` black draws and
-- `n - ℓ` red draws, the next unseen black and red clocks are independent exponentials with rates
-- `w ℓ` and `w (n - ℓ)`. The memoryless property then gives the textbook one-step cylinder law.
/-- The draw process produced by the exponential embedding realizes the owner abstraction
`IsGeneralizedPolyaUrnWithWeights`. -/
theorem isGeneralizedPolyaUrnWithWeights_weightedUrnDrawProcess
    (w : ℕ → NNReal) (hw : ∀ n : ℕ, 0 < w n) :
    IsGeneralizedPolyaUrnWithWeights
      (weightedUrnClockLaw fun n ↦ (w n : ℝ))
      w
      weightedUrnDrawProcess := sorry

/-- The total clock time of one fixed color, written as the infinite sum of its successive
exponential waiting times. -/
def weightedUrnColorTotalTime (color : Bool) (ω : WeightedUrnClockTrajectory) : ℝ≥0∞ :=
  ∑' n : ℕ, (ω (color, n) : ℝ≥0∞)

/-- The total black-clock time in the exponential embedding of the weighted urn. -/
abbrev weightedUrnBlackTotalTime : WeightedUrnClockTrajectory → ℝ≥0∞ :=
  weightedUrnColorTotalTime true

/-- The total red-clock time in the exponential embedding of the weighted urn. -/
abbrev weightedUrnRedTotalTime : WeightedUrnClockTrajectory → ℝ≥0∞ :=
  weightedUrnColorTotalTime false

/-- The source-facing textbook event that, from some time on, the induced weighted-urn draw
process keeps drawing only one fixed color. -/
def weightedUrnEventuallySingleColorEvent : Set WeightedUrnClockTrajectory :=
  {ω | ∃ color : Bool, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → weightedUrnDrawProcess n ω = color}

/-- The bridge event in the exponential embedding that one color exhausts its total clock time
strictly before the other. -/
def weightedUrnOneColorFinishesFirstEvent : Set WeightedUrnClockTrajectory :=
  {ω | weightedUrnBlackTotalTime ω < weightedUrnRedTotalTime ω ∨
      weightedUrnRedTotalTime ω < weightedUrnBlackTotalTime ω}

-- Proof sketch: if one total color-clock time is strictly smaller than the other, then after the
-- smaller total time only the other color contributes further rings, so the draw process is
-- eventually constant. Conversely, if both colors keep ringing arbitrarily close to the same total
-- horizon, the draw process cannot be eventually monochromatic.
/-- In the exponential embedding, the total-time comparison event is exactly the source-facing
event that eventually only one color is drawn. -/
theorem mem_weightedUrnEventuallySingleColorEvent_iff
    (ω : WeightedUrnClockTrajectory) :
    ω ∈ weightedUrnEventuallySingleColorEvent ↔ ω ∈ weightedUrnOneColorFinishesFirstEvent := sorry

-- Proof sketch: the summability hypothesis makes the black and red total clock times almost surely
-- finite. Under the product law `weightedUrnClockLaw w`, the two color-clock families are
-- independent, so the two total times are independent as well. Each total time has a density
-- because it is an exponential variable convolved with an independent remainder. Hence the
-- diagonal event where the two total times agree has probability zero, so almost surely one color
-- finishes first.
/-- Example 17.27: if `∑ n, 1 / w n` is summable, then in the exponential-clock realization of the
weighted Pólya urn with rates `w n`, almost surely one color finishes all of its clock time
strictly before the other. Equivalently, the induced generalized urn process eventually draws only
one color. -/
theorem weightedUrnClockLaw_ae_eventually_single_color
    (w : ℕ → ℝ) (hw : ∀ n : ℕ, 0 < w n) (hsummable : Summable fun n : ℕ ↦ 1 / w n) :
    ∀ᵐ ω ∂ weightedUrnClockLaw w, ω ∈ weightedUrnEventuallySingleColorEvent := sorry

end ProbabilityTheory
