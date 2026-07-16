import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap09.Definition_9_1

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/- Definition 5.33: a Poisson process with intensity `α` under `μ` is a stochastic
nondecreasing counting process that starts at `0`, has independent increments, and whose
increments over `(s,t]` have Poisson law with parameter `α * (t - s)`. For an `ℕ`-valued process,
the monotonicity field makes the increment `N t - N s` the genuine interval count on `(s,t]`,
rather than truncated subtraction. -/
/-- A process on `[0,∞)` is Poisson with intensity `α` under `μ` if it is stochastic, starts at
`0`, is nondecreasing, has independent increments, and every increment over `(s,t]` has Poisson
law with parameter `α * (t - s)`. -/
class IsPoissonProcess (α : NNReal) (μ : Measure Ω) (N : NNReal → Ω → ℕ) : Prop where
  /-- A Poisson process is, in particular, a stochastic process. -/
  stochastic : IsStochasticProcess N
  /-- A Poisson process starts at `0`. -/
  zero : N 0 = 0
  /-- A Poisson process is a nondecreasing counting process. -/
  mono : Monotone N
  /-- Poisson processes have independent increments. -/
  indepIncrements : HasIndepIncrements N μ
  /-- Every increment over `(s,t]` has the expected Poisson law. -/
  poisson_increment :
    ∀ ⦃s t : NNReal⦄, s ≤ t →
      HasLaw (fun ω ↦ N t ω - N s ω) (poissonMeasure (α * (t - s))) μ

/- Definition 5.33: the chapter's canonical notion of a Poisson process with intensity `α` under
`μ` is `IsPoissonProcess α μ N`. The companion declarations below restate the textbook
`N 0 = 0` + monotone counting-process + independent increments + strict Poisson increment-law
formulation in terms of this canonical API. -/
recall IsPoissonProcess

namespace IsPoissonProcess

/-- Any Poisson process is defined over a probability measure, since each positive-time increment
has Poisson law. -/
theorem isProbabilityMeasure
    {N : NNReal → Ω → ℕ} {μ : Measure Ω} {α : NNReal} (hN : IsPoissonProcess α μ N) :
    IsProbabilityMeasure μ := by
  let hLaw :
      HasLaw (fun ω ↦ N 1 ω - N 0 ω) (poissonMeasure (α * (1 - 0))) μ :=
    hN.poisson_increment (show (0 : NNReal) ≤ 1 by norm_num)
  exact hLaw.isProbabilityMeasure

/-- The textbook strict-increment formulation is an immediate corollary of the `s ≤ t` increment
law. -/
theorem poisson_increment_of_lt
    {N : NNReal → Ω → ℕ} {μ : Measure Ω} {α : NNReal}
    (hN : IsPoissonProcess α μ N) {s t : NNReal} (hst : s < t) :
    HasLaw (fun ω ↦ N t ω - N s ω) (poissonMeasure (α * (t - s))) μ :=
  hN.poisson_increment (le_of_lt hst)

/-- The marginal law at time `t` is the Poisson law with parameter `α t`. -/
theorem poisson_law
    {N : NNReal → Ω → ℕ} {μ : Measure Ω} {α : NNReal}
    (hN : IsPoissonProcess α μ N) (t : NNReal) :
    HasLaw (N t) (poissonMeasure (α * t)) μ := by
  letI := hN.isProbabilityMeasure
  simpa [hN.zero] using
    (show HasLaw (fun ω ↦ N t ω - N 0 ω) (poissonMeasure (α * (t - 0))) μ from
      hN.poisson_increment (show (0 : NNReal) ≤ t from bot_le))

end IsPoissonProcess

/-- Definition 5.33, source-facing bridge: a stochastic nondecreasing counting process that starts
at `0`, has independent increments, and whose strict increments have Poisson laws is a Poisson
process in the chapter's canonical sense. -/
theorem isPoissonProcess_of_textbook
    {N : NNReal → Ω → ℕ} {μ : Measure Ω} {α : NNReal}
    (hstochastic : IsStochasticProcess N)
    (hzero : N 0 = 0)
    (hmono : Monotone N)
    (hindep : HasIndepIncrements N μ)
    (hpoisson : ∀ ⦃s t : NNReal⦄, s < t →
      HasLaw (fun ω ↦ N t ω - N s ω) (poissonMeasure (α * (t - s))) μ) :
    IsPoissonProcess α μ N := by
  sorry

/-- The constant zero counting process is a Poisson process with intensity `0`. -/
instance (μ : Measure Ω) [IsProbabilityMeasure μ] :
    IsPoissonProcess 0 μ (fun _ _ ↦ 0) := by
  sorry
