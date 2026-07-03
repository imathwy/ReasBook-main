import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap16.Theorem_16_22
import ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8

-- Declarations for this item will be appended below by the statement pipeline.

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
