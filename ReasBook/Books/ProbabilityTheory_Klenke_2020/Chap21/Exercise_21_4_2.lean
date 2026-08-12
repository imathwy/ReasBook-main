import Mathlib
import ProbabilityTheory_Klenke_2020.Chap21.Definition_21_21

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory Set
open MeasureTheory.Filtration
open scoped ENNReal Topology

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ℱ : Filtration NNReal ‹MeasurableSpace Ω›}
variable {X : NNReal → Ω → ℝ}

/- Exercise 21.4.2 is `source-facing`: it concerns continuous-time martingale convergence on
`[0, ∞)` to the canonical limit process `ℱ.limitProcess X μ`.

Domain-style sampling for the owner abstraction:
* `HasRightContinuousPaths X` in Definition 21.21 is the local `core/canonical` owner for the path
  regularity input; the stronger càdlàg condition is only a derived specialization.
* `stronglyMeasurable_limitProcess` is the owner theorem for terminal measurability of
  `ℱ.limitProcess X μ`, and it already works for `NNReal`-indexed filtrations.
* The discrete chapter owners `Submartingale.memLp_limitProcess`,
  `Submartingale.ae_tendsto_limitProcess_of_uniformIntegrable`, and
  `Submartingale.tendsto_eLpNorm_one_limitProcess` determine the correct statement shape, but they
  live over `ℕ`-indexed filtrations, so they guide the bridge design here rather than replacing the
  present theorems by exact recalls.

Primitive data versus derived API:
* primitive inputs: right continuity, submartingale or martingale structure, and the textbook
  boundedness / uniform-integrability / `L^p` hypotheses;
* derived object: the limit random variable is the canonical owner object `ℱ.limitProcess X μ`,
  not extra public data.

Accordingly, only terminal strong measurability is a direct recall, while the almost-sure and
`eLpNorm` formulations below remain `bridge/view` companions for the continuous-time setting. -/

/- The canonical limit process is already `⨆ t, ℱ t`-strongly measurable by the general owner
declaration for `Filtration.limitProcess`. -/
recall stronglyMeasurable_limitProcess

section

variable (hX_rc : HasRightContinuousPaths X)
include hX_rc

local notation "X∞" => ℱ.limitProcess X μ

-- Proof sketch: restrict the right-continuous process to a countable dense time skeleton, apply
-- Doob's inequality from Exercise 21.4.1 together with the discrete convergence theorems of
-- Chapter 11
-- to the sampled process, and then use right continuity to upgrade convergence along the
-- skeleton to convergence as `t → ∞` in continuous time, with canonical limit `X∞`.
/-- Exercise 21.4.2, Theorem 11.4 analogue: a right-continuous submartingale on `[0,∞)` whose
positive-part expectations are bounded above has an integrable canonical limit process, and the
process converges almost surely to that limit. -/
theorem rightContinuous_submartingale_convergence_to_integrable_limitProcess_of_bdd_pos_part
    (hX : Submartingale X ℱ μ)
    (hpos : BddAbove (range fun t ↦ μ[fun ω ↦ (X t ω)⁺])) :
    Integrable X∞ μ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun t ↦ X t ω) atTop (𝓝 (X∞ ω)) := sorry

/-- Exercise 21.4.2, Theorem 11.4 analogue, convergence component. -/
theorem rightContinuous_submartingale_ae_tendsto_limitProcess_of_bdd_pos_part
    (hX : Submartingale X ℱ μ)
    (hpos : BddAbove (range fun t ↦ μ[fun ω ↦ (X t ω)⁺])) :
    ∀ᵐ ω ∂μ, Tendsto (fun t ↦ X t ω) atTop (𝓝 (X∞ ω)) := by
  exact
    (rightContinuous_submartingale_convergence_to_integrable_limitProcess_of_bdd_pos_part
      hX_rc hX hpos).2

/-- Exercise 21.4.2, Theorem 11.7 analogue for martingales: a uniformly integrable
right-continuous martingale on `[0,∞)` has an integrable canonical limit process, and the process
converges almost surely to that limit. -/
theorem rightContinuous_martingale_convergence_to_integrable_limitProcess_of_uniformIntegrable
    (hX : Martingale X ℱ μ) (hUI : UniformIntegrable X 1 μ) :
    Integrable X∞ μ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun t ↦ X t ω) atTop (𝓝 (X∞ ω)) := sorry

/-- Exercise 21.4.2, Theorem 11.7 analogue, convergence component for martingales. -/
theorem rightContinuous_martingale_ae_tendsto_limitProcess_of_uniformIntegrable
    (hX : Martingale X ℱ μ) (hUI : UniformIntegrable X 1 μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun t ↦ X t ω) atTop (𝓝 (X∞ ω)) := by
  exact
    (rightContinuous_martingale_convergence_to_integrable_limitProcess_of_uniformIntegrable
      hX_rc hX hUI).2

/-- Exercise 21.4.2, `L¹` bridge companion: a uniformly integrable right-continuous martingale on
`[0,∞)` converges to its canonical limit process in the raw `eLpNorm` formulation of `L¹`. -/
theorem rightContinuous_martingale_tendsto_eLpNorm_one_limitProcess_of_uniformIntegrable
    (hX : Martingale X ℱ μ) (hUI : UniformIntegrable X 1 μ) :
    Tendsto (fun t ↦ eLpNorm (X t - X∞) 1 μ) atTop (𝓝 0) := sorry

/-- Exercise 21.4.2, Theorem 11.10 analogue: an `L^p`-bounded right-continuous martingale with
`1 < p` has a canonical limit process that is terminally strongly measurable, belongs to
`L^p(μ)`, and captures the almost-sure limit. -/
theorem rightContinuous_martingale_convergence_to_memLp_limitProcess_of_lp_bounded
    {p : ℝ} (hX : Martingale X ℱ μ) (hp : 1 < p)
    (hbounded : ∃ C : NNReal, ∀ t : NNReal, eLpNorm (X t) (ENNReal.ofReal p) μ ≤ C) :
    StronglyMeasurable[⨆ t, ℱ t] X∞ ∧
      MemLp X∞ (ENNReal.ofReal p) μ ∧
      (∀ᵐ ω ∂μ, Tendsto (fun t ↦ X t ω) atTop (𝓝 (X∞ ω))) := sorry

/-- Exercise 21.4.2, Theorem 11.10 analogue, `L^p` bridge companion: an `L^p`-bounded
right-continuous martingale with `1 < p` converges to its canonical limit process in the raw
`eLpNorm` formulation of `L^p`. -/
theorem rightContinuous_martingale_tendsto_eLpNorm_limitProcess_of_lp_bounded
    {p : ℝ} (hX : Martingale X ℱ μ) (hp : 1 < p)
    (hbounded : ∃ C : NNReal, ∀ t : NNReal, eLpNorm (X t) (ENNReal.ofReal p) μ ≤ C) :
    Tendsto (fun t ↦ eLpNorm (X t - X∞) (ENNReal.ofReal p) μ) atTop (𝓝 0) := sorry

omit hX_rc

end

end ProbabilityTheory
