import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u v

variable {ι : Type u} {Ω : Type v} [Preorder ι]
variable {m0 : MeasurableSpace Ω}
variable {ℱ : Filtration ι m0} {μ : Measure Ω}

-- Proof sketch: combine the submartingale inequality `X s ≤ E[X t | ℱ s]` with conditional
-- Jensen for the convex map `φ`; monotonicity of `φ` lets one pass from `X s ≤ E[X t | ℱ s]` to
-- `φ (X s) ≤ φ (E[X t | ℱ s])`, and the positive-part integrability assumption upgrades the
-- resulting a.e. inequality to the submartingale API.
section

variable [SigmaFiniteFiltration μ ℱ]

/-- Exercise 9.2.3 (1): if `X` is a submartingale and `φ : ℝ → ℝ` is convex and monotone
increasing, then integrability of the positive part of `φ ∘ X_t` at every time implies that the
process `φ(X_t)` is a submartingale. -/
theorem submartingale_convex_monotone_comp {X : ι → Ω → ℝ} {φ : ℝ → ℝ}
    (hX : Submartingale X ℱ μ) (hφ : ConvexOn ℝ Set.univ φ) (hφ_mono : Monotone φ)
    (hφ_int : ∀ i, Integrable (fun ω ↦ (φ (X i ω))⁺) μ) :
    Submartingale (fun i ω ↦ φ (X i ω)) ℱ μ := sorry

end

/-- The deterministic two-time process taking the values `-1` and then `0` on the one-point
probability space. -/
def square_counterexample_process : Fin 2 → PUnit → ℝ
  | 0, _ => -1
  | 1, _ => 0

/-- The trivial two-time filtration on the one-point measurable space used for the monotonicity
counterexample. -/
abbrev square_counterexample_filtration : Filtration (Fin 2) (⊤ : MeasurableSpace PUnit) := ⊥

/-- The Dirac probability measure at the unique point of `PUnit`. -/
abbrev square_counterexample_measure : Measure PUnit := Measure.dirac PUnit.unit

-- Proof sketch: on the one-point space with the trivial filtration, conditional expectations are
-- ordinary values. The deterministic path `-1 ≤ 0` therefore defines a submartingale.
/-- The deterministic two-time process `(-1, 0)` is a submartingale on the one-point space. -/
theorem square_counterexample_process_submartingale :
    Submartingale square_counterexample_process square_counterexample_filtration
      square_counterexample_measure := sorry

-- Proof sketch: `x ↦ x^2` is convex on `ℝ` by the standard polynomial convexity criterion.
/-- The square map is convex on all of `ℝ`. -/
theorem square_counterexample_function_convex :
    ConvexOn ℝ Set.univ (fun x : ℝ ↦ x ^ 2) := sorry

-- Proof sketch: compare the values at `-1` and `0`; monotonicity would force
-- `(-1)^2 ≤ 0^2`, which is false.
/-- The square map is not monotone increasing on `ℝ`. -/
theorem square_counterexample_function_not_monotone :
    ¬ Monotone (fun x : ℝ ↦ x ^ 2) := sorry

-- Proof sketch: the one-point measure turns integrability into finiteness of a single real value,
-- and the transformed process only takes the values `1` and `0`.
/-- The positive part of the transformed counterexample process is integrable at each time. -/
theorem square_counterexample_comp_pos_integrable :
    ∀ i, Integrable
      (fun ω ↦ ((square_counterexample_process i ω) ^ 2)⁺)
      square_counterexample_measure := sorry

-- Proof sketch: after applying `x ↦ x^2`, the deterministic path becomes `1` then `0`, so the
-- one-step submartingale inequality fails already at times `0 ≤ 1`.
/-- Exercise 9.2.3 (2): the deterministic two-time submartingale `(-1, 0)` on the one-point
space together with the convex but nonmonotone map `x ↦ x^2` shows that monotonicity of `φ` is
essential, because the transformed process is not a submartingale. -/
theorem square_counterexample_transform_not_submartingale :
    ¬ Submartingale
      (fun i ω ↦ (square_counterexample_process i ω) ^ 2)
      square_counterexample_filtration square_counterexample_measure := sorry
