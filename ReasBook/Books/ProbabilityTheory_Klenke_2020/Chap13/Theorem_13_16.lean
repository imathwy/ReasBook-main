import Mathlib
import ProbabilityTheory_Klenke_2020.Chap13.Remark_13_14
import ProbabilityTheory_Klenke_2020.Chap13.Definition_13_12

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory Set Topology

noncomputable section

universe u

namespace MeasureTheory
namespace FiniteMeasure

section Portmanteau

variable {E : Type u} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]

-- Proof sketch: for the first six clauses, pass between finite subprobability measures and their
-- normalized probability measures, then combine mathlib's weak-convergence characterization for
-- `FiniteMeasure`, the probability-measure Portmanteau implications, and the null-boundary
-- criterion. Under local compactness and Polish assumptions, identify vague convergence plus mass
-- control with weak convergence via the source-facing predicate
-- `radonMeasureVaguelyConvergesTo`.
/-- Theorem 13.16: For subprobability finite measures on a metric space, weak convergence, the
bounded-Lipschitz and bounded-measurable test-function criteria, the closed/open Portmanteau
inequalities, and convergence on `μ`-continuity sets are equivalent; if the space is locally
compact and Polish, the two vague-convergence formulations are equivalent to the same conditions. -/
theorem portmanteau_subprobability_tfae (μs : ℕ → FiniteMeasure E) (μ : FiniteMeasure E)
    (hμ : μ.mass ≤ 1) (hμs : ∀ n, (μs n).mass ≤ 1) :
    List.TFAE
      [ Tendsto μs atTop (𝓝 μ)
      , ∀ f : E → ℝ, Bornology.IsBounded (range f) → (∃ L, LipschitzWith L f) →
          Tendsto (fun n ↦ ∫ x, f x ∂(μs n : Measure E)) atTop
            (𝓝 (∫ x, f x ∂(μ : Measure E)))
      , ∀ f : E → ℝ, Bornology.IsBounded (range f) → Measurable f →
          μ {x : E | ¬ ContinuousAt f x} = 0 →
            Tendsto (fun n ↦ ∫ x, f x ∂(μs n : Measure E)) atTop
              (𝓝 (∫ x, f x ∂(μ : Measure E)))
      , μ.mass ≤ liminf (fun n ↦ (μs n).mass) atTop ∧
          ∀ F : Set E, IsClosed F → limsup (fun n ↦ μs n F) atTop ≤ μ F
      , limsup (fun n ↦ (μs n).mass) atTop ≤ μ.mass ∧
          ∀ G : Set E, IsOpen G → μ G ≤ liminf (fun n ↦ μs n G) atTop
      , ∀ A : Set E, MeasurableSet A → μ (frontier A) = 0 →
          Tendsto (fun n ↦ μs n A) atTop (𝓝 (μ A))
      ] ∧
      (∀ [LocallyCompactSpace E] [PolishSpace E],
        List.TFAE
          [ Tendsto μs atTop (𝓝 μ)
          , ∀ f : E → ℝ, Bornology.IsBounded (range f) → (∃ L, LipschitzWith L f) →
              Tendsto (fun n ↦ ∫ x, f x ∂(μs n : Measure E)) atTop
                (𝓝 (∫ x, f x ∂(μ : Measure E)))
          , ∀ f : E → ℝ, Bornology.IsBounded (range f) → Measurable f →
              μ {x : E | ¬ ContinuousAt f x} = 0 →
                Tendsto (fun n ↦ ∫ x, f x ∂(μs n : Measure E)) atTop
                  (𝓝 (∫ x, f x ∂(μ : Measure E)))
          , μ.mass ≤ liminf (fun n ↦ (μs n).mass) atTop ∧
              ∀ F : Set E, IsClosed F → limsup (fun n ↦ μs n F) atTop ≤ μ F
          , limsup (fun n ↦ (μs n).mass) atTop ≤ μ.mass ∧
              ∀ G : Set E, IsOpen G → μ G ≤ liminf (fun n ↦ μs n G) atTop
          , ∀ A : Set E, MeasurableSet A → μ (frontier A) = 0 →
              Tendsto (fun n ↦ μs n A) atTop (𝓝 (μ A))
          , radonMeasureVaguelyConvergesTo (fun n ↦ (μs n : Measure E)) (μ : Measure E) ∧
              Tendsto (fun n ↦ (μs n).mass) atTop (𝓝 μ.mass)
          , radonMeasureVaguelyConvergesTo (fun n ↦ (μs n : Measure E)) (μ : Measure E) ∧
              limsup (fun n ↦ (μs n).mass) atTop ≤ μ.mass
          ]) := sorry

end Portmanteau

end FiniteMeasure
end MeasureTheory
