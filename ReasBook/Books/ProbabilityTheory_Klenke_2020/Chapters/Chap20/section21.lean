import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_20_21 (from Items/Chap20) -/
open Filter MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory Topology

-- Proof sketch: apply the canonical ergodic-theory owners on path space. The relevant partial
-- sums are the Birkhoff sums of the first-coordinate observable `ω ↦ ω 0` along the one-sided
-- shift `Stream'.tail`, and the normalized partial sums are the corresponding Birkhoff averages.
-- The divergence event is shift-invariant, so ergodicity upgrades positive probability to almost
-- sure occurrence. The linear-drift clause is the almost-sure convergence of the Birkhoff
-- averages to the expectation of the first coordinate.
/-- Theorem 20.21: for an integrable ergodic process on the path space `ℕ → ℝ`, the following are
equivalent: the Birkhoff sums of the first coordinate along the one-sided shift tend to `+∞`
almost surely; the same event has positive probability; and the corresponding Birkhoff averages
converge almost surely to the positive expectation of the first coordinate. -/
theorem ergodic_process_partial_sum_tendsto_atTop_tfae
    (P : Measure (ℕ → ℝ)) [IsProbabilityMeasure P] (hP : Ergodic Stream'.tail P)
    (h_int : Integrable (Function.eval 0) P) :
    List.TFAE
      [ ∀ᵐ ω ∂P,
          Tendsto
            (fun n ↦ birkhoffSum Stream'.tail (Function.eval 0) n ω)
            atTop atTop
      , 0 < P {ω |
          Tendsto
            (fun n ↦ birkhoffSum Stream'.tail (Function.eval 0) n ω)
            atTop atTop}
      , 0 < P[Function.eval 0] ∧
          ∀ᵐ ω ∂P,
            Tendsto
              (fun n ↦ birkhoffAverage ℝ Stream'.tail (Function.eval 0) n ω)
              atTop
              (𝓝 (P[Function.eval 0]))
      ] := sorry
