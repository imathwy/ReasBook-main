import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_15_56 (from Items/Chap15) -/
open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

section

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Theorem 15.56: Cramer--Wold device. A sequence of probability laws on `ℝ^d` converges weakly
if and only if every one-dimensional projected law along `x ↦ ⟪t, x⟫` converges weakly. -/
-- Proof sketch: for the forward implication, apply weak convergence to the continuous scalar
-- projection `x ↦ ⟪t, x⟫`. For the converse, use convergence of the projected characteristic
-- functions together with uniqueness of probability measures on `ℝ^d` from all one-dimensional
-- projections.
theorem tendsto_iff_all_scalarProjectionLaws_tendsto
    (μs : ℕ → ProbabilityMeasure E) :
    (∃ μ : ProbabilityMeasure E, Tendsto μs atTop (𝓝 μ)) ↔
      ∀ t : E, ∃ νt : ProbabilityMeasure ℝ,
        Tendsto
          (fun n ↦
            ((μs n).map
              (show AEMeasurable (fun x : E ↦ inner ℝ t x) (μs n : Measure E) from
                aemeasurable_id.const_inner) : ProbabilityMeasure ℝ))
          atTop (𝓝 νt) := sorry

/-- If `μs` converges weakly to `μ` and the projected laws converge to `ν t`, then `ν t` is the
pushforward of `μ` along `x ↦ ⟪t, x⟫`. -/
-- Proof sketch: apply the forward direction of the Cramer--Wold device to the weak convergence of
-- `μs` in order to get convergence of each projected law to the pushforward of `μ` along
-- `x ↦ ⟪t, x⟫`, then use
-- uniqueness of limits in the Hausdorff weak topology on probability measures.
theorem scalarProjectionLaw_limit_eq_of_tendsto
    {μs : ℕ → ProbabilityMeasure E}
    {μ : ProbabilityMeasure E}
    {ν : E → ProbabilityMeasure ℝ}
    (hμ : Tendsto μs atTop (𝓝 μ))
    (hν : ∀ t : E,
      Tendsto
        (fun n ↦
          ((μs n).map
            (show AEMeasurable (fun x : E ↦ inner ℝ t x) (μs n : Measure E) from
              aemeasurable_id.const_inner) : ProbabilityMeasure ℝ))
        atTop (𝓝 (ν t))) :
    ∀ t : E,
      ν t =
        (μ.map
          (show AEMeasurable (fun x : E ↦ inner ℝ t x) (μ : Measure E) from
            aemeasurable_id.const_inner) : ProbabilityMeasure ℝ) := sorry

end
