import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_21_30 (from Items/Chap21) -/
noncomputable section

/-- The path space of continuous real-valued functions on `[0, ∞)`, modeled as continuous maps on
`NNReal`. -/
abbrev BrownianPathSpace : Type := C(NNReal, ℝ)

local notation "Ω" => BrownianPathSpace

/-- Theorem 21.30: the continuous path space `Ω = C([0, ∞), ℝ)` is Polish for the canonical
compact-open topology. Equivalently, it is separable and admits a compatible complete metric. -/
theorem brownianPathSpace_polish :
    PolishSpace Ω := by
  infer_instance

/-- The continuous path space `Ω = C([0, ∞), ℝ)` is separable for the compact-open topology. -/
theorem brownianPathSpace_separable :
    TopologicalSpace.SeparableSpace Ω := by
  infer_instance

/-- The canonical compact-open topology on `Ω = C([0, ∞), ℝ)` is completely metrizable. -/
theorem brownianPathSpace_completelyMetrizable :
    TopologicalSpace.IsCompletelyMetrizableSpace Ω := by
  infer_instance

/- For continuous-path families, the compact-open topology on `Ω = C([0, ∞), ℝ)` is the
compact-convergence topology: convergence is uniform on each compact subset of `[0, ∞)`. -/
recall ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn
