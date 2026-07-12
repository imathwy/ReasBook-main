import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open FormalMultilinearSeries
open scoped NNReal ENNReal PowerSeries

universe u

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] (a : ℕ → 𝕜)

namespace PowerSeries

/-- The radius of convergence of a scalar formal power series, viewed through the canonical
scalar formal multilinear series attached to its coefficients. -/
noncomputable abbrev radius (S : 𝕜⟦X⟧) : ℝ≥0∞ :=
  (ofScalars 𝕜 (fun n ↦ coeff n S)).radius

/-- The analytic function obtained by summing the scalar power series `S`, viewed through the
canonical scalar formal multilinear series attached to its coefficients. -/
noncomputable abbrev sum (S : 𝕜⟦X⟧) : 𝕜 → 𝕜 :=
  ofScalarsSum (fun n ↦ coeff n S)

end PowerSeries

/- Definition I.2-extra-3: for the scalar formal power series `∑ a_n X^n`, the canonical radius
of convergence is `(ofScalars 𝕜 a).radius`, and the corresponding disc of convergence is the
canonical open extended metric ball `Metric.eball (0 : 𝕜) (ofScalars 𝕜 a).radius`. -/
#check (ofScalars 𝕜 a).radius
#check (Metric.eball (0 : 𝕜) (ofScalars 𝕜 a).radius : Set 𝕜)

noncomputable section

/-- A point lies in the convergence disc exactly when its norm is strictly smaller than the radius
of convergence. -/
theorem mem_scalarSeriesDiscOfConvergence_iff {z : 𝕜} :
    z ∈ Metric.eball (0 : 𝕜) (ofScalars 𝕜 a).radius ↔
      (‖z‖₊ : ℝ≥0∞) < (ofScalars 𝕜 a).radius := by
  rw [mem_eball_zero_iff, enorm_eq_nnnorm]

/-- The disc of convergence of a scalar power series is an open set. -/
theorem isOpen_scalarSeriesDiscOfConvergence :
    IsOpen (Metric.eball (0 : 𝕜) (ofScalars 𝕜 a).radius) := Metric.isOpen_eball

/-- If the radius of convergence is `0`, then the disc of convergence is empty. -/
theorem scalarSeriesDiscOfConvergence_eq_empty_of_radius_eq_zero
    (hρ : (ofScalars 𝕜 a).radius = 0) :
    Metric.eball (0 : 𝕜) (ofScalars 𝕜 a).radius = ∅ := by
  simp [hρ]

end
