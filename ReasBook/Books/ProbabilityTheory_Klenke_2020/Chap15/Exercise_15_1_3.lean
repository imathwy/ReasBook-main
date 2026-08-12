import Mathlib
import ProbabilityTheory_Klenke_2020.Chap15.Theorem_15_10

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

open scoped BigOperators

-- Proof sketch: first identify the singleton masses `μ ({x})` with the Fourier coefficients of
-- the `2π`-periodic function induced by `charFun (μ.map latticeEmbedding)` via
-- `discreteFourierInversionFormula`. Then rescale the cube `[-π, π)^d` to the owner Fourier space
-- `UnitAddTorus (Fin d)` and apply mathlib's multivariate Parseval theorem
-- `UnitAddTorus.hasSum_sq_mFourierCoeff`; the present statement keeps the textbook lattice-mass
-- formulation as the source-facing main entry.
/-- Exercise 15.1.3: under the hypotheses of the discrete Fourier inversion formula for a finite
measure `μ` on `ℤ^d`, the sum of the squared singleton masses equals the normalized `L²`-norm of
its characteristic function on the fundamental domain `[-π, π)^d`. -/
theorem lattice_measure_plancherel_formula (d : ℕ) (μ : Measure (Fin d → ℤ)) [IsFiniteMeasure μ] :
    (∑' x : Fin d → ℤ, μ.real ({x} : Set (Fin d → ℤ)) ^ 2) =
      (((2 * Real.pi) ^ d : ℝ)⁻¹ *
        ∫ t in latticeFrequencyCube d, ‖charFun (μ.map latticeEmbedding) t‖ ^ 2 ∂volume) := sorry
