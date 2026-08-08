import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import OptimizationTheoryAndMethods_SunYuan_2006.SunYuanOptimizationTheoryMethods.Chapter07.Definition_7_3_extra_1

open Matrix

section

variable {m n : ℕ}

/-- A real number `μ` is a Levenberg-Marquardt trust-region multiplier for `sk` when it
satisfies the source nonnegativity, stationarity, complementary-slackness, and feasibility
conditions. -/
structure IsLevenbergMarquardtTrustRegionMultiplier
    (J : Matrix (Fin m) (Fin n) ℝ) (r : EuclideanSpace ℝ (Fin m))
    (Δ : ℝ) (sk : EuclideanSpace ℝ (Fin n)) (μ : ℝ) : Prop where
  nonneg : 0 ≤ μ
  stationarity : solvesLevenbergMarquardtNormalEquation J (Jᵀ.mulVec r) μ sk
  complementarySlackness : μ * (Δ - ‖sk‖) = 0
  feasible : ‖sk‖ ≤ Δ

/-- Expanding the Levenberg-Marquardt trust-region multiplier predicate gives the four explicit
KKT clauses used in the source statement. -/
theorem isLevenbergMarquardtTrustRegionMultiplier_iff
    (J : Matrix (Fin m) (Fin n) ℝ) (r : EuclideanSpace ℝ (Fin m))
    (Δ : ℝ) (sk : EuclideanSpace ℝ (Fin n)) (μ : ℝ) :
    IsLevenbergMarquardtTrustRegionMultiplier J r Δ sk μ ↔
      0 ≤ μ ∧
        solvesLevenbergMarquardtNormalEquation J (Jᵀ.mulVec r) μ sk ∧
        μ * (Δ - ‖sk‖) = 0 ∧
        ‖sk‖ ≤ Δ := by
  constructor
  · intro hμ
    exact ⟨hμ.nonneg, hμ.stationarity, hμ.complementarySlackness, hμ.feasible⟩
  · rintro ⟨hnonneg, hstationarity, hcomplementary, hfeasible⟩
    exact
      { nonneg := hnonneg
        stationarity := hstationarity
        complementarySlackness := hcomplementary
        feasible := hfeasible }

end
