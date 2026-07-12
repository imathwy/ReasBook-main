import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap26.Definition_26_23

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

namespace ProbabilityTheory

variable {n m : ℕ}

local notation "State" => Fin n → ℝ
local notation "DiffusionCoeff" => NNReal → State → Fin n → Fin m → ℝ
local notation "DriftCoeff" => NNReal → State → Fin n → ℝ

section

variable (σ : DiffusionCoeff)

local notation "σσᵀ" => diffusionMatrixOfCoefficient σ

-- Proof sketch: for each deterministic starting point `x`, Theorem 26.8 gives a unique strong
-- solution of the SDE with coefficients `σ` and `b`. Theorem 26.18 upgrades this to weak
-- existence together with pathwise uniqueness, and Theorem 26.21 identifies those weak solutions
-- with solutions of the local martingale problem for `(σσᵀ, b)`, yielding existence and
-- uniqueness in law for every Dirac initial distribution.
/-- Remark 26.24: if `σ` and `b` satisfy the hypotheses of Theorem 26.8, then the local
martingale problem `LMP (σσᵀ, b)` is well-posed. -/
theorem localMartingaleProblemWellPosed_of_lipschitz_linearGrowth
    (σ : DiffusionCoeff) (b : DriftCoeff) {K : ℝ} (hK : 0 < K)
    (hbσ_lipschitz :
      ∀ x x' : State, ∀ t : NNReal,
        ‖σ t x - σ t x'‖ + ‖b t x - b t x'‖ ≤ K * ‖x - x'‖)
    (hbσ_growth :
      ∀ x : State, ∀ t : NNReal,
        ‖σ t x‖ ^ 2 + ‖b t x‖ ^ 2 ≤ K ^ 2 * (1 + ‖x‖ ^ 2)) :
    LocalMartingaleProblemWellPosed σσᵀ b := sorry

end

end ProbabilityTheory
