import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_26_22 (from Items/Chap26) -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

universe u

namespace ProbabilityTheory

variable {n : ℕ}

local notation "State" => Fin n → ℝ
local notation "PathSpace" => EuclideanPathSpace n
local notation "DiffusionMatrixCoeff" => NNReal → State → Fin n → Fin n → ℝ
local notation "DriftCoeff" => NNReal → State → Fin n → ℝ

-- Proof sketch: invoke the standard Stroock--Varadhan existence theorem for continuous bounded
-- coefficients and retain the resulting realization data directly.
/-- Theorem 26.22: if the drift field `b` and diffusion matrix field `a` are continuous and
bounded, and `a` is symmetric and nonnegative semidefinite as a diffusion matrix, then every
initial law `μ₀` on `ℝ^n` admits a realization solving the local martingale problem
`LMP(a, b, μ₀)`. -/
theorem localMartingaleProblem_existsSolution_of_continuous_bounded_coefficients
    (a : DiffusionMatrixCoeff) (b : DriftCoeff)
    (ha_cont : Continuous fun p : NNReal × State ↦ a p.1 p.2)
    (ha_bdd : ∃ C : ℝ, ∀ p : NNReal × State, ‖a p.1 p.2‖ ≤ C)
    (ha_symm : ∀ t : NNReal, ∀ x : State, ∀ i j : Fin n, a t x i j = a t x j i)
    (ha_nonneg : ∀ t : NNReal, ∀ x v : State,
      0 ≤ ∑ i : Fin n, ∑ j : Fin n, v i * a t x i j * v j)
    (hb_cont : Continuous fun p : NNReal × State ↦ b p.1 p.2)
    (hb_bdd : ∃ C : ℝ, ∀ p : NNReal × State, ‖b p.1 p.2‖ ≤ C)
    (μ₀ : Measure State) [IsProbabilityMeasure μ₀] :
    ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (ℱ : Filtration NNReal mΩ)
      (P : ProbabilityMeasure Ω) (X : Ω → PathSpace),
      IsLocalMartingaleProblemSolution μ₀ a b ℱ (P : Measure Ω) X := sorry

end ProbabilityTheory
