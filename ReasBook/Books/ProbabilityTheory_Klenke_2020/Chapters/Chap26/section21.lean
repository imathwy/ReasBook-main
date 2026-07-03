import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_26_21 (from Items/Chap26) -/
open MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

universe u v

namespace ProbabilityTheory

variable {n m : ℕ}

local notation "State" => Fin n → ℝ
local notation "PathSpace" => EuclideanPathSpace n
local notation "DiffusionCoeff" => NNReal → State → Fin n → Fin m → ℝ
local notation "DriftCoeff" => NNReal → State → Fin n → ℝ

section

variable (σ : DiffusionCoeff)

local notation "σσᵀ" => diffusionMatrixOfCoefficient σ

-- Proof sketch: for the forward implication, apply the martingale-representation theorem to the
-- local-martingale part of the martingale problem to obtain, on an extension, a Brownian driver
-- whose covariance is `σσᵀ`, and then identify the resulting decomposition with the SDE. For the
-- reverse implication, apply Itô's formula to every `C²` test function of a weak solution to show
-- that the compensated process is a continuous local martingale.
/-- Theorem 26.21: a path-space process solves the local martingale problem
`LMP (σσᵀ, b, μ₀)` if and only if, on a suitable extension of the probability space, there exists
an `m`-dimensional Brownian motion making the same state process into a weak solution of the SDE
with diffusion coefficient `σ`, drift `b`, and initial distribution `μ₀`. -/
theorem solvesLocalMartingaleProblem_iff_exists_generalizedWeakSDESolution_extension
    (σ : DiffusionCoeff) (b : DriftCoeff) (μ₀ : Measure State) [IsProbabilityMeasure μ₀]
    {Ω : Type u} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω) (X : Ω → PathSpace)
    (hX : ∀ t, Measurable (fun ω ↦ X ω t)) :
    IsLocalMartingaleProblemSolution μ₀ σσᵀ b
      (generatedFiltration (fun t ω ↦ X ω t) hX)
      (P : Measure Ω) X ↔
      ∃ L : GeneralizedWeakSDESolution.{v} μ₀ σ b,
        ∃ lift : L.Ω → Ω,
          MeasurePreserving lift L.μ (P : Measure Ω) ∧
          L.X = X ∘ lift := sorry

-- Proof sketch: choose a reference martingale-problem solution from the unique-solvability
-- hypothesis, transport it to a weak solution using
-- `solvesLocalMartingaleProblem_iff_exists_generalizedWeakSDESolution_extension`, and then use the
-- same equivalence
-- again to compare the state-path laws of any two weak solutions via the unique law of the
-- martingale problem.
/-- If the local martingale problem for `(σσᵀ, b, μ₀)` is uniquely solvable, then the SDE with
diffusion coefficient `σ`, drift `b`, and initial distribution `μ₀` has a weak solution that is
unique in law. -/
theorem exists_weakSDESolution_of_localMartingaleProblemUniquelySolvable
    (σ : DiffusionCoeff) (b : DriftCoeff) (μ₀ : Measure State) [IsProbabilityMeasure μ₀]
    (hex :
      ∃ (Ω : Type u) (_ : MeasurableSpace Ω)
        (P : ProbabilityMeasure Ω) (X : Ω → PathSpace)
        (hX : ∀ t, Measurable (fun ω ↦ X ω t)),
        IsLocalMartingaleProblemSolution μ₀ σσᵀ b
          (generatedFiltration (fun t ω ↦ X ω t) hX)
          (P : Measure Ω) X)
    (hunique : LocalMartingaleProblemHasUniqueLaw μ₀ σσᵀ b) :
    ∃ L : GeneralizedWeakSDESolution.{u} μ₀ σ b, L.IsWeaklyUnique := sorry

end

end ProbabilityTheory
