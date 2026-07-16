import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap26.Definition_26_17
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap26.Theorem_26_8

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {n m : ℕ}

local notation "State" => Fin n → ℝ
local notation "StatePathSpace" => ProbabilityTheory.EuclideanPathSpace n
local notation "NoisePathSpace" => ProbabilityTheory.EuclideanPathSpace m
local notation "DiffusionCoeff" => NNReal → State → Fin n → Fin m → ℝ
local notation "DriftCoeff" => NNReal → State → Fin n → ℝ

/-- The coefficient-based weak-solution predicate associated to the SDE with diffusion `σ` and
drift `b`. A continuous state-path random variable `X` solves the SDE when its time-indexed
version satisfies the generalized-diffusion relation. -/
def SolvesGeneralizedSDE (σ : DiffusionCoeff) (b : DriftCoeff) :
    {Ω : Type u} → [MeasurableSpace Ω] →
      Filtration NNReal (inferInstance : MeasurableSpace Ω) → Measure Ω →
      (Ω → StatePathSpace) → (NNReal → Ω → Fin m → ℝ) → Prop :=
  fun {_} _ ℱ μ X W ↦
    ∃ _ : IsProbabilityMeasure μ,
      IsGeneralizedNDimensionalDiffusion ℱ μ
        (fun ω ↦ X ω 0) W σ b (pathProcess X)

/-- The weak solutions of the SDE with coefficients `(σ, b)` and initial distribution `μ₀`. -/
abbrev GeneralizedWeakSDESolution (μ₀ : Measure State) [IsProbabilityMeasure μ₀]
    (σ : DiffusionCoeff) (b : DriftCoeff) :=
  WeakSDESolution n m μ₀ (SolvesGeneralizedSDE σ b)

section GeneralizedStrongSolutions

variable (σ : DiffusionCoeff) (b : DriftCoeff)

/- Source/core/bridge triage for Theorem 26.18:
- bridge vocabulary kept: `SolvesGeneralizedSDE` and `GeneralizedWeakSDESolution`;
- core/canonical owner reused: `HasUniqueStrongSolution`;
- bridge/view layer reused from `Theorem_26_8`: `GeneralizedSDEBrownianMotion` and
  `SolvesStrongGeneralizedSDE`;
- deleted duplicate local owner layer: the previous exact-interface unfolding theorem for
  `HasUniqueStrongSolution` and the local re-declaration of the path-valued strong-solution
  bridge.
-/

-- Proof sketch: this is the specialized Yamada--Watanabe comparison written directly with the
-- canonical unique-strong-solution owner from Definition 26.4 and the generalized-diffusion
-- Brownian/solution relations attached to `(σ, b)`.
/-- Theorem 26.18: the SDE with coefficients `σ` and `b` has a unique strong solution for every
initial distribution if and only if, for every initial distribution `μ₀`, it has a weak solution
and pathwise uniqueness holds. -/
theorem hasUniqueStrongGeneralizedSDESolution_iff_hasWeakSolutionWithPathwiseUniqueness
    :
    (∀ (μ₀ : Measure State) [IsProbabilityMeasure μ₀],
        HasUniqueStrongSolution GeneralizedSDEBrownianMotion
          (SolvesStrongGeneralizedSDE σ b) μ₀) ↔
      ∀ (μ₀ : Measure State) [IsProbabilityMeasure μ₀],
        Nonempty (GeneralizedWeakSDESolution μ₀ σ b) ∧
          ∀ L : GeneralizedWeakSDESolution μ₀ σ b, L.IsPathwiseUnique := sorry

/-- Under weak existence and pathwise uniqueness for `μ₀`, every weak solution of the SDE has the
same law on the continuous state-path space. -/
theorem weakSolution_isWeaklyUnique_of_hasWeakSolutionWithPathwiseUniqueness
    {μ₀ : Measure State} [IsProbabilityMeasure μ₀]
    (h :
      Nonempty (GeneralizedWeakSDESolution μ₀ σ b) ∧
        ∀ L : GeneralizedWeakSDESolution μ₀ σ b, L.IsPathwiseUnique)
    (L : GeneralizedWeakSDESolution μ₀ σ b) :
    L.IsWeaklyUnique := sorry

/-- Under weak existence and pathwise uniqueness for `μ₀`, the SDE admits a weak solution that is
unique in law. -/
theorem exists_weaklyUnique_generalizedWeakSDESolution_of_hasWeakSolutionWithPathwiseUniqueness
    {μ₀ : Measure State} [IsProbabilityMeasure μ₀] :
    (
      Nonempty (GeneralizedWeakSDESolution μ₀ σ b) ∧
        ∀ L : GeneralizedWeakSDESolution μ₀ σ b, L.IsPathwiseUnique) →
      ∃ L : GeneralizedWeakSDESolution μ₀ σ b, L.IsWeaklyUnique :=
  fun h ↦
    let ⟨L⟩ := h.1
    ⟨L, weakSolution_isWeaklyUnique_of_hasWeakSolutionWithPathwiseUniqueness h L⟩

end GeneralizedStrongSolutions

end ProbabilityTheory
