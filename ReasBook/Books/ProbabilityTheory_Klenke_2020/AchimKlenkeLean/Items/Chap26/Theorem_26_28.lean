import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap26.Definition_26_23
import ProbabilityTheory_Klenke_2020.Items.Chap26.Definition_26_27
import ProbabilityTheory_Klenke_2020.Items.Chap26.Theorem_26_25
import ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_9

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {n m : ℕ}

local notation "State" => Fin n → ℝ
local notation "PathSpace" => EuclideanPathSpace n
local notation "DiffusionCoeff" => NNReal → State → Fin n → Fin m → ℝ
local notation "DriftCoeff" => NNReal → State → Fin n → ℝ

section

variable
    {E' : Type u} [MeasurableSpace E'] {Ω' : Type v} [MeasurableSpace Ω']
    (σ : DiffusionCoeff) (b : DriftCoeff)
    (Q : E' → ProbabilityMeasure Ω') (Y : E' → NNReal → Ω' → E')
    (H : State → E' → ℂ)

local notation "σσᵀ" => diffusionMatrixOfCoefficient σ

/- Source/core/bridge triage for Theorem 26.28:
- source-facing bridge: the duality criterion below;
- core/canonical owners already upstream: `IsLocalMartingaleProblemSolution`,
  `HasDeterministicTimeMarginalUniqueness`, and `LocalMartingaleProblemWellPosed`;
- bridge/view layer reused here: `pathProcess` and `SatisfiesDualityAt`.
The separating-family owner already packages measurability of the slices `H(·, y)`, so no
additional measurability hypothesis on `H` or bespoke path-process wrapper is primitive here. -/

variable
    (hsep :
      IsSeparatingFamilyFor
        {μ : Measure State | IsProbabilityMeasure μ}
        (Set.range (Function.swap H)))
    (hduality :
      ∀ (x : State)
        {Ω : Type _} [MeasurableSpace Ω]
        (ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω))
        (P : ProbabilityMeasure Ω) (X : Ω → PathSpace),
        IsLocalMartingaleProblemSolution
          (Measure.dirac x) σσᵀ b ℱ (P : Measure Ω) X →
        SatisfiesDualityAt (P : Measure Ω) (pathProcess X) x Q Y H)

-- Proof sketch: for fixed `x`, `T`, and two Dirac-initial solutions `L` and `L'`, apply the
-- duality identity to both solutions. The right-hand side depends only on `x`, `y`, and `T`, so
-- the expectations of `H (·, y)` against the two time-`T` marginals agree for every `y`. Since
-- the family `H(·, y)` is separating on probability measures on `ℝⁿ`, the two marginals coincide.
/-- Duality with a separating class of complex-valued observables implies uniqueness of the
deterministic-time marginals of Dirac-initial solutions of `LMP (σσᵀ, b)`. -/
theorem hasDeterministicTimeMarginalUniqueness_of_duality
    :
    HasDeterministicTimeMarginalUniqueness σσᵀ b := sorry

-- Proof sketch: use `hasDeterministicTimeMarginalUniqueness_of_duality` to obtain uniqueness of
-- all deterministic-time marginals, then invoke
-- `localMartingaleProblemWellPosed_of_diracSolutionExistence_of_marginalUniqueness`.
/-- Theorem 26.28: if every Dirac initial condition admits a solution of `LMP (σσᵀ, b)` and every
such solution is dual to the same family `(Yʸ)` through a complex-valued function `H` whose
slices `H(·, y)` form a separating family on probability measures on `ℝⁿ`, then the local
martingale problem for `(σσᵀ, b)` is well-posed. -/
theorem localMartingaleProblemWellPosed_of_duality
    (hex :
      ∀ x : State,
        ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (ℱ : Filtration NNReal mΩ)
          (P : ProbabilityMeasure Ω) (X : Ω → PathSpace),
          IsLocalMartingaleProblemSolution
            (Measure.dirac x) σσᵀ b ℱ (P : Measure Ω) X) :
    LocalMartingaleProblemWellPosed σσᵀ b :=
  localMartingaleProblemWellPosed_of_diracSolutionExistence_of_marginalUniqueness σσᵀ b hex
    (hasDeterministicTimeMarginalUniqueness_of_duality σ b Q Y H hsep hduality)

end

end ProbabilityTheory
