import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap09.Definition_9_10
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap17.Definition_17_3
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap17.Definition_17_12
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap26.Definition_26_23
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap26.Theorem_26_18
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap26.Theorem_26_21

open MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

universe u v

namespace ProbabilityTheory

variable {n m : ℕ}

local notation "State" => Fin n → ℝ
local notation "PathSpace" => EuclideanPathSpace n
local notation "DiffusionCoeff" => NNReal → State → Fin n → Fin m → ℝ
local notation "DiffusionMatrixCoeff" => NNReal → State → Fin n → Fin n → ℝ
local notation "DriftCoeff" => NNReal → State → Fin n → ℝ

private theorem measurable_path_eval (t : NNReal) :
    Measurable (ContinuousMap.evalCLM ℝ t : PathSpace → State) := by
  simpa using (continuous_eval_const t).measurable

/-- Deterministic-time marginal uniqueness for the Dirac-initial local martingale problem means
that any two solutions started from the same point have the same law at every deterministic time
`T ≥ 0`. -/
def HasDeterministicTimeMarginalUniqueness
    (a : DiffusionMatrixCoeff) (b : DriftCoeff) : Prop :=
  ∀ (x : State)
      {Ω : Type u} [MeasurableSpace Ω]
      (ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω))
      (μ : Measure Ω) (X : Ω → PathSpace)
      {Ω' : Type v} [MeasurableSpace Ω']
      (ℱ' : Filtration NNReal (inferInstance : MeasurableSpace Ω'))
      (μ' : Measure Ω') (Y : Ω' → PathSpace),
      IsLocalMartingaleProblemSolution (Measure.dirac x) a b ℱ μ X →
      IsLocalMartingaleProblemSolution (Measure.dirac x) a b ℱ' μ' Y →
      ∀ T : NNReal,
        μ.map (fun ω ↦ X ω T) = μ'.map (fun ω ↦ Y ω T)

-- Proof sketch: deterministic-time marginal uniqueness upgrades to uniqueness in law on path
-- space by the standard martingale-problem uniqueness theorem; combined with the assumed
-- existence of Dirac-initial solutions, this is exactly the well-posedness condition.
/-- Theorem 26.25 (1): if every Dirac initial condition admits a solution of `LMP(a,b)` and any
two such solutions have the same law at every deterministic time, then the local martingale
problem `LMP(a,b)` is well-posed. -/
theorem localMartingaleProblemWellPosed_of_diracSolutionExistence_of_marginalUniqueness
    (a : DiffusionMatrixCoeff) (b : DriftCoeff)
    (hex :
      ∀ x : State,
        ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (ℱ : Filtration NNReal mΩ)
          (P : ProbabilityMeasure Ω) (X : Ω → PathSpace),
          IsLocalMartingaleProblemSolution (Measure.dirac x) a b ℱ (P : Measure Ω) X)
    (huniq : HasDeterministicTimeMarginalUniqueness a b) :
    LocalMartingaleProblemWellPosed a b := sorry

section CanonicalPathLaws

variable (a : DiffusionMatrixCoeff) (b : DriftCoeff)
variable (P : State → ProbabilityMeasure PathSpace)

variable
    (hP :
      ∀ x : State,
        IsLocalMartingaleProblemSolution (Measure.dirac x) a b
          (generatedFiltration
            (fun t ↦ (ContinuousMap.evalCLM ℝ t : PathSpace → State))
            measurable_path_eval)
          (P x : Measure PathSpace) id)

-- Proof sketch: well-posedness supplies uniqueness in law for the canonical path measures, and
-- the canonical-path-space hypothesis identifies `P x` with the law of a Dirac-initial
-- martingale-problem solution. The standard Stroock--Varadhan theorem then yields a compatible
-- time-homogeneous Markov path kernel for the canonical coordinate process and upgrades the
-- natural Markov property to the Chapter 17 strong Markov owner.
/-- Theorem 26.25 (2): if `LMP(a,b)` is well-posed and `P x` is the canonical path law of the
Dirac-initial solution started from `x`, then the canonical process on path space is a strong
Markov process with respect to the family `(P x)`. -/
theorem canonicalPathProcess_hasStrongMarkovProperty_of_localMartingaleProblemWellPosed
    (hwell : LocalMartingaleProblemWellPosed a b) :
    ∃ κ : Kernel State (NNReal → State),
      IsTimeHomogeneousMarkovProcess
        (fun t ↦ (ContinuousMap.evalCLM ℝ t : PathSpace → State)) P κ ∧
      HasStrongMarkovProperty
        P (fun t ↦ (ContinuousMap.evalCLM ℝ t : PathSpace → State)) κ := sorry

-- Proof sketch: apply
-- `solvesLocalMartingaleProblem_iff_exists_generalizedWeakSDESolution_extension` to the canonical
-- path-space
-- solution `(P x, id)` furnished by `hP`, using `ha` to identify `a` with `σσᵀ`. This produces a
-- weak solution whose state-path law is exactly `P x`, and `hwell` upgrades it to weak
-- uniqueness via `exists_weakSDESolution_of_localMartingaleProblemUniquelySolvable`.
/-- Theorem 26.25 (3): if `a = σσᵀ`, then for each start point `x` the canonical path law `P x`
is the state-path law of a weak solution of the SDE with diffusion coefficient `σ` and drift `b`,
and that weak solution is unique in law. -/
theorem exists_weakSDESolution_with_statePathLaw_of_localMartingaleProblemWellPosed
    (hwell : LocalMartingaleProblemWellPosed a b)
    (σ : DiffusionCoeff) (ha : a = diffusionMatrixOfCoefficient σ) :
    ∀ x : State,
      ∃ L : GeneralizedWeakSDESolution.{u} (Measure.dirac x) σ b,
        L.IsWeaklyUnique ∧ L.statePathLaw = (P x : Measure PathSpace) := sorry

end CanonicalPathLaws

end ProbabilityTheory
