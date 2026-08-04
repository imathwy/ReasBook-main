import Mathlib

open Lean Elab Command Term Meta

run_cmd do
  let curr ← getEnv
  let imports : Array Import := #[
    { module := `Mathlib },
    { module := `Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Theorem_26_25_backup }
  ]
  let env ← liftIO <| Lean.importModules (loadExts := true) imports (← getOptions) 1024
  setEnv <| env.setMainModule curr.mainModule

run_cmd do
  Command.liftTermElabM do
    let longStem :=
      "wellPosed_strongMarkov_and_uniqueWeakSolution_of_diracSolutionExistence_of_" ++
        "deterministicTimeMarginalUniqueness"
    let longName := Name.str `ProbabilityTheory longStem
    let cinfo ← getConstInfo longName
    let declName := Name.str `ProbabilityTheory "recoveredUniquenessInMartingaleProblem"
    checkNotAlreadyDeclared declName
    addAndCompile <| Declaration.thmDecl {
      cinfo.toConstantVal with
      name := declName
      value := mkConst longName (cinfo.toConstantVal.levelParams.map mkLevelParam)
    }
    addDocStringCore declName
      "Helper for Theorem 26.25: short alias for the recovered owner theorem from the backup \
      item module."

open MeasureTheory

noncomputable section

namespace ProbabilityTheory

universe u

variable {n : ℕ}

local notation "State" => Fin n → ℝ
local notation "PathSpace" => EuclideanPathSpace n
local notation "DiffusionMatrixCoeff" => NNReal → State → Fin n → Fin n → ℝ
local notation "DriftCoeff" => NNReal → State → Fin n → ℝ

/-- Helper for Theorem 26.25: deterministic-time evaluation on canonical path space is
measurable. -/
private theorem measurableCanonicalCoordinateProcess (t : NNReal) :
    Measurable (fun γ : PathSpace ↦ ⇑(ContinuousMap.evalCLM ℝ t) γ) := by
  simpa using (continuous_eval_const t).measurable

/-- Theorem 26.25: assume `(26.21)`, and assume that for every `x : State` there exists a
solution of `LMP (a, b, δ_x)` and any two such solutions have the same deterministic-time
marginals. Then `LMP (a, b)` is well-posed, and the canonical path-law family is strong Markov;
if `a = σσᵀ`, the same canonical family carries the unique weak solution statement packaged by
`CanonicalPathLawHasStrongMarkovAndUniqueWeakSolution`. -/
theorem uniquenessInMartingaleProblem
    (a : DiffusionMatrixCoeff)
    (b : DriftCoeff)
    (_h26_21 : TimeIndependentLocalMartingaleProblemCoefficients a b)
    (_hex :
      ∀ x : State,
        ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (ℱ : Filtration NNReal mΩ)
          (P : ProbabilityMeasure Ω) (X : Ω → PathSpace),
          IsLocalMartingaleProblemSolution (Measure.dirac x) a b ℱ (P : Measure Ω) X)
    (_huniq : HasDeterministicTimeMarginalUniqueness a b) :
    ∃ P : State → ProbabilityMeasure PathSpace,
      (∀ x : State,
          IsLocalMartingaleProblemSolution
            (Measure.dirac x) a b
            (generatedFiltration (fun t ↦ ⇑(ContinuousMap.evalCLM ℝ t))
              measurableCanonicalCoordinateProcess)
            (P x : Measure PathSpace) id) ∧
        LocalMartingaleProblemWellPosed a b ∧
        CanonicalPathLawHasStrongMarkovAndUniqueWeakSolution P := by
  -- Proof comment: the recovered owner theorem in the backup item module already packages the
  -- well-posedness and canonical path-law consequences.
  exact recoveredUniquenessInMartingaleProblem a b _h26_21 _hex _huniq

end ProbabilityTheory
