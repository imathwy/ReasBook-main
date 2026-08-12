import Mathlib
import ProbabilityTheory_Klenke_2020.Chap21.Lemma_21_47
import ProbabilityTheory_Klenke_2020.Chap21.Definition_21_2
import ProbabilityTheory_Klenke_2020.Chap21.Definition_21_4
import ProbabilityTheory_Klenke_2020.Chap26.Example_26_11
import ProbabilityTheory_Klenke_2020.Chap26.Theorem_26_10
import ProbabilityTheory_Klenke_2020.Chap26.Theorem_26_18

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

-- Proof sketch: use the higher centered moment formulas from Lemma 21.47 to obtain increment
-- bounds of order strictly larger than `2`, then apply the one-parameter Kolmogorov continuity
-- criterion to the branching diffusion. The resulting version is almost surely locally Hölder of
-- every exponent below `1 / 2`.
/-- Remark 21.49 (1): if `Y` is a continuous branching diffusion whose one-time marginals satisfy
the branching-diffusion Laplace-transform formula, then for every Hölder exponent
`γ ∈ (0, 1 / 2)` the sample paths are almost surely locally Hölder-continuous of order `γ`. -/
theorem branchingDiffusion_paths_locallyHolderContinuous_subhalf
    {κ : NNReal → Kernel NNReal NNReal}
    (P : NNReal → ProbabilityMeasure Ω) (Y : NNReal → Ω → NNReal)
    (hY : IsMarkovProcessRealization κ P Y)
    (hκ : HasBranchingDiffusionLaplaceTransform κ)
    (hY_cont : ∀ x : NNReal, HasAlmostSurelyContinuousPaths (P x : Measure Ω) Y)
    (γ : Set.Ioo (0 : ℝ≥0) (1 / 2)) :
    ∀ x : NNReal, ∀ᵐ ω ∂(P x : Measure Ω), LocallyHolderWith (γ : ℝ≥0) (processPath Y ω) := sorry

/-- Remark 21.49 (2): for every deterministic initial state `x ≥ 0`, the Feller branching SDE
`dY_t = √(2 Y_t) dW_t`, viewed through the canonical CIR/Feller coefficient pair
`cirDiffusionCoeff 2` and `cirDriftCoeff 0 0`, has a unique strong solution. -/
theorem fellerBranchingSDE_hasUniqueStrongSolution (x : NNReal) :
    HasUniqueStrongSolution
      GeneralizedSDEBrownianMotion
      (SolvesStrongGeneralizedSDE
        (oneDimensionalDiffusion (cirDiffusionCoeff 2))
        (oneDimensionalDrift (cirDriftCoeff 0 0)))
      (Measure.dirac (oneDimensionalState (x : ℝ))) := sorry

end ProbabilityTheory
