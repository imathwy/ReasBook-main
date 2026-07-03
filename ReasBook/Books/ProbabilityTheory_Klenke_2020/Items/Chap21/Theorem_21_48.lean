import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap21.Lemma_21_47
import ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_6
import ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_4

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

noncomputable section

universe u

namespace ProbabilityTheory

-- Proof sketch: first use
-- `exists_markovProcessRealization_of_branchingDiffusionKernel` to realize the kernel family by a
-- Markov process `(P, Y)`. Then identify the one-time marginals through
-- `IsMarkovProcessRealization.hasBranchingDiffusionMarginalLaplaceTransform`, derive the required
-- fourth-moment increment bounds from Lemma 21.47, and apply
-- `exists_modification_with_locally_holder_paths` under each initial law `P x`. Finally, forget
-- the stronger local Hölder conclusion and retain only almost sure continuity.
/-- Theorem 21.48: if `κ` is the branching-diffusion transition semigroup from `(21.44)`, then
there exist a Markov-process realization `Y` of `κ` and a process `Yc` on the same measurable
space such that, for every initial state `x`, `Yc` is a version of `Y` under `P x` with almost
surely continuous sample paths. This continuous version is Feller's branching diffusion. -/
theorem exists_continuous_branchingDiffusion_version
    {κ : NNReal → Kernel NNReal NNReal} (hκ : HasBranchingDiffusionLaplaceTransform κ) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (Y : NNReal → Ω → NNReal)
      (P : NNReal → ProbabilityMeasure Ω) (Yc : NNReal → Ω → NNReal),
        IsMarkovProcessRealization κ P Y ∧
          ∀ x : NNReal,
            AreModifications (P x : Measure Ω) Y Yc ∧
              HasAlmostSurelyContinuousPaths (P x : Measure Ω) Yc := sorry

end ProbabilityTheory
