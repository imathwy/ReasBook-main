import Mathlib
import ProbabilityTheory_Klenke_2020.Chap14.Definition_14_40
import ProbabilityTheory_Klenke_2020.Chap17.Theorem_17_8

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {κ : NNReal → Kernel NNReal NNReal}

/-- The kernel family `κ` has the branching-diffusion Laplace transform
`E_x[e^{-λ Y_t}] = exp (- λ x / (1 + λ t))` for all nonnegative times and Laplace parameters. -/
def HasBranchingDiffusionLaplaceTransform (κ : NNReal → Kernel NNReal NNReal) : Prop :=
  ∀ x t lam : NNReal,
    ∫ y, Real.exp (-((lam : ℝ) * (y : ℝ))) ∂ κ t x =
      Real.exp (-((lam : ℝ) * (x : ℝ)) / (((lam : ℝ) * (t : ℝ)) + 1))

-- Proof sketch: first evaluate the Laplace identity at `λ = 0` to identify each `κ t x` as a
-- probability measure, then use uniqueness of Laplace transforms on `ℝ≥0` together with the
-- explicit formula to deduce the Chapman--Kolmogorov composition law `κ t ∘ₖ κ s = κ (s + t)`.
/-- Lemma 21.46 (1): a kernel family on `ℝ≥0` with Laplace transform
`E_x[e^{-λ Y_t}] = exp (- λ x / (1 + λ t))` is a Markov semigroup. -/
theorem branchingDiffusionKernel_isMarkovSemigroup
    (hκ : HasBranchingDiffusionLaplaceTransform κ) : IsMarkovSemigroup κ := sorry

-- Proof sketch: apply the standard realization theorem for Markov semigroups on the standard
-- Borel state space `ℝ≥0` to the semigroup supplied by
-- `branchingDiffusionKernel_isMarkovSemigroup`.
/-- Lemma 21.46 (2): the branching-diffusion kernel family admits a time-homogeneous Markov
process realization whose one-time marginals are exactly the kernel rows `κ t x`. -/
theorem exists_markovProcessRealization_of_branchingDiffusionKernel
    (hκ : HasBranchingDiffusionLaplaceTransform κ) :
    ∃ (Ω : Type u), ∃ _ : MeasurableSpace Ω, ∃ Y : NNReal → Ω → NNReal,
      ∃ P : NNReal → ProbabilityMeasure Ω, IsMarkovProcessRealization κ P Y := by
  haveI : IsMarkovSemigroup κ := branchingDiffusionKernel_isMarkovSemigroup hκ
  simpa using exists_markovProcessRealization_of_markovSemigroup κ

end ProbabilityTheory
