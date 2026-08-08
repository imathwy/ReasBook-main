import Mathlib
import ProbabilityTheory_Klenke_2020.Chap14.Lemma_14_27
import ProbabilityTheory_Klenke_2020.Chap14.Theorem_14_47
import ProbabilityTheory_Klenke_2020.Chap17.Definition_17_3

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

/-- Example 17.6 (1): if `ν` is a convolution semigroup on `ℝ^d`, then the canonical coordinate
process on the path space `(ℝ^d)^[0,∞)` admits path laws `x ↦ P_x` making it a
time-homogeneous Markov process whose time-`t` transition kernel is
`x ↦ δ_x ∗ ν_t`. -/
theorem exists_timeHomogeneousMarkovProcess_of_isConvolutionSemigroup {d : ℕ}
    (ν : NNReal → ProbabilityMeasure (Fin d → ℝ)) (hν : IsConvolutionSemigroupWithZero ν) :
    ∃ P : (Fin d → ℝ) → ProbabilityMeasure (NNReal → Fin d → ℝ),
      ∃ κ : Kernel (Fin d → ℝ) (NNReal → Fin d → ℝ),
        IsTimeHomogeneousMarkovProcess Function.eval P κ ∧
          ∀ t : NNReal,
            transitionKernel κ t =
              dirac_convolution_kernel (ν t : Measure (Fin d → ℝ)) := sorry

-- Proof sketch: apply Example 17.6 (1) and then pass from the source-facing path-kernel
-- formulation of Definition 17.3 to the owner abstraction `IsMarkovProcessRealization` via
-- `IsTimeHomogeneousMarkovProcess.toIsMarkovProcessRealization`.
/-- The canonical coordinate process on the path space realizes the translated convolution kernels
`x ↦ δ_x ∗ ν_t` as a continuous-time Markov process. -/
theorem exists_markovProcessRealization_of_isConvolutionSemigroup {d : ℕ}
    (ν : NNReal → ProbabilityMeasure (Fin d → ℝ)) (hν : IsConvolutionSemigroupWithZero ν) :
    ∃ P : (Fin d → ℝ) → ProbabilityMeasure (NNReal → Fin d → ℝ),
      IsMarkovProcessRealization
        (fun t ↦ dirac_convolution_kernel (ν t : Measure (Fin d → ℝ)))
        P Function.eval := by
  sorry

-- Proof sketch: Example 17.6 yields a canonical-process realization of the translated kernels, and
-- Theorem 17.8 identifies the owner abstraction `IsMarkovProcessRealization` with the ambient
-- semigroup structure on those transition kernels.
/-- Example 17.6 (2): the translated increment kernels `x ↦ δ_x ∗ ν_t` form a
time-homogeneous Markov semigroup. -/
instance translatedIncrementKernel_isMarkovSemigroup {d : ℕ}
    (ν : NNReal → ProbabilityMeasure (Fin d → ℝ)) (hν : IsConvolutionSemigroupWithZero ν) :
    IsMarkovSemigroup
      (fun t ↦ dirac_convolution_kernel (ν t : Measure (Fin d → ℝ))) := by
  rcases exists_timeHomogeneousMarkovProcess_of_isConvolutionSemigroup ν hν with
    ⟨P, κ, hMarkov, hκ⟩
  letI :
      IsTimeHomogeneousMarkovProcess Function.eval P κ :=
    hMarkov
  have hSemigroup : IsMarkovSemigroup (transitionKernel κ) :=
    IsTimeHomogeneousMarkovProcess.transitionKernel_isMarkovSemigroup Function.eval
  have hκ' :
      transitionKernel κ =
        fun t ↦ dirac_convolution_kernel (ν t : Measure (Fin d → ℝ)) :=
    funext hκ
  simpa [hκ'] using hSemigroup
