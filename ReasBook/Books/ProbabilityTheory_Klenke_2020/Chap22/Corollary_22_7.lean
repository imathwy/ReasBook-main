import Mathlib
import ProbabilityTheory_Klenke_2020.Chap02.Definition_2_14
import ProbabilityTheory_Klenke_2020.Chap05.Theorem_5_28
import ProbabilityTheory_Klenke_2020.Chap21.Definition_21_8

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

section

variable (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
variable (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
variable (hX_mean : P[X 1] = 0)
variable (hX_memLp : MemLp (X 1) 2 P)

-- Proof sketch: apply the one-step Skorohod embedding from Theorem 22.5 independently to the iid
-- increments `X₁, X₂, …`, then concatenate the resulting Brownian pieces using the strong Markov
-- property. The accumulated stopping times are increasing, their increments stay iid, the mean of
-- `τ₁` is the variance of `X₁`, and the stopped Brownian path `(B_{τₙ})ₙ` has the law of the
-- textbook partial sums.
/-- Corollary 22.7: if `X₁, X₂, …` are i.i.d. real random variables with mean `0` and finite
variance, then on a suitable probability space there exist a filtration `ℱ`, a Brownian motion
`B`, and increasing `ℱ`-stopping times `τₙ` such that `(τₙ₊₁ - τₙ)ₙ` is i.i.d.,
`E[τ₁] = Var[X₁]`, and `(B_{τₙ})ₙ` has the law of the textbook partial-sum process `Sₙ`. -/
theorem exists_centered_iid_skorohod_embedding :
    ∃ (space : Type v) (_mSpace : MeasurableSpace space) (ℱ : Filtration NNReal _mSpace)
      (law : ProbabilityMeasure space) (brownian : NNReal → space → ℝ)
      (hBrownian : IsBrownianMotion (law : Measure space) brownian)
      (stoppingTime : ℕ → space → NNReal),
        stoppingTime 0 = 0 ∧
        (∀ n, IsStoppingTime ℱ (fun ω ↦ (stoppingTime n ω : ENNReal))) ∧
        Monotone stoppingTime ∧
        IdentDistrib
          (fun ω n ↦ brownian (stoppingTime n ω) ω)
          (fun ω n ↦ partialSum (fun k ↦ X (k + 1)) n ω)
          (law : Measure space) P ∧
        IsIID (fun n ω ↦ stoppingTime (n + 1) ω - stoppingTime n ω) (law : Measure space) ∧
        (law : Measure space)[fun ω ↦ (stoppingTime 1 ω : ℝ)] = Var[X 1; P] := sorry

-- Proof sketch: apply Corollary 22.7 and then sharpen the filtration to the natural filtration of
-- the Brownian motion, keeping the conclusion directly on the stopped Brownian path rather than
-- introducing an auxiliary copied process as extra existential data. The iid increment condition
-- remains an additional conclusion.
/-- A natural-filtration restatement of Corollary 22.7 keeps the conclusion directly on the stopped
Brownian path `(B_{τₙ})ₙ`; the iid increment condition for the embedding times remains an extra
conclusion. -/
theorem exists_centered_iid_brownian_stopping_embedding :
    ∃ (space : Type v) (_mSpace : MeasurableSpace space) (law : ProbabilityMeasure space)
      (brownian : NNReal → space → ℝ) (hBrownian : IsBrownianMotion (law : Measure space) brownian)
      (stoppingTime : ℕ → space → NNReal),
        stoppingTime 0 = 0 ∧
        (∀ n,
          IsStoppingTime (Filtration.natural brownian hBrownian.stronglyMeasurable)
            (fun ω ↦ (stoppingTime n ω : ENNReal))) ∧
        Monotone stoppingTime ∧
        IdentDistrib
          (fun ω n ↦ brownian (stoppingTime n ω) ω)
          (fun ω n ↦ partialSum (fun k ↦ X (k + 1)) n ω)
          (law : Measure space) P ∧
        (∀ n,
          (law : Measure space)[fun ω ↦ (stoppingTime n ω : ℝ)] =
            (law : Measure space)[fun ω ↦ (brownian (stoppingTime n ω) ω) ^ 2]) ∧
        IsIID (fun n ω ↦ stoppingTime (n + 1) ω - stoppingTime n ω) (law : Measure space) := sorry

end

end ProbabilityTheory
